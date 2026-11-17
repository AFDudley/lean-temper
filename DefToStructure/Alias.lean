/-
  The alias transform (`--alias WORKLIST.json`, see ../README.md, "Alias
  mode"). One work-list entry names a declaration `D`, a binder `v` and the
  right-hand side of an equation binder `hv : v = rhs` (or `rhs = v`). The
  transform deletes the two binders from `D`, puts `rhs` for `v` in the
  statement, keeps the proof correct, and deletes the two arguments at every
  call site of `D`.

  Every fact comes from the info tree of an in-process elaboration of the
  original file (`elabFile`): the free variables of `v` and `hv` (the binder
  nodes at the binder positions), the occurrences of `v` in the signature
  and in the proof (term nodes whose expression is that free variable), and
  the call sites (term nodes of `app` syntax whose expression is an
  application of `D`). At a call site, the argument for `v` (or `hv`) is the
  syntactic argument whose own term node elaborated to the same expression
  as the application's argument at `v`'s index. That covers implicit
  arguments (no syntax, nothing to delete), named arguments `(v := e)`, `@D`
  and dot notation `h.D a` (the receiver is no syntactic argument).

  The proof keeps its text. When it names `v` or `hv` (or a first attempt
  without a preamble fails), the proof starts with
  `generalize hv : rhs = v at h₁ … ⊢` (and `replace hv := hv.symm` for
  `v = rhs`): the context and the goal are then the original ones again.
-/
import Lean
import DefToStructure.Patterns

open Lean Elab Meta

namespace DefToStructure.Alias

/-- One work-list entry (`scripts/type_lint.lean` output plus `at`). -/
structure Finding where
  declaration : String
  binder : String
  rhs : String
  at_ : String
  deriving Inhabited, BEq

def Finding.ofJson (j : Json) : Except String Finding := do
  return { declaration := ← j.getObjValAs? String "declaration", binder := ← j.getObjValAs? String "binder",
           rhs := ← j.getObjValAs? String "rhs", at_ := ← j.getObjValAs? String "at" }

def Finding.file (f : Finding) : String := (f.at_.splitOn ":")[0]!

/-- A term node of the info tree with an original source range. -/
structure Node where
  start : Nat
  stop : Nat
  ti : TermInfo
  ctx : ContextInfo

def Node.instExpr (n : Node) : IO Expr :=
  n.ti.runMetaM n.ctx do return (← instantiateMVars n.ti.expr).consumeMData

/-- An elaborated file: the commands, the term nodes, the final environment. -/
structure FileElab where
  text : String
  fileMap : FileMap
  env : Environment
  commands : Array Syntax
  nodes : Array Node
  errors : Array String

def rng? (stx : Syntax) : Option (Nat × Nat) := do
  let a ← stx.getPos? (canonicalOnly := true)
  let b ← stx.getTailPos? (canonicalOnly := true)
  pure (a.byteIdx, b.byteIdx)

unsafe def enableInitializersUnsafe : IO Unit := enableInitializersExecution

/-- `importModules (loadExts := true)` consumes the permission that
    `enableInitializersExecution` gives: each import needs it again. -/
@[implemented_by enableInitializersUnsafe] opaque enableInitializers : IO Unit

/-- Elaborate `text` as module `mainModule` with its own imports (the search
    path must be set), synchronously, and keep every term node with an
    original range. -/
def elabText (fileName : String) (mainModule : Name) (text : String) : IO FileElab := do
  let inputCtx := Parser.mkInputContext text fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let opts := Elab.async.set ({} : Options) false
  enableInitializers
  let (env, messages) ← processHeader header opts messages inputCtx (trustLevel := 1024) (mainModule := mainModule)
  for m in messages.toList do
    if m.severity == .error then throw (IO.userError s!"{fileName}: the header does not import: {← m.data.toString}")
  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages opts)
  let mut nodes : Array Node := #[]
  for t in s.commandState.infoState.trees do
    nodes := t.foldInfo (init := nodes) fun ctx info acc =>
      match info with
      | .ofTermInfo ti =>
        match rng? ti.stx with
        | some (a, b) => acc.push { start := a, stop := b, ti, ctx }
        | none => acc
      | _ => acc
  let mut errors := #[]
  for m in s.commandState.messages.toList do
    if m.severity == .error then
      errors := errors.push s!"{m.pos.line}:{m.pos.column}: {← m.data.toString}"
  return { text, fileMap := inputCtx.fileMap, env := s.commandState.env, commands := s.commands, nodes, errors }

def slice (text : String) (s e : Nat) : String := String.Pos.Raw.extract text ⟨s⟩ ⟨e⟩

/-- `pre ++ t ++ post`, where `t` started at column `col` and `pre` opens a
    tactic block (`(by …`). The lines of `t` after its first move right by
    one amount: they keep their layout, they move as far as the first line
    moved (`pre`'s length), and they stay right of the block's column
    `col + 4`. -/
def underBy (col : Nat) (pre t post : String) : String :=
  let lines := t.splitOn "\n"
  match lines with
  | [] | [_] => pre ++ t ++ post
  | first :: rest =>
    let blank (l : String) : Bool := l.trimAscii.isEmpty
    let indent (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length
    let contMin := rest.foldl (fun m l => if blank l then m else min m (indent l)) col
    let shift := max pre.length (col + 5 - contMin)
    let pad := String.ofList (List.replicate shift ' ')
    pre ++ "\n".intercalate (first :: rest.map fun l => if blank l then l else pad ++ l) ++ post

-- --- deletions ---------------------------------------------------------------

def isSp (b : UInt8) : Bool := b == 32 || b == 9
def isWs (b : UInt8) : Bool := isSp b || b == 10 || b == 13

/-- The edit that deletes `[s, e)`: a line left empty goes whole; a line
    left with ` :` only (the end of a signature) joins the line before; an
    item at a line start keeps the indentation; otherwise the space before
    (or, with none, after) the item goes with it. -/
def deletion (text : String) (s e : Nat) : Edit := Id.run do
  let b := text.toUTF8
  let n := b.size
  let mut l := s
  while l > 0 && isSp b[l - 1]! do l := l - 1
  let mut r := e
  while r < n && isSp b[r]! do r := r + 1
  let atStart := l == 0 || b[l - 1]! == 10
  let atEnd := r == n || b[r]! == 10
  if atStart && atEnd then return { start := l, stop := min (r + 1) n, replacement := "" }
  if atStart && l > 0 && r + 1 < n && b[r]! == 58 && b[r + 1]! == 10 then
    let mut p := l - 1
    while p > 0 && b[p - 1]! != 10 do p := p - 1
    unless ((slice text p (l - 1)).splitOn "--").length > 1 do
      return { start := l - 1, stop := r, replacement := " " }
  if atStart || l == s then return { start := s, stop := r, replacement := "" }
  return { start := l, stop := e, replacement := "" }

/-- Deletion edits for raw ranges: ranges separated by white space only merge. -/
def deletions (text : String) (ranges : Array (Nat × Nat)) : Array Edit := Id.run do
  let b := text.toUTF8
  let sorted := ranges.qsort (·.1 < ·.1)
  let mut merged : Array (Nat × Nat) := #[]
  for (s, e) in sorted do
    match merged.back? with
    | some (ps, pe) =>
      let gapWs := Id.run do
        let mut ok := true
        for i in [pe:s] do
          if !isWs b[i]! then ok := false
        return ok
      if s ≤ pe || gapWs then
        merged := merged.pop.push (ps, max pe e)
      else merged := merged.push (s, e)
    | none => merged := merged.push (s, e)
  return merged.map fun (s, e) => deletion text s e

-- --- the declaration -----------------------------------------------------------

/-- One binder group of a signature. -/
structure Group where
  stx : Syntax
  idents : Array Syntax
  type? : Option Syntax
  deriving Inhabited

def groupOf (b : Syntax) : Group :=
  if b.isOfKind ``Parser.Term.instBinder then { stx := b, idents := #[], type? := some b[2] }
  else
    let idents := b[1].getArgs.map fun i => if i.isIdent then i else i[0]
    let bt := b[2]
    { stx := b, idents, type? := if bt.getNumArgs == 2 then some bt[1] else none }

def identName (i : Syntax) : String := i.getId.eraseMacroScopes.toString (escape := false)

/-- The parts of a declaration command: binder groups, the type, the value. -/
structure DeclParts where
  cmd : Syntax
  groups : Array Group
  type : Syntax
  value : Syntax

/-- `omit … in theorem …`: the declaration inside the `in` commands. -/
partial def unwrapIn (cmd : Syntax) : Syntax :=
  if cmd.isOfKind ``Parser.Command.in then unwrapIn cmd[2] else cmd

def declParts? (cmd : Syntax) : Option DeclParts := do
  let cmd := unwrapIn cmd
  guard (cmd.isOfKind ``Parser.Command.declaration)
  let d := cmd[1]
  guard (d.isOfKind ``Parser.Command.theorem || d.isOfKind ``Parser.Command.definition)
  let sig := d[2]
  let type ← if sig.isOfKind ``Parser.Command.declSig then some sig[1][1]
    else if sig[1].getNumArgs == 0 then none else some sig[1][0][1]
  pure { cmd, groups := sig[0].getArgs.map groupOf, type, value := d[3] }

/-- One alias pair of a declaration, as the info tree gives it. -/
structure Pair where
  finding : Finding
  v : String
  /-- `hv`'s name; empty for a premise `v = rhs →` of the statement. -/
  hv : String
  /-- `true` for `hv : v = rhs`, `false` for `hv : rhs = v`. -/
  vLeft : Bool
  rhsText : String
  /-- The variables that `rhs` names: their ranges in `rhsText` and their names. -/
  holes : Array (Nat × Nat × String) := #[]
  /-- The variables that `rhs` names: their free variables. -/
  holeIds : Array FVarId := #[]
  vIds : Array FVarId
  hvIds : Array FVarId
  vIdent : Syntax
  /-- `v`'s binder group in the declaration; none for a `∀` binder of the statement. -/
  vGroup : Option Group
  /-- `hv`'s binder group in the declaration; none for a premise of the statement. -/
  hvGroup : Option Group
  /-- The ranges that go in the statement: `v`'s `∀` binder, `hv`'s premise. -/
  stmtDel : Array (Nat × Nat)

/-- `v` or `hv` is part of the statement, not a binder of the declaration. -/
def Pair.inStatement (p : Pair) : Bool := p.vGroup.isNone || p.hvGroup.isNone

/-- The edits of one declaration. `sig`: the binder deletions and the
    substitutions in the signature. The proof has three forms: `proof`, the
    occurrences of `v` and `hv` in the proof replaced (`v` by `rhs`, a
    rewrite or `subst` with `hv` deleted, another `hv` by `rfl`);
    `restated`, the proof text kept behind
    `suffices h : ∀ (v : T) (hv : v = rhs) (h₁ : T₁ v) …, OLD from h _ rfl h₁ …; intro v hv h₁ …`
    (the context and the goal of the old proof exactly); and `preamble`,
    the proof text kept behind `generalize`. -/
structure DeclEdits where
  sig : Array Edit
  proof : Except String (Array Edit)
  restated : Option Edit
  preamble : Option Edit
  /-- The proof names `v` or `hv`. -/
  proofNames : Bool
  pairs : Array Pair
  /-- The end of the declaration's name: the fresh name of a check goes there. -/
  declIdEnd : Nat
  /-- The range of `:= proof`, and whether the command is a `theorem`. -/
  valueRange : Nat × Nat
  isTheorem : Bool
  /-- The binders that moved before `v`'s place (`rhs` names them), in order. -/
  moved : Array String := #[]

def atomic (rhs : Syntax) : Bool :=
  rhs.isIdent || rhs.isOfKind ``Parser.Term.paren || rhs.isOfKind ``Parser.Term.num ||
    rhs.isOfKind ``Parser.Term.proj

def nodesIn (fe : FileElab) (s e : Nat) : Array Node := fe.nodes.filter fun n => s ≤ n.start && n.stop ≤ e

def fvarsAt (ns : Array Node) (r : Nat × Nat) (binder : Bool) : Array FVarId :=
  ns.foldl (init := #[]) fun acc n =>
    if n.start == r.1 && n.stop == r.2 && n.ti.isBinder == binder then
      match n.ti.expr.consumeMData with
      | .fvar id => if acc.contains id then acc else acc.push id
      | _ => acc
    else acc

/-- The declaration command of `D` in an elaborated file: the command that
    holds the binder node whose expression is the constant `D`. -/
def declCommand? (fe : FileElab) (d : Name) : Option Syntax := do
  let n ← fe.nodes.find? fun n => n.ti.isBinder && n.ti.expr.constName? == some d
  fe.commands.find? fun c => match rng? c with
    | some (s, e) => s ≤ n.start && n.stop ≤ e
    | none => false

partial def descendants (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  stx.getArgs.foldl (init := acc.push stx) fun acc c => descendants c acc

/-- Find the pair for binder `v`, from the info tree: `v` is a binder of
    the declaration or of a `∀` in the statement; `hv` is a later binder of
    the declaration or a premise `v = rhs →` of the statement. -/
def findPair (fe : FileElab) (ns : Array Node) (parts : DeclParts) (f : Finding) : Except String Pair := do
  let declHit := parts.groups.zipIdx.findSome? fun (g, gi) =>
    (g.idents.find? fun i => identName i == f.binder).map (gi, ·)
  let typeNodes := descendants parts.type
  -- `v`: its identifier, its group, and the statement range that goes
  let (vIdent, vGi?, vStmtDel) ← match declHit with
    | some (gi, i) => pure (i, some gi, #[])
    | none =>
      let hit := typeNodes.findSome? fun fa => do
        guard (fa.isOfKind ``Parser.Term.forall)
        let bs := fa[1].getArgs
        bs.findSome? fun b =>
          let g : Group := if b.isIdent then { stx := b, idents := #[b], type? := none } else groupOf b
          (g.idents.find? (identName · == f.binder)).bind fun i => do
            if bs.size == 1 && g.idents.size == 1 then
              let (s, _) ← rng? fa
              let (_, e) ← rng? fa[3]
              pure (i, (s, e))
            else if g.idents.size == 1 then pure (i, ← rng? g.stx)
            else pure (i, ← rng? i)
      match hit with
      | some (i, r) => pure (i, none, #[r])
      | none => throw s!"no binder `{f.binder}` in the declaration or its statement"
  let some vr := rng? vIdent | throw "the binder has no source range"
  let vIds := fvarsAt ns vr true
  if vIds.isEmpty then throw s!"no binder node for `{f.binder}`"
  let isV (stx : Syntax) : Bool := match rng? stx with
    | some r => stx.isIdent && (fvarsAt ns r false).any vIds.contains
    | none => false
  let sides (t : Syntax) : Option (Bool × Syntax) :=
    if !t.isOfKind ``«term_=_» then none
    else if isV t[0] then some (true, t[2]) else if isV t[2] then some (false, t[0]) else none
  -- `rhs`'s text (in parentheses unless atomic) and the variables in it
  let rhsOf (side : Syntax) : Except String (String × Array (Nat × Nat × String) × Array FVarId) := do
    let some (ss, se) := rng? side | throw "no range"
    let paren := !atomic side
    let off := if paren then 1 else 0
    let mut holes : Array (Nat × Nat × String) := #[]
    let mut ids : Array FVarId := #[]
    for n in ns do
      unless ss ≤ n.start && n.stop ≤ se && !n.ti.isBinder do continue
      let .fvar id := n.ti.expr.consumeMData | continue
      if holes.any (fun (a, _, _) => a == n.start - ss + off) then continue
      let some ld := n.ti.lctx.find? id | continue
      holes := holes.push (n.start - ss + off, n.stop - ss + off, ld.userName.eraseMacroScopes.toString (escape := false))
      unless ids.contains id do ids := ids.push id
    let text := slice fe.text ss se
    return (if paren then s!"({text})" else text, holes.qsort (·.1 < ·.1), ids)
  let base : Pair := { finding := f, v := f.binder, hv := "", vLeft := true, rhsText := "", vIds, hvIds := #[],
                       vIdent, vGroup := vGi?.map (parts.groups[·]!), hvGroup := none, stmtDel := vStmtDel }
  -- `hv`: a later binder of the declaration
  if let some gi := vGi? then
    for g in parts.groups.extract (gi + 1) parts.groups.size do
      let some t := g.type? | continue
      unless g.idents.size == 1 do continue
      let some (vLeft, side) := sides t | continue
      let some hr := rng? g.idents[0]! | continue
      let (rhsText, holes, holeIds) ← rhsOf side
      return { base with hv := identName g.idents[0]!, vLeft, rhsText, holes, holeIds,
                         hvIds := fvarsAt ns hr true, hvGroup := some g }
  -- `hv`: a premise of the statement
  for a in typeNodes do
    unless a.isOfKind ``Parser.Term.arrow do continue
    let some (vLeft, side) := sides a[0] | continue
    let some (s, _) := rng? a[0] | continue
    let some (_, e) := rng? a[1] | continue
    let (rhsText, holes, holeIds) ← rhsOf side
    return { base with vLeft, rhsText, holes, holeIds, stmtDel := vStmtDel.push (s, e) }
  throw s!"no equation `{f.binder} = …` among the binders and premises"

/-- The proof's first tactic, or the term, and whether it is a tactic block. -/
def proofStart? (value : Syntax) : Option (Syntax × Bool) := do
  guard (value.isOfKind ``Parser.Command.declValSimple)
  let t := value[1]
  if t.isOfKind ``Parser.Term.byTactic then
    let seq := t[1]
    let inner := seq[0]
    let first := inner[0].getArgs[0]?
    first.map (·, true)
  else pure (t, false)

-- --- the proof ---------------------------------------------------------------------

/-- The nodes from `stx` down to the innermost node that covers `[s, e)`. -/
partial def pathTo (stx : Syntax) (s e : Nat) (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := acc.push stx
  match stx.getArgs.find? fun c => match rng? c with
    | some (a, b) => a ≤ s && e ≤ b
    | none => false with
  | some c => pathTo c s e acc
  | none => acc

partial def stripParens (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Parser.Term.paren then stripParens stx[1] else stx

/-- `stx` is `name` or `name.symm`, in parentheses or not. -/
def isRef (stx : Syntax) (name : String) : Bool :=
  let s := stripParens stx
  s.isIdent && (identName s == name || identName s == name ++ ".symm")

def isAtom (stx : Syntax) (a : String) : Bool := match stx with
  | .atom _ v => v == a
  | _ => false

/-- The deletion of the tactic at `path[k]`, an element of a tactic sequence
    (`path[k-1]` the element list), with its `;`. A lone tactic becomes `skip`. -/
def tacticDeletion (text : String) (path : Array Syntax) (k : Nat) : Option Edit := do
  let elem := path[k]!
  let items := path[k - 1]!.getArgs
  let (es, ee) ← rng? elem
  let j ← items.findIdx? fun i => rng? i == some (es, ee)
  if items.size == 1 then return { start := es, stop := ee, replacement := "skip" }
  if h : j + 1 < items.size then
    if isAtom items[j + 1] ";" then
      let (_, se) ← rng? items[j + 1]
      return deletion text es se
  if j ≥ 1 && isAtom items[j - 1]! ";" then
    let (ss, _) ← rng? items[j - 1]!
    return deletion text ss ee
  return deletion text es ee

/-- The innermost tactic-sequence element on `path`: its index. -/
def tacticElem? (path : Array Syntax) : Option Nat := Id.run do
  let mut found := none
  for k in [2:path.size] do
    let seq := path[k - 2]!
    if seq.isOfKind ``Parser.Tactic.tacticSeq1Indented || seq.isOfKind ``Parser.Tactic.tacticSeqBracketed then
      found := some k
  return found

/-- The deletion of the list item at `path[k]` (a `rw` rule or a `simp`
    lemma) with its comma; `none` when it is the only item. -/
def itemDeletion (text : String) (path : Array Syntax) (k : Nat) : Option Edit := do
  let item := path[k]!
  let items := path[k - 1]!.getArgs
  let (is, ie) ← rng? item
  let real := items.filter (!isAtom · ",")
  if real.size ≤ 1 then none
  let j ← items.findIdx? fun i => rng? i == some (is, ie)
  if h : j + 1 < items.size then
    if isAtom items[j + 1] "," then
      if h2 : j + 2 < items.size then
        let (ns, _) ← rng? items[j + 2]
        return { start := is, stop := ns, replacement := "" }
  let (cs, _) ← rng? items[j - 1]!
  return { start := cs, stop := ie, replacement := "" }

/-- The index of the last element of `a` that satisfies `p`. -/
def lastIdx? (a : Array Syntax) (p : Syntax → Bool) : Option Nat := Id.run do
  let mut found := none
  for h : i in [0:a.size] do
    if p a[i] then found := some i
  return found

def tacticsThatConsume : List Name :=
  [``Parser.Tactic.cases, ``Parser.Tactic.rcases, ``Parser.Tactic.obtain, ``Parser.Tactic.induction]

/-- The proof edits of the `proof` form for one occurrence of `name`. -/
def occurrenceEdit (text : String) (cmd : Syntax) (n : Node) (name : String) (isHv : Bool) (rhsText : String) :
    Except String Edit := do
  let path := pathTo cmd n.start n.stop
  let elemK := tacticElem? path
  -- a `rw` rule or a `simp` lemma: the rewrite is the identity now
  if let some k := lastIdx? path fun s => s.isOfKind ``Parser.Tactic.rwRule || s.isOfKind ``Parser.Tactic.simpLemma then
    if let some ed := itemDeletion text path k then return ed
    if path[k]!.isOfKind ``Parser.Tactic.simpLemma then
      -- the only lemma: the bracket goes
      let some (bs, be) := rng? path[k - 2]! | throw "no range"
      return deletion text bs be
    let some ek := elemK | throw s!"a `rw` rule names `{name}` outside a tactic sequence"
    let some ed := tacticDeletion text path ek | throw "no range"
    return ed
  if let some ek := elemK then
    let elem := path[ek]!
    if elem.isOfKind ``Parser.Tactic.subst || elem.isOfKind ``Parser.Tactic.clear then
      if elem[1].getArgs.size ≤ 1 then
        let some ed := tacticDeletion text path ek | throw "no range"
        return ed
      return deletion text n.start n.stop
    -- `cases hv`, `obtain rfl := hv`: only when `hv` itself is the target
    if isHv && tacticsThatConsume.any elem.isOfKind then
      if let some (es, ee) := rng? elem then
        let t := (slice text es ee).trimAscii.copy
        if t.endsWith s!":= {name}" || (t.splitOn " ")[1]? == some name then
          let some ed := tacticDeletion text path ek | throw "no range"
          return ed
  -- `hv ▸ e` is `e` now
  if isHv then
    if let some k := lastIdx? path (·.isOfKind ``Parser.Term.subst) then
      let t := path[k]!
      if isRef t[0] name then
        let some (ts, te) := rng? t | throw "no range"
        let some (rs, re) := rng? t[2] | throw "no range"
        return { start := ts, stop := te, replacement := slice text rs re }
  return { start := n.start, stop := n.stop, replacement := if isHv then "rfl" else rhsText }

/-- Drop the edits that lie inside another edit; refuse partial overlaps.
    An insertion at the start or the end of another edit is kept: it goes
    before that edit (`applyEdits` applies it after, at the same offset). -/
def nest (edits : Array Edit) : Except String (Array Edit) := do
  let ins (e : Edit) : Bool := e.start == e.stop
  let sorted := edits.qsort fun a b =>
    a.start < b.start || (a.start == b.start && ((ins a && !ins b) || (ins a == ins b && a.stop > b.stop)))
  let mut out : Array Edit := #[]
  for ed in sorted do
    match out.back? with
    | some last =>
      if ed == last then continue
      if last.start ≤ ed.start && ed.stop ≤ last.stop && last.start < last.stop && !(ins ed && ed.start == last.stop) then continue
      if ed.start < last.stop then throw s!"two edits overlap at byte {ed.start}"
      out := out.push ed
    | none => out := out.push ed
  return out

/-- The binder names of `d`'s type, in order (implicit ones included). -/
def binderNames (env : Environment) (d : Name) : Option (Array Name) := do
  let ci ← env.find? d
  let rec go (t : Expr) (acc : Array Name) (fuel : Nat) : Array Name :=
    match fuel, t with
    | fuel + 1, .forallE n _ b _ => go b (acc.push n) fuel
    | _, _ => acc
  pure (go ci.type #[] 10000)

/-- The binder types of a `∀` telescope (with loose bound variables) and
    the type after `n` binders. -/
def telescope (t : Expr) (n : Nat) : Array Expr × Expr := Id.run do
  let mut t := t
  let mut doms := #[]
  for _ in [0:n] do
    let .forallE _ d b _ := t | break
    doms := doms.push d
    t := b
  return (doms, t)

/-- The index of `hv` in a telescope: the first binder after `after` whose
    type is an equation with the bound variable of binder `iv` as one side. -/
def eqIndexAfter (doms : Array Expr) (after iv : Nat) : Option Nat :=
  (List.range doms.size).find? fun k =>
    k > after && k > iv && (doms[k]!.isAppOfArity ``Eq 3) &&
      (doms[k]!.getArg! 1 == .bvar (k - 1 - iv) || doms[k]!.getArg! 2 == .bvar (k - 1 - iv))

/-- The declaration edits for all pairs of one declaration. -/
def declEdits (fe : FileElab) (d : Name) (fs : Array Finding) : Except String DeclEdits := do
  let some cmd0 := declCommand? fe d | throw s!"{d} has no declaration command in its file"
  let some parts := declParts? cmd0 | throw s!"{d} is not a `theorem` or `def` with a type"
  let some (cs, ce) := rng? cmd0 | throw "no range"
  let ns := nodesIn fe cs ce
  let pairs ← fs.mapM (findPair fe ns parts)
  let some (_, sigEnd) := rng? parts.type | throw "no type range"
  let some (valStart, valStop) := rng? parts.value | throw "no value range"
  let decl := parts.cmd[1]
  let some (_, declIdEnd) := rng? decl[1] | throw "no range for the declaration's name"
  -- the deleted ranges: the `v` identifiers (a group whose identifiers all go,
  -- whole) and the `hv` groups
  let mut del : Array (Nat × Nat) := #[]
  for g in parts.groups do
    let gone := g.idents.filter fun i => pairs.any fun p => rng? p.vIdent == rng? i
    if gone.isEmpty then continue
    if gone.size == g.idents.size then
      let some r := rng? g.stx | throw "no range"
      del := del.push r
    else
      for i in gone do
        let some r := rng? i | throw "no range"
        del := del.push r
  for p in pairs do
    if let some g := p.hvGroup then
      let some hr := rng? g.stx | throw "no range"
      del := del.push hr
    del := del ++ p.stmtDel
  let inDel (s e : Nat) := del.any fun (a, b) => a ≤ s && e ≤ b
  let userBound : Std.HashSet FVarId := ns.foldl (init := {}) fun s n =>
    if n.ti.isBinder then match n.ti.expr.consumeMData with
      | .fvar id => s.insert id
      | _ => s
    else s
  let mut subst : Array Edit := #[]
  let mut names := false
  let mut atHyps : Array (Array String) := #[]
  let mut proof : Except String (Array Edit) := .ok #[]
  for p in pairs do
    -- a reference to the binder, or to a copy of it that a tactic
    -- (`induction`, `cases`) reintroduced under the same name; a variable
    -- that the proof binds itself has a binder node
    let refersTo (ids : Array FVarId) (name : String) (n : Node) : Bool :=
      !n.ti.isBinder && match n.ti.expr.consumeMData with
        | .fvar id => ids.contains id || (name != "" &&
          !userBound.contains id && (n.ti.lctx.find? id).any (·.userName.eraseMacroScopes.toString == name))
        | _ => false
    let occ := ns.filter (refersTo p.vIds p.v)
    let hvOcc := ns.filter (refersTo p.hvIds p.hv)
    if hvOcc.any (·.stop ≤ sigEnd) then throw s!"the signature names `{p.hv}`"
    let mut seen : Array (Nat × Nat) := #[]
    let mut hyps : Array String := #[]
    for (n, isHv) in occ.map (·, false) ++ hvOcc.map (·, true) do
      if inDel n.start n.stop || seen.contains (n.start, n.stop) then continue
      seen := seen.push (n.start, n.stop)
      let name := if isHv then p.hv else p.v
      unless slice fe.text n.start n.stop == name do
        throw s!"an occurrence of `{name}` is `{slice fe.text n.start n.stop}`"
      if n.start ≥ valStart then
        names := true
        proof := do
          let acc ← proof
          return acc.push (← occurrenceEdit fe.text parts.cmd n name isHv p.rhsText)
        continue
      unless n.stop ≤ sigEnd do continue
      subst := subst.push { start := n.start, stop := n.stop, replacement := p.rhsText }
      -- the binder group that holds the occurrence: a hypothesis for `generalize … at`
      for g in parts.groups do
        if let some (gs, ge) := rng? g.stx then
          if gs ≤ n.start && n.stop ≤ ge then
            if g.idents.isEmpty || g.idents.any (!·.isIdent) then
              throw s!"an anonymous binder's type names `{p.v}`"
            for i in g.idents do
              unless hyps.contains (identName i) do hyps := hyps.push (identName i)
    atHyps := atHyps.push hyps
  -- `rhs` must be in scope where it replaces `v`: the groups of the `rhs`
  -- variables that the declaration binds after the first group whose type
  -- names `v` move before the first kept group after `v`'s group (the call
  -- sites move their arguments the same way, `callSites`)
  let groupIdx (id : FVarId) : Option Nat := parts.groups.findIdx? fun g =>
    g.idents.any fun i => match rng? i with
      | some r => (fvarsAt ns r true).contains id
      | none => false
  let gRange (gi : Nat) : Option (Nat × Nat) := rng? parts.groups[gi]!.stx
  let some (ts, te) := rng? parts.type | throw "no type range"
  let stmtBound (id : FVarId) : Bool := ns.any fun n =>
    n.ti.isBinder && ts ≤ n.start && n.stop ≤ te && n.ti.expr.consumeMData == .fvar id
  let mut moves : Array Edit := #[]
  let mut moved : Array String := #[]
  for p in pairs do
    let some vg := p.vGroup | continue
    let some vGi := parts.groups.findIdx? (rng? ·.stx == rng? vg.stx) | continue
    let namesV (gi : Nat) : Bool := match gRange gi with
      | some (gs, ge) => subst.any fun ed => gs ≤ ed.start && ed.stop ≤ ge
      | none => false
    let some fv := (List.range parts.groups.size).find? (fun gi => gi > vGi && namesV gi) | continue
    if let some id := p.holeIds.find? stmtBound then
      let nm := (ns.findSome? fun n => if n.ti.expr.consumeMData == .fvar id then
        (n.ti.lctx.find? id).map (·.userName.eraseMacroScopes.toString) else none).getD "?"
      throw s!"`rhs` names `{nm}`, a variable of the statement, and a binder of the declaration names `{p.v}`"
    let late := (p.holeIds.filterMap groupIdx).filter (· > fv)
    let G := late.toList.eraseDups.toArray.qsort (· < ·)
    if G.isEmpty then continue
    for gi in G do
      if namesV gi || parts.groups[gi]!.idents.isEmpty then
        throw s!"the binder group of an `rhs` variable cannot move: it names `{p.v}` or has no name"
      let some (gs, ge) := gRange gi | throw "no range"
      for n in ns do
        unless gs ≤ n.start && n.stop ≤ ge && !n.ti.isBinder do continue
        let .fvar id := n.ti.expr.consumeMData | continue
        if let some gj := groupIdx id then
          if gj > vGi && gj < gi && !G.contains gj then
            throw s!"the binder group of an `rhs` variable cannot move before `{p.v}`: its type names a later binder"
    let some a := (List.range parts.groups.size).find? (fun gi =>
        gi > vGi && !G.contains gi && !(gRange gi).any fun (s, e) => inDel s e) | continue
    let some (as, _) := gRange a | continue
    let text := " ".intercalate (G.toList.filterMap fun gi => (gRange gi).map fun (s, e) => slice fe.text s e)
    moves := moves.push { start := as, stop := as, replacement := text ++ " " }
    for gi in G do
      if let some r := gRange gi then del := del.push r
      moved := moved ++ parts.groups[gi]!.idents.map identName
  let sig := deletions fe.text del ++ subst ++ moves
  let inStatement := pairs.any (·.inStatement)
  -- the statement's own binders change the proof's `intro`s: only `restated` keeps the proof
  if inStatement then proof := .error "`v` or `hv` is part of the statement: the proof's `intro`s depend on them"
  let preamble : Option Edit := Id.run do
    if inStatement then return none
    let some (start, tactic) := proofStart? parts.value | return none
    let some (ps, _) := rng? start | return none
    let mut text := ""
    for (p, hyps) in pairs.zip atHyps do
      let loc := if hyps.isEmpty then "" else s!" at {" ".intercalate hyps.toList} ⊢"
      text := text ++ s!"generalize {p.hv} : {p.rhsText} = {p.v}{loc}; "
      if p.vLeft then text := text ++ s!"replace {p.hv} := {p.hv}.symm; "
    return some { start := ps, stop := ps, replacement := if tactic then text else s!"by {text}exact " }
  -- `suffices`: the old statement over `v`, `hv` and the binders whose types
  -- name `v`, proved by the old proof; one line before the first tactic
  let restated : Option Edit := Id.run do
    let some (start, true) := proofStart? parts.value | return none
    let some (ps, _) := rng? start | return none
    let some (ts, te) := rng? parts.type | return none
    let typeText := slice fe.text ts te
    if (typeText.splitOn "--").length > 1 then return none
    let cmdText := slice fe.text cs ce
    let h := if (cmdText.splitOn "hAlias").length > 1 then "hAlias'" else "hAlias"
    let mut binders : Array String := #[]
    let mut args : Array String := #[]
    let mut intros : Array String := #[]
    for g in parts.groups do
      let some (gs, ge) := rng? g.stx | continue
      let some t := g.type? | continue
      let some (tts, tte) := rng? t | continue
      let tText := slice fe.text tts tte
      if let some p := pairs.find? (fun p => p.hvGroup.any (rng? ·.stx == some (gs, ge))) then
        binders := binders.push s!"({p.hv} : {tText})"
        args := args.push "rfl"
        intros := intros.push p.hv
        continue
      for i in g.idents do
        if pairs.any (fun p => p.vGroup.isSome && rng? p.vIdent == rng? i) then
          binders := binders.push s!"({identName i} : {tText})"
          args := args.push "_"
          intros := intros.push (identName i)
      if subst.any (fun ed => gs ≤ ed.start && ed.stop ≤ ge) then
        if g.idents.isEmpty || g.idents.any (!·.isIdent) then return none
        let ns := g.idents.map identName
        binders := binders.push s!"({" ".intercalate ns.toList} : {tText})"
        args := args ++ ns
        intros := intros ++ ns
    -- the statement's binders up to its last `hv`: introduced, then passed on
    let stmt := pairs.filter (·.hvGroup.isNone)
    let mut fromTerm := s!"{h} {" ".intercalate args.toList}"
    unless stmt.isEmpty do
      let some ci := fe.env.find? d | return none
      let names := ((binderNames fe.env d).getD #[]).map (·.eraseMacroScopes.toString (escape := false))
      let doms := (telescope ci.type names.size).1
      -- the position after the declaration's binders
      let mut m := 0
      for nm in parts.groups.flatMap (·.idents.map identName) do
        while m < names.size && names[m]! != nm do m := m + 1
        m := m + 1
      let mut ivs : Array Nat := #[]
      let mut ihs : Array Nat := #[]
      for p in stmt do
        let iv? := if p.vGroup.isSome then names.idxOf? p.v
          else (List.range names.size).find? fun k => k ≥ m && names[k]! == p.v
        let some iv := iv? | return none
        let some ih := eqIndexAfter doms (max iv (m - 1)) iv | return none
        if p.vGroup.isNone then ivs := ivs.push iv
        ihs := ihs.push ih
      let top := ihs.foldl max 0
      let mut xs : Array String := #[]
      let mut sargs : Array String := #[]
      for k in [m:top + 1] do
        if ihs.contains k then sargs := sargs.push "rfl"
        else if ivs.contains k then sargs := sargs.push "_"
        else
          xs := xs.push s!"{h}_{k - m}"
          sargs := sargs.push s!"{h}_{k - m}"
      let call := s!"{h} {" ".intercalate (args ++ sargs).toList}"
      fromTerm := if xs.isEmpty then s!"({call})" else s!"(by intro {" ".intercalate xs.toList}; exact {call})"
    let quant := if binders.isEmpty then "" else s!"∀ {" ".intercalate binders.toList}, "
    let introPart := if intros.isEmpty then "" else s!"intro {" ".intercalate intros.toList}; "
    let text := s!"suffices {h} : {quant}{typeText} from {fromTerm}; {introPart}"
    -- one line: the line breaks of the copied texts become spaces
    let oneLine := " ".intercalate ((text.splitOn "\n").map (·.trimAsciiStart.copy))
    return some { start := ps, stop := ps, replacement := oneLine }
  return { sig, proof := proof >>= nest, preamble, restated, proofNames := names, pairs, declIdEnd,
           valueRange := (valStart, valStop), isTheorem := decl.isOfKind ``Parser.Command.theorem, moved }

-- --- call sites ------------------------------------------------------------------

/-- One pair as the call sites need it. -/
structure SitePair where
  v : String
  hv : String
  /-- `true` for `hv : v = rhs`. -/
  vLeft : Bool := true
  /-- `rhs`'s text and the variables in it (`Pair.holes`). -/
  rhsText : String := ""
  holes : Array (Nat × Nat × String) := #[]
  deriving Inhabited

def Pair.site (p : Pair) : SitePair :=
  { v := p.v, hv := p.hv, vLeft := p.vLeft, rhsText := p.rhsText, holes := p.holes }

/-- The call-site edits in one file. A call loses the two arguments; the
    arguments of the binders that moved (`DeclEdits.moved`) go before the
    first kept argument after `v`'s. When the two sides of the `hv`
    equation, instantiated with the call's arguments, are not
    definitionally equal (the caller passes its own term for `v`), the call
    also gets casts with the `hv` argument `h`, in three forms.
    `argCasts`: each other argument whose binder type names `v` becomes
    `(h ▸ a)`, and the call becomes `(h ▸ D …)` when its type names `v`.
    `callCast`: `(by obtain rfl := h; exact (D …))` when the `v` argument is
    a local variable, else `(h ▸ D …)`. `rewriteCasts` (also when the two
    sides are only not the same term): see `callSites`. -/
structure Sites where
  argCasts : Array Edit
  callCast : Array Edit
  /-- An error when a call has no text for its equation. -/
  rewriteCasts : Except String (Array Edit) := .ok #[]
  /-- A reason when a call site could not be mapped. -/
  problem : Option String

/-- The binder infos of `d`'s type, in order. -/
def binderInfos (env : Environment) (d : Name) : Option (Array BinderInfo) := do
  let ci ← env.find? d
  let rec go (t : Expr) (acc : Array BinderInfo) (fuel : Nat) : Array BinderInfo :=
    match fuel, t with
    | fuel + 1, .forallE _ _ b bi => go b (acc.push bi) fuel
    | _, _ => acc
  pure (go ci.type #[] 10000)

/-- `t`, with loose bound variables for the binders `0 … k - 1`, instantiated
    with `args`: does it name binder `iv` after beta reduction? -/
def namesBinder (t : Expr) (k iv : Nat) (args : Array Expr) : CoreM Bool := do
  if iv ≥ k then return false
  if args.size < k then return t.hasLooseBVar (k - 1 - iv)
  let marker : FVarId := ⟨`_aliasMarker⟩
  let xs := (args.extract 0 k).set! iv (.fvar marker)
  let e ← Core.betaReduce (t.instantiateRev xs)
  return e.containsFVar marker

/-- One pair at one call. -/
structure CallPair where
  iv : Nat
  ih : Nat
  sp : SitePair
  av : Option ((Nat × Nat) × Syntax)
  ah : Option ((Nat × Nat) × Syntax)
  /-- The sides of the instantiated `hv` equation: `v`'s argument and `rhs`. -/
  vSide : Expr
  rSide : Expr
  synDiff : Bool
  defDiff : Bool

/-- Every call of `d` in `fe` outside `skip`, for the pairs `(v, hv)`. With
    a `suffix`, every reference to `d` outside `skip` (a call's function, an
    identifier) also gets `suffix` after it: the edits then name the fresh
    declaration of a check (`ReplCheck`).

    Two arguments that elaborate to the same term: positional arguments fill
    the explicit binders in order, so the rank of the binder among the
    explicit binders picks the argument (a call by name or with `@`).

    `rewriteCasts`, for a pair whose two sides are not the same term: each
    other argument `a` whose binder type (beta reduced, with the call's
    arguments) names `v` and whose sides are not definitionally equal
    becomes `(by rewrite [E]; exact a)`; a call whose type names `v` becomes
    `(by have hAlias := D …; rewrite [E] at hAlias; exact hAlias)`. `E`
    rewrites `rhs` to the caller's term: `h` when its type has the two sides
    as they are; else `(show rhs' = x from h)` with `x` and `rhs'` written
    from the call's argument texts (an argument without syntax: the name of
    the local variable); for `h = ?_` a function `(fun (hAliasEqN : …) => …) ?_`.
    An implicit argument that no remaining explicit argument determines and
    that is a local variable gets a named argument `(b := x)`. -/
def callSites (fe : FileElab) (d : Name) (pairs : Array SitePair) (skip : Nat × Nat := (0, 0))
    (suffix : String := "") (moved : Array String := #[]) : IO Sites := do
  let fail (msg : String) : Sites := { argCasts := #[], callCast := #[], problem := some msg }
  let some names := binderNames fe.env d | return fail s!"{d} is not in the environment"
  let some bis := binderInfos fe.env d | return fail s!"{d} is not in the environment"
  let some ci := fe.env.find? d | return fail s!"{d} is not in the environment"
  let nameStr (k : Nat) : String := (names[k]?.map (·.eraseMacroScopes.toString (escape := false))).getD ""
  let allDoms := (telescope ci.type names.size).1
  let mut idx : Array (Nat × Nat) := #[]
  for sp in pairs do
    let some iv := names.idxOf? (Name.mkSimple sp.v) | return fail s!"{d}'s type does not bind `{sp.v}`"
    let some ih := eqIndexAfter allDoms iv iv | return fail s!"{d}'s type has no equation for `{sp.v}`"
    idx := idx.push (iv, ih)
  let mIdx := (moved.filterMap fun nm => (List.range names.size).find? (nameStr · == nm)).qsort (· < ·)
  let deleted (j : Nat) : Bool := idx.any fun (iv, ih) => j == iv || j == ih
  let byRange : Std.HashMap (Nat × Nat) (Array Node) :=
    fe.nodes.foldl (init := {}) fun m n => m.insert (n.start, n.stop) ((m.getD (n.start, n.stop) #[]).push n)
  let outside (n : Node) : Bool := !(skip.1 ≤ n.start && n.stop ≤ skip.2)
  let renames : Array Edit := if suffix.isEmpty then #[] else Id.run do
    let mut ends : Array Nat := #[]
    for n in fe.nodes do
      unless n.ti.expr.consumeMData.getAppFn.constName? == some d && !n.ti.isBinder && outside n do continue
      let e? := if n.ti.stx.isIdent then some n.stop
        else if n.ti.stx.isOfKind ``Parser.Term.app then (rng? n.ti.stx[0]).map (·.2) else none
      if let some e := e? then
        unless ends.contains e do ends := ends.push e
    return ends.map fun e => { start := e, stop := e, replacement := suffix }
  let mut argCasts : Array Edit := #[]
  let mut callCast : Array Edit := #[]
  let mut rewrite : Array Edit := #[]
  let mut rewriteErr : Option String := none
  let mut done : Array (Nat × Nat) := #[]
  for n in fe.nodes do
    unless n.ti.expr.consumeMData.getAppFn.constName? == some d && !n.ti.isBinder do continue
    unless n.ti.stx.isOfKind ``Parser.Term.app do continue
    if done.contains (n.start, n.stop) then continue
    unless outside n do continue
    done := done.push (n.start, n.stop)
    let pos := fe.fileMap.toPosition ⟨n.start⟩
    let full ← n.instExpr
    let args := full.getAppArgs
    let synArgs := n.ti.stx[1].getArgs
    let (doms, rest) := telescope ci.type args.size
    let fnStx := n.ti.stx[0]
    let explicitMode := fnStx.isOfKind ``Parser.Term.explicit
    let fnIdent := if explicitMode then fnStx[1] else fnStx
    let direct := explicitMode || (fnIdent.isIdent &&
      let fc := fnIdent.getId.eraseMacroScopes.components
      let dc := d.components
      fc.length ≤ dc.length && dc.drop (dc.length - fc.length) == fc)
    let positional := synArgs.filter fun a =>
      !a.isOfKind ``Parser.Term.namedArgument && !a.isOfKind ``Parser.Term.ellipsis
    let namedNames := synArgs.filterMap fun a =>
      if a.isOfKind ``Parser.Term.namedArgument then some (identName a[1]) else none
    let isExplicit (k : Nat) : Bool := explicitMode || (bis[k]?.any (·.isExplicit))
    let explicitIdx := (List.range (min args.size bis.size)).toArray.filter fun k =>
      isExplicit k && !namedNames.contains (nameStr k)
    -- the syntactic argument for binder index `i` named `nm`: its range and its term
    let argFor (i : Nat) (nm : String) : IO (Except String (Option ((Nat × Nat) × Syntax))) := do
      if let some a := synArgs.find? fun a => a.isOfKind ``Parser.Term.namedArgument && identName a[1] == nm then
        return .ok ((rng? a).map (·, a[3]))
      if i ≥ args.size then return .ok none
      let target := args[i]!
      let mut hits : Array ((Nat × Nat) × Syntax) := #[]
      for a in positional do
        let some r := rng? a | continue
        for cand in byRange.getD r #[] do
          if (← cand.instExpr) == target && !hits.any (·.1 == r) then hits := hits.push (r, a)
      if hits.size > 1 then
        -- positional arguments fill the explicit binders in order
        let byRank : Option (Nat × Nat) := if direct then do
            let rank ← explicitIdx.idxOf? i
            rng? (← positional[rank]?)
          else none
        match byRank.bind fun r => hits.find? (·.1 == r) with
        | some h => return .ok (some h)
        | none => return .error s!"{pos.line}:{pos.column}: two arguments of a call elaborate to the argument for `{nm}`"
      return .ok hits[0]?
    -- an implicit binder has syntax only as a named argument
    let syntaxFor (k : Nat) : IO (Option ((Nat × Nat) × Syntax)) := do
      if !isExplicit k && !namedNames.contains (nameStr k) then return none
      match ← argFor k (nameStr k) with
      | .ok a => return a
      | .error _ => return none
    -- the name of a local variable, when it means that variable at the call
    let localName (x : Expr) : Option String := do
      let .fvar id := x | none
      let ld ← n.ti.lctx.find? id
      guard (!ld.userName.hasMacroScopes)
      let ld' ← n.ti.lctx.findFromUserName? ld.userName
      guard (ld'.fvarId == id)
      pure (ld.userName.toString (escape := false))
    -- the text of binder `k`'s argument at this call
    let argText (k : Nat) : IO (Option String) := do
      match ← syntaxFor k with
      | some (_, t) => return (rng? t).map fun (s, e) =>
          let x := slice fe.text s e
          if (atomic t) then x else s!"({x})"
      | none => return (args[k]?.bind localName)
    -- the `hv` equation of this call
    let eqOf (ih : Nat) : Option Expr := do
      let dom ← doms[ih]?
      let eq := (dom.instantiateLevelParams ci.levelParams full.getAppFn.constLevels!).instantiateRev
        (args.extract 0 ih)
      guard (eq.isAppOfArity ``Eq 3)
      pure eq
    let mut toDelete : Array (Nat × Nat) := #[]
    let mut casts : Array (Nat × String × Bool) := #[]
    let mut cps : Array CallPair := #[]
    for ((iv, ih), sp) in idx.zip pairs do
      let av ← match ← argFor iv sp.v with
        | .ok a => pure a
        | .error msg => return fail msg
      let ah ← match ← argFor ih sp.hv with
        | .ok a => pure a
        | .error msg => return fail msg
      if let some (r, _) := av then toDelete := toDelete.push r
      if let some (r, _) := ah then toDelete := toDelete.push r
      let some eq := eqOf ih | continue
      let (vSide, rSide) := if sp.vLeft then (eq.getArg! 1, eq.getArg! 2) else (eq.getArg! 2, eq.getArg! 1)
      let defDiff := !(← n.ti.runMetaM n.ctx (isDefEq (eq.getArg! 1) (eq.getArg! 2)))
      cps := cps.push { iv, ih, sp, av, ah, vSide, rSide, synDiff := eq.getArg! 1 != eq.getArg! 2, defDiff }
      if let some (_, t) := ah then
        let some (ts, te) := rng? t | continue
        if iv < args.size && defDiff then
          casts := casts.push (iv, slice fe.text ts te, args[iv]!.isFVar)
    -- the moved binders' arguments go before the first kept explicit argument after `v`'s
    let mut moveIns : Array Edit := #[]
    unless mIdx.isEmpty do
      let mut texts : Array String := #[]
      let mut ranges : Array (Nat × Nat) := #[]
      for k in mIdx do
        if let some (r, t) ← syntaxFor k then
          if positional.any (rng? · == some r) then
            ranges := ranges.push r
            texts := texts.push ((rng? t).map (fun (s, e) => slice fe.text s e) |>.getD "")
      let lo := idx.foldl (fun a (iv, _) => min a iv) names.size
      let hi := mIdx.foldl min names.size
      let mut anchor : Option Nat := none
      for j in [lo + 1:hi] do
        if anchor.isSome || deleted j || !isExplicit j then continue
        if let some (r, _) ← syntaxFor j then
          if positional.any (rng? · == some r) then anchor := some r.1
      if let some a := anchor then
        unless ranges.isEmpty do
          moveIns := #[{ start := a, stop := a, replacement := " ".intercalate texts.toList ++ " " }]
          toDelete := toDelete ++ ranges
    let dels := deletions fe.text toDelete ++ moveIns ++ renames.filter fun r => n.start ≤ r.start && r.stop ≤ n.stop
    let toLocal (eds : Array Edit) : Array Edit :=
      eds.map fun ed => { ed with start := ed.start - n.start, stop := min ed.stop n.stop - n.start }
    let appText (eds : Array Edit) : String := applyEdits (slice fe.text n.start n.stop) (toLocal eds)
    -- `rewriteCasts`
    let relevant := cps.filter fun cp => cp.synDiff && cp.iv < args.size
    if relevant.isEmpty then rewrite := rewrite ++ dels
    else
      let mut rules : Array (CallPair × String) := #[]
      let mut lambdas : Array String := #[]
      let mut holes : Array String := #[]
      for cp in relevant do
        let x? ← argText cp.iv
        -- `rhs` written with the call's argument texts
        let mut r? : Option String := some ""
        let mut last := 0
        for (s, e, nm) in cp.sp.holes do
          let k? := (List.range names.size).find? (nameStr · == nm)
          let t? ← match k? with
            | some k => argText k
            | none => pure none
          r? := match r?, t? with
            | some acc, some t => some (acc ++ slice cp.sp.rhsText last s ++ t)
            | _, _ => none
          last := e
        let rText? := r?.map (· ++ slice cp.sp.rhsText last cp.sp.rhsText.utf8ByteSize)
        let printed := match x?, rText? with
          | some x, some r => some (if cp.sp.vLeft then s!"{x} = {r}" else s!"{r} = {x}")
          | _, _ => none
        let hText? := match cp.ah with
          | some (_, t) => (rng? t).map fun (s, e) => let h := slice fe.text s e; if (atomic t) then h else s!"({h})"
          | none => args[cp.ih]?.bind localName
        let isHole := cp.ah.any (·.2.isOfKind ``Parser.Term.syntheticHole)
        let hType ← n.ti.runMetaM n.ctx do
          match args[cp.ih]? with
          | some h => return some (← instantiateMVars (← inferType h))
          | none => return none
        let asIs := match hType with
          | some t => t.isAppOfArity ``Eq 3 && (if cp.sp.vLeft then t.getArg! 1 == cp.vSide && t.getArg! 2 == cp.rSide
              else t.getArg! 1 == cp.rSide && t.getArg! 2 == cp.vSide)
          | none => false
        let term? : Option String := if isHole then
            printed.map fun _ =>
              let nm := s!"hAliasEq{lambdas.size}"
              nm
          else if asIs then hText?
          else match printed, hText? with
            | some eq, some h => some s!"(show {eq} from {h})"
            | _, h => h
        match term? with
        | none =>
          rewriteErr := some s!"{pos.line}:{pos.column}: no text for the equation `{cp.sp.hv}` at this call"
        | some term =>
          if isHole then
            lambdas := lambdas.push s!"({term} : {printed.getD ""})"
            holes := holes.push (cp.ah.map (fun ((s, e), _) => slice fe.text s e) |>.getD "?_")
          rules := rules.push (cp, (if cp.sp.vLeft then "← " else "") ++ term)
      -- the arguments whose types name a `v` with a caller's own term
      let mut argEdits := dels
      let mut castArgs : Array Nat := #[]
      for j in [0:min args.size doms.size] do
        if deleted j || mIdx.contains j then continue
        let mut rs : Array String := #[]
        for (cp, rule) in rules do
          if cp.defDiff && (← n.ti.runMetaM n.ctx (namesBinder doms[j]! j cp.iv args)) then rs := rs.push rule
        if rs.isEmpty then continue
        let some ((_, _), t) ← syntaxFor j | continue
        let some (s, e) := rng? t | continue
        castArgs := castArgs.push j
        argEdits := argEdits.push
          { start := s, stop := e, replacement := underBy (fe.fileMap.toPosition ⟨s⟩).column
              s!"(by rewrite [{", ".intercalate rs.toList}]; exact " (slice fe.text s e) ")" }
      let mut rsR : Array String := #[]
      for (cp, rule) in rules do
        if ← n.ti.runMetaM n.ctx (namesBinder rest doms.size cp.iv args) then rsR := rsR.push rule
      -- implicit arguments that no remaining explicit argument determines
      if !castArgs.isEmpty || !rsR.isEmpty then
        let mut named : String := ""
        for k in [0:min args.size doms.size] do
          if isExplicit k || deleted k || namedNames.contains (nameStr k) then continue
          unless bis[k]!.isImplicit || bis[k]!.isStrictImplicit do continue
          let determined := (List.range (min args.size doms.size)).any fun j =>
            j > k && isExplicit j && !deleted j && !castArgs.contains j && doms[j]!.hasLooseBVar (j - 1 - k)
          if determined then continue
          if let some x := args[k]?.bind localName then named := named ++ s!" ({nameStr k} := {x})"
        unless named.isEmpty do argEdits := argEdits.push { start := n.stop, stop := n.stop, replacement := named }
      let lamPre := if lambdas.isEmpty then "" else s!"((fun {" ".intercalate lambdas.toList} => "
      let lamPost := if lambdas.isEmpty then "" else s!") {" ".intercalate holes.toList})"
      let inner : Option String :=
        if !rsR.isEmpty then some (underBy (pos.column + lamPre.length) "(by have hAlias := " (appText argEdits)
          s!"; rewrite [{", ".intercalate rsR.toList}] at hAlias; exact hAlias)")
        else if !lambdas.isEmpty then some (appText argEdits) else none
      let text? := inner.map (lamPre ++ · ++ lamPost)
      match text? with
      | some t => rewrite := rewrite.push { start := n.start, stop := n.stop, replacement := t }
      | none => rewrite := rewrite ++ argEdits
    if casts.isEmpty then
      argCasts := argCasts ++ dels
      callCast := callCast ++ dels
      continue
    let castWith (hs : Array (Nat × String × Bool)) (t : String) : String :=
      hs.foldr (fun (_, h, _) acc => h ++ " ▸ " ++ acc) t
    -- `argCasts`: the other arguments whose binder types name `v`
    let mut argEdits := dels
    for j in [0:args.size] do
      let hs := casts.filter fun (iv, _, _) => iv < j && (doms[j]?.any (·.hasLooseBVar (j - 1 - iv)))
      if hs.isEmpty || deleted j then continue
      let some nm := names[j]? | continue
      match ← argFor j (nm.eraseMacroScopes.toString (escape := false)) with
      | .ok (some ((s, e), _)) =>
        argEdits := argEdits.push { start := s, stop := e, replacement := s!"({castWith hs (slice fe.text s e)})" }
      | _ => pure ()
    let resultNames := casts.filter fun (iv, _, _) => iv < doms.size && rest.hasLooseBVar (doms.size - 1 - iv)
    if resultNames.isEmpty then
      argCasts := argCasts ++ argEdits
    else
      let wrappedArgs := s!"({castWith resultNames (appText argEdits)})"
      argCasts := argCasts.push { start := n.start, stop := n.stop, replacement := wrappedArgs }
    -- `callCast`
    let app := appText dels
    let wrapped := if casts.all (·.2.2) then
        let obtains := casts.foldl (fun acc (_, h, _) => acc ++ s!"obtain rfl := {h}; ") ""
        underBy pos.column s!"(by {obtains}exact (" app "))"
      else s!"({castWith casts app})"
    callCast := callCast.push { start := n.start, stop := n.stop, replacement := wrapped }
  -- a rename inside a call's edit is part of that edit's text
  let rewriteCasts : Except String (Array Edit) := match rewriteErr with
    | some msg => .error msg
    | none => nest (rewrite ++ renames)
  match nest (argCasts ++ renames), nest (callCast ++ renames) with
  | .ok a, .ok b => return { argCasts := a, callCast := b, rewriteCasts, problem := none }
  | .error msg, _ | _, .error msg => return fail msg

end DefToStructure.Alias
