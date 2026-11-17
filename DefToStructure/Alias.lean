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

-- --- deletions ---------------------------------------------------------------

def isSp (b : UInt8) : Bool := b == 32 || b == 9
def isWs (b : UInt8) : Bool := isSp b || b == 10 || b == 13

/-- The edit that deletes `[s, e)`: a line left empty goes whole; an item
    at a line start keeps the indentation; otherwise the space before (or,
    with none, after) the item goes with it. -/
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
  let rhsOf (side : Syntax) : Except String String := do
    let some (ss, se) := rng? side | throw "no range"
    return if atomic side then slice fe.text ss se else s!"({slice fe.text ss se})"
  let base : Pair := { finding := f, v := f.binder, hv := "", vLeft := true, rhsText := "", vIds, hvIds := #[],
                       vIdent, vGroup := vGi?.map (parts.groups[·]!), hvGroup := none, stmtDel := vStmtDel }
  -- `hv`: a later binder of the declaration
  if let some gi := vGi? then
    for g in parts.groups.extract (gi + 1) parts.groups.size do
      let some t := g.type? | continue
      unless g.idents.size == 1 do continue
      let some (vLeft, side) := sides t | continue
      let some hr := rng? g.idents[0]! | continue
      return { base with hv := identName g.idents[0]!, vLeft, rhsText := ← rhsOf side,
                         hvIds := fvarsAt ns hr true, hvGroup := some g }
  -- `hv`: a premise of the statement
  for a in typeNodes do
    unless a.isOfKind ``Parser.Term.arrow do continue
    let some (vLeft, side) := sides a[0] | continue
    let some (s, _) := rng? a[0] | continue
    let some (_, e) := rng? a[1] | continue
    return { base with vLeft, rhsText := ← rhsOf side, stmtDel := vStmtDel.push (s, e) }
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

/-- Drop the edits that lie inside another edit; refuse partial overlaps. -/
def nest (edits : Array Edit) : Except String (Array Edit) := do
  let sorted := edits.qsort fun a b => a.start < b.start || (a.start == b.start && a.stop > b.stop)
  let mut out : Array Edit := #[]
  for ed in sorted do
    match out.back? with
    | some last =>
      if ed == last then continue
      if last.start ≤ ed.start && ed.stop ≤ last.stop && last.start < last.stop then continue
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
  let some (valStart, _) := rng? parts.value | throw "no value range"
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
  let sig := deletions fe.text del ++ subst
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
  return { sig, proof := proof >>= nest, preamble, restated, proofNames := names, pairs }

-- --- call sites ------------------------------------------------------------------

/-- The call-site edits in one file. A call loses the two arguments. When
    the two sides of the `hv` equation, instantiated with the call's
    arguments, are not definitionally equal (the caller passes its own term
    for `v`), the call also gets casts with the `hv` argument `h`, in two
    forms. `argCasts`: each other argument whose binder type names `v`
    becomes `(h ▸ a)`, and the call becomes `(h ▸ D …)` when its type
    names `v`. `callCast`: `(by obtain rfl := h; exact (D …))` when the `v`
    argument is a local variable, else `(h ▸ D …)`. -/
structure Sites where
  argCasts : Array Edit
  callCast : Array Edit
  /-- A reason when a call site could not be mapped. -/
  problem : Option String

/-- Every call of `d` in `fe` outside `skip`, for the pairs `(v, hv)`. -/
def callSites (fe : FileElab) (d : Name) (pairs : Array (String × String)) (skip : Nat × Nat := (0, 0)) : IO Sites := do
  let fail (msg : String) : Sites := { argCasts := #[], callCast := #[], problem := some msg }
  let some names := binderNames fe.env d | return fail s!"{d} is not in the environment"
  let some ci := fe.env.find? d | return fail s!"{d} is not in the environment"
  let allDoms := (telescope ci.type names.size).1
  let mut idx : Array (Nat × Nat) := #[]
  for (v, _) in pairs do
    let some iv := names.idxOf? (Name.mkSimple v) | return fail s!"{d}'s type does not bind `{v}`"
    let some ih := eqIndexAfter allDoms iv iv | return fail s!"{d}'s type has no equation for `{v}`"
    idx := idx.push (iv, ih)
  let byRange : Std.HashMap (Nat × Nat) (Array Node) :=
    fe.nodes.foldl (init := {}) fun m n => m.insert (n.start, n.stop) ((m.getD (n.start, n.stop) #[]).push n)
  let mut argCasts : Array Edit := #[]
  let mut callCast : Array Edit := #[]
  let mut done : Array (Nat × Nat) := #[]
  for n in fe.nodes do
    unless n.ti.expr.consumeMData.getAppFn.constName? == some d && !n.ti.isBinder do continue
    unless n.ti.stx.isOfKind ``Parser.Term.app do continue
    if done.contains (n.start, n.stop) then continue
    if skip.1 ≤ n.start && n.stop ≤ skip.2 then continue
    done := done.push (n.start, n.stop)
    let pos := fe.fileMap.toPosition ⟨n.start⟩
    let full ← n.instExpr
    let args := full.getAppArgs
    let synArgs := n.ti.stx[1].getArgs
    let (doms, rest) := telescope ci.type args.size
    -- the syntactic argument for binder index `i` named `nm`: its range and its term
    let argFor (i : Nat) (nm : String) : IO (Except String (Option ((Nat × Nat) × Syntax))) := do
      if let some a := synArgs.find? fun a => a.isOfKind ``Parser.Term.namedArgument && identName a[1] == nm then
        return .ok ((rng? a).map (·, a[3]))
      if i ≥ args.size then return .ok none
      let target := args[i]!
      let mut hits : Array ((Nat × Nat) × Syntax) := #[]
      for a in synArgs do
        if a.isOfKind ``Parser.Term.namedArgument || a.isOfKind ``Parser.Term.ellipsis then continue
        let some r := rng? a | continue
        for cand in byRange.getD r #[] do
          if (← cand.instExpr) == target && !hits.any (·.1 == r) then hits := hits.push (r, a)
      if hits.size > 1 then
        return .error s!"{pos.line}:{pos.column}: two arguments of a call elaborate to the argument for `{nm}`"
      return .ok hits[0]?
    -- the `hv` equation of this call: are its sides definitionally equal?
    let sidesDiffer (ih : Nat) : IO Bool := do
      let some dom := doms[ih]? | return false
      let eq := (dom.instantiateLevelParams ci.levelParams full.getAppFn.constLevels!).instantiateRev
        (args.extract 0 ih)
      unless eq.isAppOfArity ``Eq 3 do return false
      return !(← n.ti.runMetaM n.ctx (isDefEq (eq.getArg! 1) (eq.getArg! 2)))
    let mut toDelete : Array (Nat × Nat) := #[]
    let mut casts : Array (Nat × String × Bool) := #[]
    for ((iv, ih), (v, hv)) in idx.zip pairs do
      let av ← match ← argFor iv v with
        | .ok a => pure a
        | .error msg => return fail msg
      let ah ← match ← argFor ih hv with
        | .ok a => pure a
        | .error msg => return fail msg
      if let some (r, _) := av then toDelete := toDelete.push r
      if let some (r, t) := ah then
        toDelete := toDelete.push r
        let some (ts, te) := rng? t | continue
        if iv < args.size && (← sidesDiffer ih) then
          casts := casts.push (iv, slice fe.text ts te, args[iv]!.isFVar)
    let dels := deletions fe.text toDelete
    if casts.isEmpty then
      argCasts := argCasts ++ dels
      callCast := callCast ++ dels
      continue
    let castWith (hs : Array (Nat × String × Bool)) (t : String) : String :=
      hs.foldr (fun (_, h, _) acc => h ++ " ▸ " ++ acc) t
    let toLocal (eds : Array Edit) : Array Edit :=
      eds.map fun ed => { ed with start := ed.start - n.start, stop := min ed.stop n.stop - n.start }
    let appText (eds : Array Edit) : String := applyEdits (slice fe.text n.start n.stop) (toLocal eds)
    -- `argCasts`: the other arguments whose binder types name `v`
    let mut argEdits := dels
    for j in [0:args.size] do
      let hs := casts.filter fun (iv, _, _) => iv < j && (doms[j]?.any (·.hasLooseBVar (j - 1 - iv)))
      if hs.isEmpty || idx.any (fun (iv, ih) => j == iv || j == ih) then continue
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
        s!"(by {obtains}exact ({app}))"
      else s!"({castWith casts app})"
    callCast := callCast.push { start := n.start, stop := n.stop, replacement := wrapped }
  return { argCasts, callCast, problem := none }

end DefToStructure.Alias
