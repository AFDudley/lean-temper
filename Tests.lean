/-
  Tests of the alias transform (`LeanTemper.Alias`) and the REPL check
  (`LeanTemper.ReplCheck`).

    .lake/build/bin/tests <armada-lean checkout> <Lean REPL>

  The alias cases elaborate with `Init` only; the REPL case runs the given
  REPL, with the target checkout's `LEAN_PATH`.
-/
import Lean
import LeanTemper.Target
import LeanTemper.Alias
import LeanTemper.ReplCheck

open Lean LeanTemper

namespace Tests

/-! ## The alias transform (`LeanTemper.Alias`)

Each case elaborates a whole snippet (with `Init` only), computes the
declaration edits and the call-site edits of one form from the info tree,
compares the text, and elaborates the result: it must have no error. -/

/-- The proof form of a case. -/
inductive ProofForm where
  | unchanged | substituted | generalized

structure AliasCase where
  name : String
  src : String
  decl : Name
  binders : Array String
  proof : ProofForm
  /-- The `callCast` call-site form; else `argCasts`. -/
  callCast : Bool := false
  /-- The `rewriteCasts` call-site form. -/
  rewrite : Bool := false
  want : String

def fooSrc (use : String) : String :=
  s!"theorem foo \{n : Nat} (m : Nat) (hn : n = m + 1) : 0 < n := by\n  subst hn\n  exact Nat.succ_pos m\n\n{use}"

def bazSrc (use : String) : String :=
  s!"theorem baz (a : Nat) (b : Nat) (hb : b = a + 1) (h : 0 < b) : b ≠ 0 := by\n  subst hb\n  exact Nat.pos_iff_ne_zero.mp h\n\n{use}"

def nbSrc (use : String) : String :=
  s!"theorem nb (l : List Nat) (hl : 0 < l.length) (pre : List Nat) (a : Nat) (heq : l = pre ++ [a]) :\n    0 < (pre ++ [a]).length := heq ▸ hl\n\n{use}"

def aliasCases : List AliasCase := [
  { name := "implicit binder at the call site; the proof names hv (`subst hn` goes)",
    src := fooSrc "theorem use1 : 0 < 3 := foo 2 rfl\n", decl := `foo, binders := #["n"], proof := .substituted,
    want := "theorem foo (m : Nat) : 0 < (m + 1) := by\n  exact Nat.succ_pos m\n\ntheorem use1 : 0 < 3 := foo 2\n" },
  { name := "named argument",
    src := fooSrc "theorem use2 : 0 < 3 := foo (hn := rfl) 2\n", decl := `foo, binders := #["n"], proof := .substituted,
    want := "theorem foo (m : Nat) : 0 < (m + 1) := by\n  exact Nat.succ_pos m\n\ntheorem use2 : 0 < 3 := foo 2\n" },
  { name := "dot notation; the proof does not name v or hv",
    src := "structure P where\n  x : Nat\n\ntheorem P.le (p : P) (k : Nat) (hk : k = p.x) : k ≤ p.x + 1 := by\n  omega\n\ntheorem use3 (p : P) : p.x ≤ p.x + 1 := p.le p.x rfl\n",
    decl := `P.le, binders := #["k"], proof := .unchanged,
    want := "structure P where\n  x : Nat\n\ntheorem P.le (p : P) : p.x ≤ p.x + 1 := by\n  omega\n\ntheorem use3 (p : P) : p.x ≤ p.x + 1 := p.le\n" },
  { name := "the proof names v and hv; a hypothesis names v",
    src := bazSrc "theorem use4 : (3 : Nat) ≠ 0 := baz 2 3 rfl (by decide)\n", decl := `baz, binders := #["b"],
    proof := .substituted,
    want := "theorem baz (a : Nat) (h : 0 < (a + 1)) : (a + 1) ≠ 0 := by\n  exact Nat.pos_iff_ne_zero.mp h\n\ntheorem use4 : (3 : Nat) ≠ 0 := baz 2 (by decide)\n" },
  { name := "the proof kept behind `generalize … at h ⊢`",
    src := bazSrc "theorem use4 : (3 : Nat) ≠ 0 := baz 2 3 rfl (by decide)\n", decl := `baz, binders := #["b"],
    proof := .generalized,
    want := "theorem baz (a : Nat) (h : 0 < (a + 1)) : (a + 1) ≠ 0 := by\n  generalize hb : (a + 1) = b at h ⊢; replace hb := hb.symm; subst hb\n  exact Nat.pos_iff_ne_zero.mp h\n\ntheorem use4 : (3 : Nat) ≠ 0 := baz 2 (by decide)\n" },
  { name := "a caller with its own variable for v: argument casts",
    src := bazSrc "theorem use5 (k : Nat) (hk : k = 2 + 1) (h : 0 < k) : k ≠ 0 := baz 2 k hk h\n", decl := `baz,
    binders := #["b"], proof := .substituted,
    want := "theorem baz (a : Nat) (h : 0 < (a + 1)) : (a + 1) ≠ 0 := by\n  exact Nat.pos_iff_ne_zero.mp h\n\ntheorem use5 (k : Nat) (hk : k = 2 + 1) (h : 0 < k) : k ≠ 0 := (hk ▸ baz 2 (hk ▸ h))\n" },
  { name := "a caller with its own variable for v: a call cast",
    src := bazSrc "theorem use5 (k : Nat) (hk : k = 2 + 1) (h : 0 < k) : k ≠ 0 := baz 2 k hk h\n", decl := `baz,
    binders := #["b"], proof := .substituted, callCast := true,
    want := "theorem baz (a : Nat) (h : 0 < (a + 1)) : (a + 1) ≠ 0 := by\n  exact Nat.pos_iff_ne_zero.mp h\n\ntheorem use5 (k : Nat) (hk : k = 2 + 1) (h : 0 < k) : k ≠ 0 := (by obtain rfl := hk; exact (baz 2 h))\n" },
  -- class 5: `rhs` names binders bound after a binder whose type names `v`
  { name := "rhs binders move before the binders that name v; the call's arguments move too",
    src := nbSrc "theorem useNb : 0 < ([1] ++ [2]).length := nb ([1] ++ [2]) (by decide) [1] 2 rfl\n",
    decl := `nb, binders := #["l"], proof := .substituted,
    want := "theorem nb (pre : List Nat) (a : Nat) (hl : 0 < (pre ++ [a]).length) :\n    0 < (pre ++ [a]).length := hl\n\ntheorem useNb : 0 < ([1] ++ [2]).length := nb [1] 2 (by decide)\n" },
  { name := "a signature line left with ` :` only joins the line before",
    src := "theorem nb2 (l : List Nat) (hl : 0 < l.length)\n    (pre : List Nat) (a : Nat) (heq : l = pre ++ [a]) :\n    0 < (pre ++ [a]).length := heq ▸ hl\n",
    decl := `nb2, binders := #["l"], proof := .substituted,
    want := "theorem nb2 (pre : List Nat) (a : Nat) (hl : 0 < (pre ++ [a]).length) :\n    0 < (pre ++ [a]).length := hl\n" },
  { name := "moved binders and a caller with its own variable: rewrite casts",
    src := nbSrc "theorem useNb2 (xs : List Nat) (hx : 0 < xs.length) (h : xs = [1] ++ [2]) : 0 < ([1] ++ [2]).length :=\n  nb xs hx [1] 2 h\n",
    decl := `nb, binders := #["l"], proof := .substituted, rewrite := true,
    want := "theorem nb (pre : List Nat) (a : Nat) (hl : 0 < (pre ++ [a]).length) :\n    0 < (pre ++ [a]).length := hl\n\ntheorem useNb2 (xs : List Nat) (hx : 0 < xs.length) (h : xs = [1] ++ [2]) : 0 < ([1] ++ [2]).length :=\n  nb [1] 2 (by rewrite [← h]; exact hx)\n" },
  { name := "the equation argument is `?_` of a `refine`: rewrite casts under a function",
    src := nbSrc "theorem useNb3 (xs : List Nat) (hx : 0 < xs.length) (h : xs = [1] ++ [2]) : 0 < ([1] ++ [2]).length := by\n  refine nb xs hx [1] 2 ?_\n  exact h\n",
    decl := `nb, binders := #["l"], proof := .substituted, rewrite := true,
    want := "theorem nb (pre : List Nat) (a : Nat) (hl : 0 < (pre ++ [a]).length) :\n    0 < (pre ++ [a]).length := hl\n\ntheorem useNb3 (xs : List Nat) (hx : 0 < xs.length) (h : xs = [1] ++ [2]) : 0 < ([1] ++ [2]).length := by\n  refine ((fun (hAliasEq0 : xs = (([1]) ++ [(2)])) => nb [1] 2 (by rewrite [← hAliasEq0]; exact hx)) ?_)\n  exact h\n" },
  -- class 6: two arguments elaborate to the same term
  { name := "two arguments with the same term: the binder's rank among the explicit binders",
    src := "theorem dup (n : Nat) (m : Nat) (hm : m = n) : m ≤ n := hm ▸ Nat.le_refl _\n\ntheorem useDup : 3 ≤ 3 := dup 3 3 rfl\n",
    decl := `dup, binders := #["m"], proof := .substituted,
    want := "theorem dup (n : Nat) : n ≤ n := Nat.le_refl _\n\ntheorem useDup : 3 ≤ 3 := dup 3\n" },
  -- class 1: the caller's own variable, implicit arguments that only cast arguments determine
  { name := "a caller with its own variable, a `have` without a type: rewrite casts and named implicits",
    src := "structure S where\n  ch : Nat\n\ndef Mem (c : Nat) : Prop := c = c\n\ntheorem callee {c : Nat} {s : S} (hC : Mem c) (hchan : s.ch = c) {a b : Nat} (hab : a ≤ b ∧ c = c) :\n    a ≤ b → c = c := fun _ => hab.2\n\ntheorem caller (s : S) (c : Nat) (h : s.ch = c) (hC : Mem c) (a b : Nat) (hr : a ≤ b) : a ≤ b → c = c := by\n  have hinv := callee hC h ⟨hr, rfl⟩\n  exact hinv\n",
    decl := `callee, binders := #["c"], proof := .unchanged, rewrite := true,
    want := "structure S where\n  ch : Nat\n\ndef Mem (c : Nat) : Prop := c = c\n\ntheorem callee {s : S} (hC : Mem s.ch) {a b : Nat} (hab : a ≤ b ∧ s.ch = s.ch) :\n    a ≤ b → s.ch = s.ch := fun _ => hab.2\n\ntheorem caller (s : S) (c : Nat) (h : s.ch = c) (hC : Mem c) (a b : Nat) (hr : a ≤ b) : a ≤ b → c = c := by\n  have hinv := (by have hAlias := callee (by rewrite [h]; exact hC) (by rewrite [h]; exact ⟨hr, rfl⟩) (s := s) (a := a) (b := b); rewrite [h] at hAlias; exact hAlias)\n  exact hinv\n" },
  { name := "a call over two lines under `(by have hAlias := …`: the second line moves right",
    src := "structure S where\n  ch : Nat\n\ndef Mem (c : Nat) : Prop := c = c\n\ntheorem callee {c : Nat} {s : S} (hC : Mem c) (hchan : s.ch = c) {a b : Nat} (hab : a ≤ b ∧ c = c) :\n    a ≤ b → c = c := fun _ => hab.2\n\ntheorem caller (s : S) (c : Nat) (h : s.ch = c) (hC : Mem c) (a b : Nat) (hr : a ≤ b) : a ≤ b → c = c := by\n  have hinv := callee hC h\n    ⟨hr, rfl⟩\n  exact hinv\n",
    decl := `callee, binders := #["c"], proof := .unchanged, rewrite := true,
    want := "structure S where\n  ch : Nat\n\ndef Mem (c : Nat) : Prop := c = c\n\ntheorem callee {s : S} (hC : Mem s.ch) {a b : Nat} (hab : a ≤ b ∧ s.ch = s.ch) :\n    a ≤ b → s.ch = s.ch := fun _ => hab.2\n\ntheorem caller (s : S) (c : Nat) (h : s.ch = c) (hC : Mem c) (a b : Nat) (hr : a ≤ b) : a ≤ b → c = c := by\n  have hinv := (by have hAlias := callee (by rewrite [h]; exact hC)\n                       (by rewrite [h]; exact ⟨hr, rfl⟩) (s := s) (a := a) (b := b); rewrite [h] at hAlias; exact hAlias)\n  exact hinv\n" },
  -- class 2: the equation's side is not the caller's term itself
  { name := "the caller's term is a coercion of a subtype: `show` with the call's texts",
    src := "structure S where\n  ch : Nat\n\ntheorem callee2 (c : Nat) (s : S) (hchan : s.ch = c) : c = c ∧ s.ch = s.ch := ⟨rfl, rfl⟩\n\ntheorem caller2 (s : S) (L : Nat) (hd : 0 < L) (h : s.ch = (⟨L, hd⟩ : {c // 0 < c}).1) : L = L := by\n  have hU := callee2 L s h\n  exact hU.1\n",
    decl := `callee2, binders := #["c"], proof := .unchanged, rewrite := true,
    want := "structure S where\n  ch : Nat\n\ntheorem callee2 (s : S) : s.ch = s.ch ∧ s.ch = s.ch := ⟨rfl, rfl⟩\n\ntheorem caller2 (s : S) (L : Nat) (hd : 0 < L) (h : s.ch = (⟨L, hd⟩ : {c // 0 < c}).1) : L = L := by\n  have hU := (by have hAlias := callee2 s; rewrite [(show s.ch = L from h)] at hAlias; exact hAlias)\n  exact hU.1\n" },
  -- class 3: `v` implicit, the variable occurs in the equation's other side
  { name := "an implicit v whose variable occurs in the equation's other side: `show`, a named implicit",
    src := "def hc (p : Nat) : Nat := p + 1\n\ndef Cons (r : Nat → Nat) : Prop := True\n\ndef recStep (r : Nat → Nat) (c p : Nat) : Nat → Nat := fun x => if x = c then p else r x\n\ntheorem callee3 {r : Nat → Nat} (hr : Cons r) {c : Nat} {p : Nat} (hv : hc p = c) : Cons (recStep r c p) := trivial\n\ntheorem caller3 (r : Nat → Nat) (hr : Cons r) (rest : List (Nat × Nat)) (hvalid : ∀ cp ∈ rest, hc cp.2 = cp.1)\n    (c p : Nat) (hm : (c, p) ∈ rest) : Cons (recStep r c p) := by\n  exact callee3 hr (hvalid (c, p) hm)\n",
    decl := `callee3, binders := #["c"], proof := .unchanged, rewrite := true,
    want := "def hc (p : Nat) : Nat := p + 1\n\ndef Cons (r : Nat → Nat) : Prop := True\n\ndef recStep (r : Nat → Nat) (c p : Nat) : Nat → Nat := fun x => if x = c then p else r x\n\ntheorem callee3 {r : Nat → Nat} (hr : Cons r) {p : Nat} : Cons (recStep r (hc p) p) := trivial\n\ntheorem caller3 (r : Nat → Nat) (hr : Cons r) (rest : List (Nat × Nat)) (hvalid : ∀ cp ∈ rest, hc cp.2 = cp.1)\n    (c p : Nat) (hm : (c, p) ∈ rest) : Cons (recStep r c p) := by\n  exact (by have hAlias := callee3 hr (p := p); rewrite [(show (hc p) = c from (hvalid (c, p) hm))] at hAlias; exact hAlias)\n" },
  -- class 4: the two sides are definitionally equal, not the same term; a later `rw` needs the caller's term
  { name := "sides equal by definition only (`rfl`): the result rewritten to the caller's term",
    src := "def insT (l : List Nat) (n : Nat) : Nat := l.length + n\n\ntheorem callee4 (trees nl : List Nat) (tn : Nat) (htn : tn = insT trees nl.length) : tn = insT trees nl.length := htn\n\ntheorem caller4 (t : List Nat) (x : Nat) (y : Nat) (hy : y = insT t 1) : y = insT t 1 := by\n  have h := callee4 t [x] (insT t 1) rfl\n  rw [h]; exact hy\n",
    decl := `callee4, binders := #["tn"], proof := .substituted, rewrite := true,
    want := "def insT (l : List Nat) (n : Nat) : Nat := l.length + n\n\ntheorem callee4 (trees nl : List Nat) : (insT trees nl.length) = insT trees nl.length := rfl\n\ntheorem caller4 (t : List Nat) (x : Nat) (y : Nat) (hy : y = insT t 1) : y = insT t 1 := by\n  have h := (by have hAlias := callee4 t [x]; rewrite [← (show (insT t 1) = (insT t ([x]).length) from rfl)] at hAlias; exact hAlias)\n  rw [h]; exact hy\n" } ]

def extraAliasCases : List AliasCase := [
  -- class 3: an implicit argument whose value is no local variable: printed from the info tree
  { name := "an implicit argument that is no local variable: its printed value as a named argument",
    src := "def hc (p : Nat) : Nat := p + 1\n\ndef Cons (r : Nat → Nat) : Prop := True\n\ndef recStep (r : Nat → Nat) (c p : Nat) : Nat → Nat := fun x => if x = c then p else r x\n\ntheorem callee3 {r : Nat → Nat} (hr : Cons r) {c : Nat} {p : Nat} (hv : hc p = c) : Cons (recStep r c p) := trivial\n\ntheorem caller3 (r : Nat → Nat) (hr : Cons r) (cs ps : Nat → Nat) (hvalid : ∀ i, hc (ps i) = cs i) (i : Nat) :\n    Cons (recStep r (cs i) (ps i)) := callee3 hr (hvalid i)\n",
    decl := `callee3, binders := #["c"], proof := .unchanged, rewrite := true,
    want := "def hc (p : Nat) : Nat := p + 1\n\ndef Cons (r : Nat → Nat) : Prop := True\n\ndef recStep (r : Nat → Nat) (c p : Nat) : Nat → Nat := fun x => if x = c then p else r x\n\ntheorem callee3 {r : Nat → Nat} (hr : Cons r) {p : Nat} : Cons (recStep r (hc p) p) := trivial\n\ntheorem caller3 (r : Nat → Nat) (hr : Cons r) (cs ps : Nat → Nat) (hvalid : ∀ i, hc (ps i) = cs i) (i : Nat) :\n    Cons (recStep r (cs i) (ps i)) := (by have hAlias := callee3 hr (p := (ps i)); rewrite [(hvalid i)] at hAlias; exact hAlias)\n" } ]

def runAliasCase (c : AliasCase) : IO Bool := do
  let fe0 ← Alias.elabText "t.lean" `t c.src
  unless fe0.errors.isEmpty do
    IO.println s!"FAIL {c.name}: the snippet has errors: {fe0.errors}"
    return false
  let fs := c.binders.map fun b => { declaration := c.decl.toString, binder := b, rhs := "", at_ := "t.lean:1" }
  let (fe, deE) ← Alias.declEditsHoisting fe0 c.decl fs "t.lean" `t
  match deE with
  | .error msg =>
    IO.println s!"FAIL {c.name}: {msg}"
    return false
  | .ok de =>
    let skip := ((Alias.declCommand? fe c.decl).bind Alias.rng?).getD (0, 0)
    let sites ← Alias.callSites fe c.decl (de.pairs.map (·.site)) skip "" de.moved
    if let some p := sites.problem then
      IO.println s!"FAIL {c.name}: {p}"
      return false
    let proof ← match c.proof, de.proof with
      | .unchanged, _ => pure #[]
      | .generalized, _ => pure de.preamble.toArray
      | .substituted, .ok eds => pure eds
      | .substituted, .error msg => do
        IO.println s!"FAIL {c.name}: {msg}"
        return false
    let calls ← if c.rewrite then match sites.rewriteCasts with
        | .ok eds => pure eds
        | .error msg => do IO.println s!"FAIL {c.name}: {msg}"; return false
      else pure (if c.callCast then sites.callCast else sites.argCasts)
    let .ok edits := Alias.nest (de.sig ++ proof ++ calls)
      | IO.println s!"FAIL {c.name}: overlapping edits"; return false
    let got := applyEdits fe.text edits
    unless got == c.want do
      IO.println s!"FAIL {c.name}:\n--- got\n{got}--- want\n{c.want}"
      return false
    let after ← Alias.elabText "t.lean" `t got
    unless after.errors.isEmpty do
      IO.println s!"FAIL {c.name}: the result has errors: {after.errors}"
      return false
    IO.println s!"ok   {c.name}"
    return true

/-! ## The REPL check of an alias candidate (`LeanTemper.ReplCheck`)

`foo` and a caller in its scope (`namespace A`, a `variable`), and a caller
in another scope (`namespace B`, `open A in`): the right candidate has no
error; a candidate whose proof still names `hn` fails in the declaration;
callers that keep the deleted arguments fail at the call sites. -/

def replSrc : String :=
  "namespace A\nvariable {α : Type}\n\ntheorem foo (x : α) (n : Nat) (m : Nat) (hn : n = m + 1) : 0 < n ∧ x = x := by\n  subst hn\n  exact ⟨Nat.succ_pos m, rfl⟩\n\ntheorem useA : 0 < 3 := (foo () 3 2 rfl).1\n\nend A\n\nnamespace B\nopen A in\ntheorem useB : 0 < 4 := (A.foo () 4 3 rfl).1\nend B\n"

def replCase (c : Repl.Client) : IO Bool := do
  let fe ← Alias.elabText "t.lean" `t replSrc
  let fs := #[{ declaration := "A.foo", binder := "n", rhs := "", at_ := "t.lean:1" : Alias.Finding }]
  let .ok de := Alias.declEdits fe `A.foo fs | IO.println "FAIL repl check: no declaration edits"; return false
  let .ok peds := de.proof | IO.println "FAIL repl check: no substituted proof"; return false
  let skip := ((Alias.declCommand? fe `A.foo).bind Alias.rng?).getD (0, 0)
  let sc ← Alias.callSites fe `A.foo (de.pairs.map (·.site)) skip ReplCheck.suffix
  let t0 ← IO.monoMsNow
  let (sess, errs) ← ReplCheck.sync c "t.lean" fe none
  unless errs.isEmpty do IO.println s!"FAIL repl check: the snippet has errors: {errs}"; return false
  let some dIdx := sess.chunkAt skip.1 | IO.println "FAIL repl check: no chunk"; return false
  let rename : Edit := { start := de.declIdEnd, stop := de.declIdEnd, replacement := ReplCheck.suffix }
  let stub : Edit := { start := de.valueRange.1, stop := de.valueRange.2, replacement := ":= sorry" }
  let .ok dEdits := Alias.nest (de.sig ++ peds ++ #[rename]) | return false
  let .ok badEdits := Alias.nest (de.sig ++ #[rename]) | return false
  let .ok stubEdits := Alias.nest (de.sig ++ #[rename, stub]) | return false
  let dText := sess.editedChunk dIdx dEdits
  let dStub := sess.editedChunk dIdx stubEdits
  let callersOf (eds : Array Edit) := (sess.touched eds).filter (· != dIdx) |>.map fun i => (sess, i, sess.editedChunk i eds)
  let good := callersOf sc.argCasts
  unless good.size == 2 do IO.println s!"FAIL repl check: {good.size} caller commands, not 2"; return false
  let (d1, c1) ← ReplCheck.check c sess dIdx dText dStub good
  unless d1.isEmpty && c1.isEmpty do IO.println s!"FAIL repl check: the right candidate has errors: {d1 ++ c1}"; return false
  let (d2, _) ← ReplCheck.check c sess dIdx (sess.editedChunk dIdx badEdits) dStub good
  if d2.isEmpty then IO.println "FAIL repl check: a proof that names `hn` passed"; return false
  let renamesOnly := sc.argCasts.filter (·.replacement == ReplCheck.suffix)
  let (d3, c3) ← ReplCheck.check c sess dIdx dText dStub (callersOf renamesOnly)
  unless d3.isEmpty && !c3.isEmpty do
    IO.println s!"FAIL repl check: callers with the old arguments: {d3 ++ c3}"; return false
  IO.println s!"ok   repl check (session and 3 checks in {(← IO.monoMsNow) - t0} ms)"
  return true

end Tests

open Tests in
unsafe def main (args : List String) : IO UInt32 := do
  let [root, repl] := args | do IO.eprintln "usage: tests <armada-lean checkout> <Lean REPL>"; return 2
  let sp ← LeanTemper.targetSearchPath root
  let home := (← IO.getEnv "HOME").getD ""
  initSearchPath (← findSysroot s!"{home}/.elan/bin/lean") sp
  let mut failed := 0
  let mut total := 0
  for c in aliasCases ++ extraAliasCases do
    total := total + 1
    unless ← runAliasCase c do failed := failed + 1
  let c ← Repl.start repl sp "/dev/null"
  total := total + 1
  unless ← replCase c do failed := failed + 1
  c.stop
  IO.println s!"{total - failed}/{total} passed"
  return if failed == 0 then 0 else 1
