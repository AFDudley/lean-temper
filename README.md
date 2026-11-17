# lean_def_to_structure

One Lean program that converts a predicate `def P (binders) : Prop := body`
of an armada-lean checkout to the one-field structure
`structure P (binders) : Prop where holds : body`, adds the lemma
`P.iff : P args ↔ body`, and repairs the proofs that break. The same input
gives the same output. The tool lives here, not in armada-lean, because
armada-lean goes upstream.

Why: the `repeatedPremise` linter (`ArmadaLean/Lint/TypeDoctrine.lean`)
excludes a hypothesis once its head is an `ArmadaLean`-declared structure.
Workers made this conversion by hand many times. The brief is
`.scratch/briefs/2026-11-14-codemod-def-to-structure.md`.

## Build and run

```
cd tools/lean_def_to_structure && lake build
.lake/build/bin/def_to_structure --checkout /path/to/armada-lean-worktree \
  --slot 2 --names RegistryConsistent,Adjudicator.IsDAG --report report.json
```

`lean-toolchain` here must equal the target's. The checkout is a throwaway
worktree, never a live branch. Every `lake` command runs as
`flock ~/.cache/lean-run/locks/slot-N.lock nice <command>` with
`~/.elan/bin` on `PATH` and `CI` unset. Logs, `state.json` and the LSP log
go to `<checkout>/.scratch/codemod/`.

Tests: `.lake/build/bin/tests <checkout> <repl>` (the snippets parse with `Init`
and `Mathlib.Tactic.Says` from the checkout; the alias cases elaborate with
`Init`; the REPL case runs `<repl>`, the Lean REPL).

## Alias mode

```
.lake/build/bin/def_to_structure --checkout /path/to/armada-lean-worktree \
  --slot 3 --alias WORKLIST.json --repl /path/to/repl/.lake/build/bin/repl \
  --report scripts/codemod/alias-report.json
```

`--repl` is the Lean REPL (https://github.com/leanprover-community/repl)
built at the target's toolchain; the tool starts it with the target's
`LEAN_PATH`.

The work list holds `aliasHypothesis` findings of `scripts/type_lint.lean`
(`declaration`, `binder` v, `rhs`, `at`). For each declaration the mode
deletes the binders `v` and `hv : v = rhs` (or `rhs = v`), puts the
source text of `rhs` for `v` in the signature, and deletes the two
arguments at every call site. Code: `DefToStructure/Alias.lean`; driver:
`stepAlias` in `Main.lean`.

Every fact comes from the info tree of an in-process elaboration of the
current file text (`Alias.elabText`, `Elab.async` off), not from the text:

| fact | source |
|------|--------|
| the free variables of `v` and `hv` | the binder term nodes at the binder identifiers |
| `hv`'s equation and the side that is `rhs` | the `=` binder whose one side is an identifier node that elaborated to `v` |
| the occurrences of `v` and `hv` in the signature and in the proof | term nodes whose expression is that free variable (`c` in `c.participants` has its own node); binders in the proof that reuse the name are other variables |
| a call site | a term node of `app` syntax whose expression is an application of `D` |
| the argument for `v` or `hv` | a named argument `(v := e)`; else the syntactic argument whose own term node elaborated to the application's argument at that binder's index. An implicit argument has no syntax; the receiver of dot notation is no syntactic argument |
| a caller's own term for `v` | the two sides of `hv`'s type, instantiated with the call's arguments, are not definitionally equal (`isDefEq` in the call's context) |
| a caller's own variable for `v` | that, and the application's argument at `v`'s index is a free variable |
| a binder that a tactic reintroduced (`induction`, `cases`) | a free variable with the user name of `v` or `hv` and no binder node in the declaration |

Proof forms, tried in this order for each declaration (the first without an
error stays):

| proof form | edit |
|------------|------|
| unchanged | the proof does not name `v` or `hv` |
| substituted | `v` becomes `rhs`; a `rw` rule or a `simp` lemma that names `hv` goes (the whole `rw` when it was its only rule); `subst` and `clear` of `v` or `hv`, and `cases hv`, `rcases hv`, `induction hv`, `obtain … := hv` go; `hv ▸ e` becomes `e`; another `hv` becomes `rfl` |
| behind `generalize` | the first tactic gets `generalize hv : rhs = v at h₁ … ⊢; replace hv := hv.symm;` (`replace` only for `v = rhs`; `h₁ …` are the binders whose types named `v`); a term proof becomes `by <that>exact <term>`. `generalize` also abstracts the occurrences of `rhs` that the statement had itself |

A call site loses the two arguments. When the caller passes its own term
for `v` (see the table above), the call also gets casts with the `hv`
argument `h`. Call-site forms, in this order:

| call-site form | edit |
|----------------|------|
| argument casts | each other argument whose binder type names `v` becomes `(h ▸ a)`; the call becomes `(h ▸ D …)` when its type names `v` |
| call cast | `(by obtain rfl := h; exact (D …))` when the `v` argument is a local variable, else `(h ▸ D …)` |

Loop (`stepAlias`): one declaration at a time, the last declaration of the
last file first. A caller then comes before its callee, so the caller's
arguments are already `rhs`, not its own variable. For each declaration:
the analysis of its file and of every file that names it, on their current
texts; then the forms, each checked through the Lean REPL
(`DefToStructure/ReplCheck.lean`). An error in the declaration moves to the
next proof form; an error in a caller moves to the next call-site form. The
first form without an error is written to the files; with none, the files
keep their texts. A module is rebuilt (`lake build <Module>`) before a file
that imports it is elaborated. A second pass retries each declaration that
failed on a form.

The REPL check. Each file of a check runs once in the REPL, one command per
request, so that the environment after each command stays available
(`ReplCheck.Session`; the command boundaries come from the in-process
elaboration). After an accepted form, the next check runs again only the
commands from the first changed one on, and a file after the first changed
file in import order starts again (its imports changed). A Lean environment
cannot lose a constant, so a candidate is checked under a fresh name
`D_aliasCheck`: the new declaration in the environment before `D`; then each
changed command that names `D` (every reference renamed to
`D_aliasCheck`) in the environment before that command, after the
declaration (its proof `sorry` for a theorem: a caller needs its type only)
is added there. When the scopes at the caller differ from the scopes at `D`,
that addition closes the caller's namespaces and sections, opens `D`'s (with
their `open`, `variable`, `universe`, `set_option`, `omit` and `include`
commands) in a `section`, and opens the caller's again (`ReplCheck.bridge`).
One request is one command. At the end of the loop, one `lake build` of the
changed modules confirms the accepted forms; a failure stops the tool.
The end is the full check of the def mode, without
`scripts/update_gate_baseline.py` (the mode changes nothing under
`scripts/` outside `scripts/codemod/`), and `check.sh --json --base <head>`.
The report's `alias` field lists each finding: `fixed`, `form`, `reason`
(the last form's first error), `attempts` (every form and its first error),
`files_changed`.

Not handled (reported as not fixed): `v` or `hv` bound in the statement
(`∀ n, n = W.length → …`): the proof's `intro`s depend on them.

## Files

- `Main.lean`: the driver. Steps: the base build and `scripts/type_lint.lean`
  (the "before" list); `importModules` of the target (discovery, and the
  parser for the loop); discovery and the guards; the conversion; the
  dependents in import order through `lake serve`; one full check at the
  end.
- `DefToStructure/Lsp.lean`: the `lake serve` client of the def mode. JSON-RPC with
  `Lean.JsonRpc`; `didOpen`/`didChange` with the whole text; `waitIdle`
  returns the diagnostics once `$/lean/fileProgress` reports nothing left for
  the current version. Queries: `textDocument/definition`, and
  `$/lean/rpc/call` with `Lean.Widget.getInteractiveTermGoal`,
  `Lean.Widget.getInteractiveGoals`, `Lean.Widget.getInteractiveDiagnostics`
  and `Lean.Widget.getGoToLocation`.
- `DefToStructure/Parse.lean`: the target file as command `Syntax`. The
  parser runs with the imports' environment; only the commands that change
  later parsing elaborate (`open`, `namespace`, `section`, `end`,
  `set_option`, `universe`, `macro`, `syntax`, `notation`, …). Declarations
  are the server's job.
- `DefToStructure/Patterns.lean`: the decision. One diagnostic in, one repair
  or none out.
- `DefToStructure/Discovery.lean`: `findDeclarationRanges?`, the `def`
  pieces from the parsed declaration, the conversion text, the import graph
  from file headers.
- `DefToStructure/Alias.lean`: the alias mode: the in-process elaboration,
  the declaration edits and the call-site edits from the info tree.
- `DefToStructure/Repl.lean`: the Lean REPL client (one JSON command per
  request). `DefToStructure/ReplCheck.lean`: the alias mode's check through
  it (sessions, scopes, the fresh-name check).
- `Tests.lean`: 55 cases of the decision (the 43 recorded cases of the first
  tool, the silent projection, the parenthesized-receiver goal, the two
  applications under `unfold`, the negation cases and the `Decidable` instances),
  9 alias cases (an implicit argument, a named argument, dot notation,
  a proof that names `v` and `hv`, the `generalize` form, the `suffices`
  forms, the two cast forms), and the REPL check (a caller in `D`'s scope and
  one in another scope; a right candidate, a wrong proof, wrong callers).
- `scope.lean`: scope measurement, `lake env lean scope.lean` in a built
  checkout.

## Elaboration data

A predicate is recognized by **location**: the position of its name in the
`structure` declaration the tool wrote, or the position of its `holds`
field. Every fact below is a declaration location that the server returns.

| fact | source |
|------|--------|
| the syntax at the diagnostic range | the parsed file (`Parse.stackAt`) |
| the expected type's head of a term | `getInteractiveTermGoal` at the term's first token, then `getGoToLocation` on the head tag of its `type` (the tag with the longest all-`appFn` `subexprPos`) |
| the goal's head before a tactic | `getInteractiveGoals` at the tactic's start, the same way |
| what an identifier or field index resolves to | `textDocument/definition` |
| the type's head of the term a diagnostic is about | `getInteractiveDiagnostics`, then `getGoToLocation` on the head tag of the **second expression embedded in the diagnostic** |
| the expected type's head of a projection term `h.1` | the third embedded expression, the same way |
| the head under `¬` | the same queries, the head tag under the first argument (`/1/0/…`) |

The last two rows are the one place where the diagnostic itself is a source.
They read the `Expr` objects Lean attached to the message (through their RPC
references), not the message text. No position query gives those two types:
the server's info lookup (`InfoTree.hoverableInfoAtM?`) prefers the
innermost info at a position, and every position of a projection node or an
application node belongs to one of its children (`h` and `1` in `h.1`); an
intermediate of a dotted identifier (`hord.isDAG` in `hord.isDAG.irrefl`)
has no info at all (`Lean/Elab/App.lean`, `elabAppLValsAux` elaborates it
with `expectedType? := none`). Lean puts `e` first and `eType` second in
`throwTypeMismatchError`, `throwFunctionExpected`, the invalid-field and the
invalid-projection errors, and the expected type third in the mismatch
errors.

## Repair patterns

Each pattern is a fixed edit. An error that matches no pattern stops the
tool; the report names the file, the line and the message, and nothing more
changes. No pattern inserts `sorry`, `admit`, `axiom` or `native_decide`.

| pattern | decision | edit |
|---------|----------|------|
| `holds-apply` | the term at the range is an application with no term info (it did not elaborate), and the diagnosed term's type is `P …` | `f.holds args` |
| `holds-field` | the range sits in a projection chain; the first field that resolves to nothing is the failing step; the diagnosed term's type is `P …` | `h.holds.f`, `h.holds.2.1` |
| `holds-type` | a term whose type is `P …` where the expected type is not | `t.holds`, `(t).holds` for an application |
| `wrap` | a term whose expected type is `P …` and whose type is not; not already `⟨…⟩` | `⟨t⟩` |
| `wrap-nested` | the argument of `⟨…⟩ : P` whose expected type is `P`'s body, itself a structure | `⟨t⟩` |
| `constructor` | a tactic from a fixed list failed and the goal before it is `P …` | `constructor` before the tactic |
| `unfold-iff` | the range is a name in `unfold` that resolves to `P` (or, without an error, any `unfold` naming `P`: on a hypothesis it reports nothing and changes nothing) | goal: `simp only [P.iff]` (every application, as `unfold` did; `rw` rewrites one instantiation only); hypothesis: `rw [P.iff] at h` (`simp only … at h` moves `h` to the end of the context, and a later `revert` binds in the other order); then `unfold` of the rest |
| `simp-iff` | the range is a `simp` family call (or `says`) with a name that resolves to `P` | `P.iff` in place of `P` |
| `decidable-iff` | the stack holds an `instance` whose declared type is `Decidable (X)` with the head of `X` resolving to `P`, and whose value is an `inferInstanceAs` application | `decidable_of_iff _ (P.iff ..).symm` |
| `not-wrap` / `not-holds` | a term of type `¬ P args` where `¬ body` is expected, or the converse: the heads under `Not` on both sides (the first argument's head, tag `/1/0/…` of the explicit form) | `fun h => t ⟨h⟩` / `fun h => t h.holds`, parenthesized in an argument position |
| `constructor-split` | every `constructor` whose goal before it is `P …` and which this run did not insert (`constructor` on the old `def` split the body; on the structure it enters it) | `constructor` before it |
| `holds-proj` | every `t.k` in the file whose index resolves to `P.holds` (the silent case: `t.k` was part `k` of the body, now it is the whole body) | `t.holds.k` |

## Loop

For each file that imports a converted module, in import order: `didOpen`;
until the file has no error and no silent case: read the diagnostics; if the
silent scans (`holds-proj`, and `unfold P` whose name resolves to a
converted predicate, which reports no error on a hypothesis) find anything,
apply those alone (`holds-proj`, the silent `unfold`, `constructor-split`), else decide one repair per error (last position first,
no overlapping edits); apply, write the file, `didChange`. A round with an error and no repair
stops the tool. A repair that would repeat (same pattern, same detail, same
line text) stops the tool. An edited module is rebuilt with
`lake build <Module>` before the next file opens, so that a dependent's
imports are the repaired `.olean` files. No full `lake build` runs inside the
loop.

At the end: `lake build`, the linter modules, `scripts/type_lint.lean` (the
"after" list), `scripts/update_gate_baseline.py --hashes-only`,
`bash scripts/check.sh --json` (it also elaborates
`docs/counterexamples/*.lean`), and the JSON report.

## Guards

- A predicate under `ArmadaLean/Spec/` is refused. The loop never writes a
  file under `ArmadaLean/Spec/`.
- `git grep "Spec\.<name>\b" -- ArmadaLean/Spec` must find nothing.
- `--resume` continues a stopped run after a hand edit of the file that
  stopped it: it skips the base build, the discovery and the conversion, and
  reads `state.json` and `lint-before.jsonl`.

## Report

The predicates, the repairs (file, line, pattern, predicate, detail), the
rounds, the linter summaries before and after, the finding lines removed and
added (the `example` field dropped: it is a nondeterministic
representative), the `check.sh --json` `_ok` fields, the files changed, the
timings of every `lake` command, `stopped` and `stops`.
