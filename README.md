# lean-temper

A compiler from Lean that elaborates but is badly structured (often written
by AI) to Lean in a declared type-doctrine form. It runs named passes over
the elaborated declarations of a target checkout. Each pass preserves
meaning: an edit is checked through the Lean REPL, and a pass either
transforms a declaration or leaves it unchanged and reports why. The same
input gives the same output.

The target project's rules — which paths the tool never edits, where its
source lives, how to run its lint and its final check — are a JSON config
file the run names (`--config`), not code. `examples/armada-lean.json` is
the config for armada-lean.

`docs/design.md` describes the planned design: the passes, their order, the
failure rules, and the build plan. This README describes the tool as it is now.

## The alias pass

```
.lake/build/bin/lean-temper --checkout /path/to/target-worktree --slot 2 \
  --config examples/armada-lean.json --alias WORKLIST.json \
  --repl /path/to/repl/.lake/build/bin/repl --report report.json
```

`--repl` is the Lean REPL (https://github.com/leanprover-community/repl)
built at the target's toolchain; the tool starts it with the target's
`LEAN_PATH`. The target's `lean-toolchain` must equal this repository's.
The checkout is a throwaway worktree, never a live branch. Every `lake`
command runs as `flock ~/.cache/lean-run/locks/slot-N.lock nice <command>`
with `~/.elan/bin` on `PATH` and `CI` unset. Logs and the REPL log go to
`<checkout>/.scratch/codemod/`.

One work-list entry names a declaration `D`, a binder `v` and the
right-hand side of an equation binder `hv : v = rhs` (or `rhs = v`): a
value-plus-equation binder pair that a call site need not pass, because the
caller's own argument for `v` already is `rhs`. The pass deletes the
binders `v` and `hv` from `D`, puts the source text of `rhs` for `v` in the
signature, and deletes the two arguments at every call site. Code:
`LeanTemper/Alias.lean`; driver: `stepAlias` in `Main.lean`.

Every fact comes from the info tree of an in-process elaboration of the
current file text (`Alias.elabText`, `Elab.async` off), not from the text:

| fact | source |
|------|--------|
| the free variables of `v` and `hv` | the binder term nodes at the binder identifiers |
| `hv`'s equation and the side that is `rhs` | the `=` binder whose one side is an identifier node that elaborated to `v` |
| the occurrences of `v` and `hv` in the signature and in the proof | term nodes whose expression is that free variable (`c` in `c.participants` has its own node); binders in the proof that reuse the name are other variables |
| a call site | a term node of `app` syntax whose expression is an application of `D` |
| the argument for `v` or `hv` | a named argument `(v := e)`; else the syntactic argument whose own term node elaborated to the application's argument at that binder's index. An implicit argument has no syntax; the receiver of dot notation is no syntactic argument. When two arguments elaborate to that term (`f order … order`), the binder's rank among the explicit binders picks the positional argument (a call by name or with `@` only) |
| the binders that move | the groups of the `rhs` variables (the free variables of the term nodes in `rhs`) that come after the first group whose type names `v`; they go before the first kept group after `v`'s group. A group that names `v`, or whose type names a binder that stays before it, does not move (not fixed) |
| the hoist | an `rhs` variable bound by the statement's leading `∀ x y : T,` while a binder of the declaration names `v` (`∀ suf pre, order = pre ++ suf → …`): the `∀` becomes the binder group `(x y : T)` after the last binder (the type stays the same chain of `∀`; no call site changes), and the proof starts with `suffices hHoist : <the old statement> from hHoist x y;`. The analysis then runs again on that text (`Alias.declEditsHoisting`), and the move above puts `(x y : T)` before the binders that name `v` |
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

A call site loses the two arguments; the arguments of the moved binders go
before the first kept explicit argument after `v`'s. When the caller passes
its own term for `v` (see the table above), the call also gets casts with
the `hv` argument `h`. Call-site forms, in this order:

| call-site form | edit |
|----------------|------|
| argument casts | each other argument whose binder type names `v` becomes `(h ▸ a)`; the call becomes `(h ▸ D …)` when its type names `v` |
| call cast | `(by obtain rfl := h; exact (D …))` when the `v` argument is a local variable, else `(h ▸ D …)` |
| rewrite casts | for a pair whose two sides are not the same term (also when they are only definitionally equal: a later `rw` needs the caller's term): each other argument `a` whose binder type, beta reduced with the call's arguments, names `v` (sides not definitionally equal) becomes `(by rewrite [E]; exact a)`; a call whose type names `v` becomes `(by have hAlias := D …; rewrite [E] at hAlias; exact hAlias)`; an implicit argument that no remaining explicit argument determines gets `(b := x)`: `x` is the name of a local variable, else the argument's elaborated value at the original call printed in the call's context (`ppExpr`, one line; not when the print has `✝`, `?` or `sorry`). The REPL check decides whether the print elaborates; when it does not, the form fails |

`E` rewrites `rhs` to the caller's term `x`: `h` (or `← h` for `v = rhs`)
when the elaborated type of `h` has the two sides as they are; else
`(show rhs' = x from h)`, with `x` and `rhs'` written from the call's
argument texts (an argument without syntax: the name of its local
variable, else its printed value as above). For `h = ?_` (a `refine` goal)
the call becomes `((fun (hAliasEq0 : rhs' = x) => D …) ?_)` and `E` is
`hAliasEq0`.

Not handled (reported as not fixed): `v` or `hv` bound in the statement
(`∀ n, n = W.length → …`): the proof's `intro`s depend on them.

## The check through the REPL

Loop (`stepAlias`): one declaration at a time, the last declaration of the
last file first. A caller then comes before its callee, so the caller's
arguments are already `rhs`, not its own variable. For each declaration:
the analysis of its file and of every file that names it, on their current
texts; then the forms, each checked through the Lean REPL
(`LeanTemper/ReplCheck.lean`). An error in the declaration moves to the next
proof form; an error in a caller moves to the next call-site form. The
first form without an error is written to the files; with none, the files
keep their texts. A module is rebuilt (`lake build <Module>`) before a file
that imports it is elaborated. A second pass retries each declaration that
failed on a form.

Each file of a check runs once in the REPL, one command per request, so
that the environment after each command stays available
(`ReplCheck.Session`; the command boundaries come from the in-process
elaboration). After an accepted form, the next check runs again only the
commands from the first changed one on, and a file after the first changed
file in import order starts again (its imports changed). A Lean environment
cannot lose a constant, so a candidate is checked under a fresh name
`D_aliasCheck`: the new declaration in the environment before `D`; then
each changed command that names `D` (every reference renamed to
`D_aliasCheck`) in the environment before that command, after the
declaration (its proof `sorry` for a theorem: a caller needs its type only)
is added there. When the scopes at the caller differ from the scopes at
`D`, that addition closes the caller's namespaces and sections, opens `D`'s
(with their `open`, `variable`, `universe`, `set_option`, `omit` and
`include` commands) in a `section`, and opens the caller's again
(`ReplCheck.bridge`). One request is one command.

At the end of the loop, one `lake build` of the changed modules confirms
the accepted forms; a failure stops the tool. Then the full check: `lake
build`, the config's lint command (the "after" list), and the config's
check command with `--base <head>` (`<head>` is the commit the run started
at). The report's `alias` field lists each finding: `fixed`, `form`,
`reason` (the last form's first error), `attempts` (every form and its
first error), `files_changed`.

## Configuration

`--config PATH` names a JSON file with four keys. A missing file or a
missing key is an error that stops the run; there are no default values.

| key | meaning | armada-lean's value |
|-----|---------|----------------------|
| `protectedPaths` | directory prefixes the tool never writes | `["ArmadaLean/Spec/", "ArmadaLean/Lint/"]` |
| `sourcePrefix` | the prefix of the target's own source tree: the file `<prefix>.lean` and the directory `<prefix>/` | `"ArmadaLean"` |
| `lintCommand` | the commands that run the target's lint, in order; the last command's standard output is the lint's JSON-lines findings and one JSON summary line | `[["lake", "build", "ArmadaLean.Lint.TypeDoctrine", "ArmadaLean.Lint.TypeDoctrineTest"], ["lake", "env", "lean", "scripts/type_lint.lean"]]` |
| `checkCommand` | the target's final check command; the tool appends `--base <head>` | `["bash", "scripts/check.sh", "--json"]` |

`examples/armada-lean.json` holds armada-lean's values.

## Build and run

```
lake build
.lake/build/bin/lean-temper --checkout /path/to/target-worktree --slot N \
  --config CONFIG.json --alias WORKLIST.json --repl REPL --report report.json
```

Tests: `lake build tests && .lake/build/bin/tests <target checkout> <repl>`
(the alias cases elaborate with `Init`; the REPL case runs `<repl>`, the
Lean REPL, with the checkout's `LEAN_PATH`).

## Files

- `Main.lean`: the driver. Steps: the base build and the config's lint
  command (the "before" list); the alias pass (`stepAlias`); the dependents
  in import order through the Lean REPL; one full check at the end.
- `LeanTemper/Edit.lean`: a byte-range text edit (`Edit`) and `applyEdits`.
- `LeanTemper/Proc.lean`: the process environment every `lake` and `lean`
  command runs with.
- `LeanTemper/Target.lean`: a module name from a file path, the target's
  `LEAN_PATH`, and the imports of one file from its header.
- `LeanTemper/Alias.lean`: the alias pass: the in-process elaboration, the
  declaration edits and the call-site edits from the info tree.
- `LeanTemper/Repl.lean`: the Lean REPL client (one JSON command per
  request). `LeanTemper/ReplCheck.lean`: the alias pass's check through it
  (sessions, scopes, the fresh-name check).
- `Tests.lean`: the alias cases (an implicit argument, a named argument,
  dot notation, a proof that names `v` and `hv`, the `generalize` form, the
  cast forms), and the REPL check (a caller in `D`'s scope and one in
  another scope; a right candidate, a wrong proof, wrong callers).
- `examples/armada-lean.json`: the config for armada-lean.

## Report

The lint summaries before and after, the finding lines removed and added
(the `example` field dropped: it is a nondeterministic representative), the
check command's `_ok` fields, the files changed, the timings of every
`lake` command, `stopped` and `stops`, and the `alias` field (one entry per
work-list finding: `fixed`, `form`, `reason`, `attempts`, `files_changed`).
