# lean-temper: design

Status: proposal, 2026-11-18.

## 1. Overview

Lean projects that an AI writes often build and prove what they claim, but their structure
is poor. The same value appears under two names. A fact about a value travels beside the
value as a separate hypothesis, instead of inside its type. The same invariant is restated
in many theorems. Such a project is correct, but it is hard to read, hard to extend, and
hard to check against a specification.

lean-temper is a compiler that fixes this structure. Its input is a Lean project that
builds. Its output is the same project, rewritten into the form that a declared type
doctrine requires. The rewrite keeps the meaning of every statement. Lean checks every
edit before the tool keeps it. No person takes part in the rewrite.

The first user is armada-lean, the Lean model of the Armada privacy pool and the Nitro
state-channel protocol. The tool itself knows nothing about armada-lean. A configuration
file supplies the facts of each project.

This document is for a reader who knows Lean 4. It does not assume knowledge of compiler
design or of proof repair. Section 2 defines the terms that the rest of the document uses.

## 2. Terms

**Alias.** A variable that gives a second name to a value that other variables already
determine, together with an equation that records that fact. Example: a theorem takes
`c : Channel` and `hc : c = s.channel`. The value `c` adds no information, because
`s.channel` already fixes it.

**Refined type.** A type whose values carry a fact together with their data, so that a
value without the fact cannot exist. Example: `{o : List Entry // o.Nodup}` holds only lists
without duplicates. Lean writes such a type as a subtype or as a structure with a `Prop`
field.

**Boundary.** A declaration where data enters the model: an operation that creates a new
state, an initial state, or a constructor of a reachable state. A refined value is built at
a boundary. Everywhere else, statements receive it already built.

**Intermediate representation (IR).** The form of the program that the compiler works on.
For lean-temper, the IR has two linked layers for each declaration:

- the **Syntax** tree of its source command, as the Lean parser produced it. Each node keeps
  its source text, and the whitespace and comments around it (`SourceInfo.original`), so
  `Syntax.reprint` gives back the original text byte for byte;
- the elaborated **`Expr`** of its type and its value, which the kernel checks.

The info tree links each Syntax node to the `Expr` that Lean elaborated from it. The IR also
holds the dependency graph: for each declaration, the declarations that its type and its
value use.

**Pass.** One step of the compiler. A pass finds every instance of one pattern in the IR and
applies one rewrite to each instance.

**Postcondition.** A property that must hold after a pass. For lean-temper, the
postcondition of a pass is that its linter reports no finding.

**Change set.** A group of rewrites that the tool keeps or discards as one unit. A rewrite
replaces a Syntax node of a declaration with a new Syntax node, never a range of bytes. When
the signature of a declaration changes, the change set holds that declaration and every
declaration that calls it.

**Transport.** Moving a proof from one type to an equivalent type. If two types are
equivalent, every proof about one gives a proof about the other. Each lean-temper pass
replaces a type with an equivalent one, so each existing proof can be moved instead of
written again.

**Translation validation.** A way to make a compiler trustworthy without proving the
compiler correct: an independent checker checks each output. For lean-temper, Lean is the
checker. The tool keeps a change set only if Lean accepts it.

**Fixpoint.** The state in which running the passes again changes nothing. The tool repeats
its passes until it reaches this state.

## 3. Principles

**Every rewrite is an equivalence.** Each pass replaces a form with an equivalent form, and
the proofs move by transport. This is the method of PUMPKIN Pi, a proof-repair tool for Coq
(Ringer et al., PLDI 2021). Because the old and the new statement are equivalent, the
rewrite cannot change what the project proves.

**Lean is the judge.** The tool does not need to prove its own rewrites correct. Lean checks
each change set through its REPL (a Lean process that keeps its state between commands). At
the end of a run, a build of the changed modules checks the whole result.

**One rewrite per pattern, and no fallback.** A pass has exactly one rewrite for each
pattern. If Lean refuses the result, the declaration stays unchanged, the tool records the
reason, and the run ends with a failure. The tool never tries a second, weaker form. It never
retries a failed change a fixed number of times. It never substitutes a default value for a
missing fact.

**The linter decides when a pass is complete.** A pass is complete when its linter reports
no finding. If a finding remains, the run fails. The project's own gate then checks the
result independently. A linter can only enforce what it can see, so each pass's linter must
check the pass's actual goal. A linter that checks statements cannot show that a proof is free
of aliases. That needs its own rule, which inspects proof bodies (section 9).

**A pass covers every instance of its pattern.** A pass rule never says "where it can". If an
instance of the pattern exists that the pass does not rewrite, that is a defect in the pass:
the run reports the instance, with the tactic or construct involved and Lean's error, and
fails. An instance is never left in place as an accepted exception, and no adapter is left in
the merged result to hide it.

**The output is deterministic.** The same input always gives the same output. When the
doctrine leaves a choice open, for example the name of a new type, a fixed rule makes the
choice. If a rule gives a poor result, the rule is a defect of the tool, and the fix goes into
the tool. No person reviews the choices one by one.

**Parse at the boundary.** This principle comes from functional programming, where it is
known as "parse, don't validate" (King, 2019). A program should not carry a value next to a
separate check of that value. It should convert the value into a refined type once, where the
value enters, and pass the refined type from then on. For lean-temper, this means that a
refined value is built only at a boundary. Inside the model, statements take the refined
type, and no conversion is necessary. A conversion or a cast inside the model therefore
shows that a pass did not finish its work.

**Decide on `Expr`, write on Syntax, never on text.** A pass decides what an instance is, and
what the rewrite means, from the elaborated `Expr`, through the info tree. It writes the
rewrite as a change to the Syntax tree. The new source is the reprint of the changed tree, so
every part that the rewrite did not touch keeps its text, its whitespace and its comments.
The tool never computes a byte range, never inserts a string, and never guesses parentheses:
a new subterm is a Syntax node, and Lean's parenthesizer
(`Lean.PrettyPrinter.parenthesizeCommand`) adds parentheses where the precedence of the
surrounding node requires them. Input from outside the tool (the work list, the linter's
findings, the configuration) is parsed once into typed values, `Name`s and positions, and a
malformed input stops the run.

## 4. How the compiler works

A run has four stages.

1. **The front end** reads the project into the IR. It opens one REPL session per file and
   elaborates each file once. The REPL keeps the Lean environment after each command, so the
   tool can later check one changed declaration without checking the whole file again. The
   front end also builds the dependency graph: for each declaration, the declarations that its
   type and its proof use.

2. **The analyses** find the instances of each pattern (section 5), and they compute the
   boundary set from the boundary roots that the configuration names.

3. **The passes** rewrite the IR. They run in a fixed order. The whole sequence repeats until a
   fixpoint. Each change set is checked by Lean before the tool keeps it (section 6).

4. **The back end** writes the result back to the source files. For each declaration that a
   kept change set touched, it replaces the command's text with the reprint of the changed
   Syntax tree. Then the tool builds the changed modules, runs each pass's linter, and runs
   the project's gate. The run succeeds only if all of them succeed.

## 5. The passes

The passes run in this order: `alias`, `alias-proof`, `variant`, `refine`, `cleanup`.

### 5.1 `alias`: remove an alias from a statement

**Pattern.** A declaration takes a variable `v` and a hypothesis `hv : v = e`, where `e` is
built from other variables and does not mention `v`.

**Scope.** This pass removes the alias from statements, signatures and call sites. It does not
rewrite proofs. It carries each old proof across unchanged, with an adapter, and section 5.2
then removes every adapter. The output of this pass is therefore intermediate, in the way a
compiler's intermediate code is: Lean checks it, but it is never the merged result.

**Case 1: `hv` is unused in the proof.** (A `clear hv` counts as no use.) The pass deletes
`hv`, keeps `v` as an ordinary variable, deletes the `clear`, and at each call site deletes
only the argument for `hv`. The statement becomes more general, and the proof needs no change.

**Case 2: `hv` is used.** The pass replaces `v` with `e` in the statement and deletes `v` and
`hv` from the signature. Every parameter from the first one that mentions `v` onwards moves
after the colon, into the statement. The proof becomes a function that rebinds those
parameters in their original form, applied to `e` and `rfl`:

```lean
-- before
theorem queue_drains (state : State) (pending_list : List Op)
    (pending_is_default : pending_list = default_list state)
    (schedule : Schedule pending_list) (state_is_valid : Valid state) :
    Drains pending_list := by
  <old proof>

-- after this pass (intermediate)
theorem queue_drains (state : State) :
    ∀ (schedule : Schedule (default_list state)) (state_is_valid : Valid state),
      Drains (default_list state) :=
  (fun (pending_list : List Op) (pending_is_default : pending_list = default_list state)
       (schedule : Schedule pending_list) (state_is_valid : Valid state) =>
    show Drains pending_list by
      <old proof>) (default_list state) rfl
```

The old proof is then checked in exactly the local context, and against exactly the goal, in
which Lean first accepted it. The moved parameters must leave the signature: a parameter that
stays in the signature remains in the proof's local context as a hidden duplicate, and a tactic
that collects hypotheses by dependency (for example an induction that generalizes) then sees
both copies. A theorem's type is the same whether a parameter stands before or after the colon,
and named arguments still work in both forms (tested on Lean 4.35), so no caller changes.

**Call sites.** At each call to a changed declaration, the pass decides the form from the
elaborated application, before any check:

1. The caller's value for `v` is definitionally `e`: the pass deletes the arguments for `v`
   and `hv`.
2. The caller's value is a local variable that does not occur in `e`, and its equation is a
   local hypothesis: the call becomes `(by subst hv₀; exact T a h₁ …)`.
3. Otherwise: an explicit transport, `Eq.ndrec`, with a motive built from the declaration's
   original type.

Forms 2 and 3 are adapters. When the caller has the same alias in its own signature, the pass
removes the caller's alias in the same change set, so that the call needs form 1.

**Why the meaning stays the same.** A statement that holds for every `v` equal to `e` holds
exactly when it holds for `e` itself. In Lean: `(∀ v, v = e → P v) ↔ P e`. Applying the
rebinding function to `e` and `rfl` gives the new statement by substitution alone.

**Statements under specification.** When the declaration is an approved specification
statement, the pass also writes a proof that the new statement is equivalent to the old one,
has Lean check it, and then deletes the old statement.

### 5.2 `alias-proof`: remove every alias from every proof

**Pattern.** Inside a proof, a variable is tied to a value by an equation that exists only to
restore another context. The pattern includes every adapter that section 5.1 produces (the
rebinding function, the `subst` call form, the explicit transport) and every older form in the
project: `generalize name : value = variable`, a `suffices` that restates a statement with such
an equation, and `obtain name : variable = value`. After elaboration, all of them leave the same
shape in the proof term: a function over the variable and its equation, applied to the value
and to `rfl`, or a transport along such an equation.

**Rewrite: replacement, everywhere.** The pass replaces the variable with the value in the
proof, and removes each use of the equation by the rule for that kind of use. Examples: a
rewrite with the equation is deleted, because it rewrites nothing. A `clear` or a `subst` of
the equation is deleted. The variable is dropped from an induction's `generalizing` list. An
induction whose index was the variable generalizes the value itself at that point, with no
equation kept. The rule catalogue grows with each kind of use the project contains. After the
pass, the proof has no alias and no adapter, and reads as if it had been written over the value
from the start.

**Every instance, without exception.** For every alias, a proof with no alias exists: replace
the variable with the value and the equation with `rfl` in the proof term, and every transport
along `rfl` reduces away. Lean's kernel accepts this by substitution and reduction. The only
open question is how to write that proof back as source, which is engineering, not
possibility. So a proof that the pass does not rewrite is a defect in the pass (a missing rule),
reported with the tactic and Lean's error. The run fails. The pass never leaves the instance in
place.

**Why the meaning stays the same.** Applying a function to an argument and substituting the
argument into the function's body give the same result (beta reduction). A transport along
`rfl` reduces to its argument. Lean's kernel guarantees that both keep the type of the proof.

### 5.3 `variant`: reconcile different premises on one field

**Pattern.** Different statements put different conditions on the same field. Example: some
statements require `bp.treeNumber < N`, and others require `bp.treeNumber ≤ N`.

**Rewrite.** The pass orders the conditions by implication. It proves each implication with a
fixed decision procedure (`decide`, `omega` or `grind`). The strongest condition becomes the
refined type, and each weaker condition becomes a lemma that derives it. If the pass cannot
prove an implication, the group stays unchanged and the run fails.

### 5.4 `refine`: move facts into types

This pass does most of the work. It applies doctrine rules 1 and 2: a fact that a statement
assumes about its inputs belongs in the type of those inputs.

**Pattern, one input.** A declaration takes a variable `x` and a hypothesis `h : P x` that
mentions no other input.

**Pattern, several inputs.** Several declarations share the same group of hypotheses over the
same group of variables. Example: three theorems each take two channels `c₁ c₂` and the
hypothesis `c₁ ≠ c₂`.

**Finding the groups.** The pass uses formal concept analysis (Ganter and Wille, 1999), a
standard algorithm for finding shared structure. It treats each declaration as an object and
each hypothesis, written over its variables, as an attribute of that object. A *concept* is a
largest group of declarations together with the largest group of hypotheses that all of them
share. Each concept that covers two or more declarations is an invariant that the model
repeats, so it is a candidate for a type.

**Choosing among the groups.** Concepts can overlap. The pass chooses by a fixed rule: the
concept with the most hypotheses first, then the one with the most declarations, then the
first in source order. A concept whose hypotheses an already chosen concept covers is dropped.

**The type.** If an existing structure already has exactly these fields (Lean checks this by
definitional equality), the pass uses it. Otherwise it generates the type. One hypothesis on
one variable gives a subtype. Several give a structure with one field per variable and one
`Prop` field per hypothesis. The name comes from a fixed scheme: the shared namespace of the
declarations, then the names of the hypotheses' main constants. A name that already exists
gets a number.

**The API.** With each new type, the pass generates the operations that doctrine rule 5
requires: a coercion back to the data, a constructor that checks the hypotheses when they are
decidable, a lemma that extracts each hypothesis, and an equality lemma. Lean's proof
irrelevance makes two refined values with equal data equal, so the equality lemma needs no
extra proof.

**Rewrite.** In each declaration, the variables and their hypotheses become one input of the
refined type. The statement reads the data through the coercion. The proof starts by opening
the refined value into its parts, so that the old proof runs on the old names unchanged.

**Example.**

```lean
-- before: three theorems take this pair of inputs
theorem resolves (c₁ c₂ : Channel) (hne : c₁ ≠ c₂) … : …

-- after
structure DistinctChannels where
  first  : Channel
  second : Channel
  distinct : first ≠ second

theorem resolves (cs : DistinctChannels) … : … := by
  obtain ⟨c₁, c₂, hne⟩ := cs
  … -- the old proof, unchanged
```

**Call sites.** A caller that already holds the refined value passes it. A boundary builds it.
Any other caller is itself an instance of the same concept, so the pass rewrites it in the same
change set. If a caller is neither, the change set fails, and the declaration stays unchanged.

### 5.5 `cleanup`: delete what the passes replaced

The pass deletes every statement and helper lemma that a rewrite replaced. No deprecated copy
remains.

## 6. Change sets and their order

When a pass changes the signature of a declaration, every caller of that declaration must
change too. The tool puts the declaration and all its callers into one change set. Lean checks
the whole set through the REPL. The tool keeps all of it, or none of it.

The tool processes change sets in the order of the dependency graph: a declaration before the
declarations that use it. A caller therefore always sees the new form of what it calls.

Change sets that share no file and no caller are independent. The tool checks independent
change sets at the same time, one REPL session for each available Lean process slot.

## 7. Failure

The tool reports a failure in three ways, and it never hides one.

- A change set that Lean refuses leaves its declarations unchanged. The report names each
  declaration and the reason.
- A missing fact stops the run with an error. Examples: a declaration that the tool cannot
  find in its file, or a configuration key that is absent.
- The run exits with a failure if the build of the changed modules fails, if any linter still
  reports a finding, or if the project's gate fails. The tool reads the exit status of each
  of these commands.

## 8. Configuration

Each project supplies one JSON file. Every key is required. The tool has no default values.

| Key | Meaning |
|---|---|
| `sourcePrefix` | The directory of the model's source files. |
| `protectedPaths` | Paths that the tool never edits. |
| `boundaryRoots` | The declarations from which the tool derives the boundary set. |
| `lintCommand` | The commands that build and run the project's linters. |
| `checkCommand` | The project's gate. |
| `slots` | The Lean process slots that the tool may use. |

## 9. Acceptance

A step of the work is done only when the tool has run on the real project and Lean has
accepted the result. For armada-lean, each step must meet three conditions:

1. The tool runs on armada-lean, and Lean accepts every change set that the tool keeps.
2. The step's linter reports no finding for the instances in its scope.
3. The project's strict gate (`scripts/check.sh`) fails only on findings outside the step's
   scope, and no count is higher than before the step.

**Each merge into armada-lean meets the GATE of `armada-laconic/docs/process.md`.** Operator
ruling, 2026-11-19: where `process.md` and this document differ, `process.md` governs. Its
GATE says "Every step merges on its own". At each merge, no type-doctrine count rises
(`scripts/check.sh`, `lint_ok`), and the net line change of the model code is at most 0. So a
merge happens only at a point where the result has no adapter. The `alias` pass leaves
adapters (section 5.1), so its result merges only together with the `alias-proof` result for
the same findings. In lean-temper, the two passes are separate build steps. On armada-lean,
they are one merge. The strict gate passes only when the model has no finding at all, so the
strict gate itself merges after the last step (section 10).

**The gate must see inside proofs.** armada-lean's type-doctrine linter checks statements only.
Nothing in it inspects a proof body. So a proof that keeps an alias through an adapter (any form
listed in section 5.2) passes today's gate. Before step 2 is accepted, the linter gains a
proof-level rule that reports each such form. It works on the elaborated proof term, as the
statement rule does. With it, "no finding" means "no alias anywhere", which is the goal, and
an adapter cannot reach the merged result.

Tests on small Lean snippets help the developer of a pass. They run real Lean, with no mock,
but they do not make a step done. When a developer tests one change on the model, the work list
holds only the instances that the change must fix.

### 9.1 The two forms of "done" (operator ruling, 2026-11-20)

A model has two kinds of statement. A **specification statement** says what the system must
do. In armada-lean it has a record under `ArmadaLean/Spec/`, and `#check_spec_bindings` binds
its theorem to that record (armada-lean `docs/spec-module-design.md`). A **helper** is every
other theorem. A helper exists only to prove the specification statements.

**The weak form.** A run is done in the weak form when all four conditions hold:

1. No file under a protected path changes, and `#check_spec_bindings` passes.
2. The run changes only `theorem` declarations. It changes no `def`, `structure`, `inductive`
   or `abbrev`. The tool checks this with a diff of declaration kinds.
3. The whole model builds, and the project's gate runs on the whole model.
4. The step's linter reports no finding in its scope, the proof-level rule reports no adapter,
   and the merge meets the GATE above.

Conditions 1 and 2 keep every specification statement and every definition unchanged. So the
weak form needs no equivalence proof for a specification statement, and no analysis of which
definitions the specification uses. The rule of section 3 stays in force for every rewrite.

**The strong form.** A run is done in the strong form when one run on the whole model gives
one verdict:

1. Every specification statement is unchanged, or the run changed it and Lean checked a proof
   that the old and the new statement are equivalent.
2. Every definition in the **protected set** is unchanged, or changed with such a proof. The
   protected set is every definition that a specification statement reaches in the dependency
   graph.
3. Every helper builds. The tool may replace a helper's statement with any statement. A helper
   needs no equivalence proof. This relaxes the rule of section 3 for helpers only.
4. The linters report nothing, and no adapter remains.

The strong form needs three parts that do not exist yet: the computation of the protected set,
a configuration mode that accepts a change under a protected path together with its
equivalence proof, and the acceptance run on the whole model.

## 10. Build plan

**Roadmap (operator ruling, 2026-11-20).** The work has three phases, in this order:

1. **The weak form** (section 9.1). It covers steps 1 and 2. It covers step 6 if `variant`
   changes theorems only. All 26 of the alias findings' declarations that a text search
   resolved are `theorem` declarations; the inventory script must confirm the kind of all 27.
2. **The strong form** (section 9.1). Its three missing parts come first. Then steps 3, 4 and
   5 run under it: step 3 changes specification statements, and steps 4 and 5 change state
   types.
3. **A second project: `FlashProve/lean`.** The analysis passes run there with a new
   configuration and no change to the tool's code. The output is a list of candidate types.
   Known obstacles: the linters are in `ArmadaLean/Lint/` and must move into the tool;
   `FlashProve/lean` has no `Spec/` convention, so the configuration must take a list of root
   theorems; `FlashProve/lean` pins Lean v4.29.1 and the tool pins v4.35.0.

The purpose of the tool is wider than the type-doctrine findings. A model in the tool's normal
form is the input of the generators (Solidity, and the shared application code). The types
that the analysis passes find are the vocabulary of a declared form for new work. An analysis
that finds a shared pattern in definition bodies (for example `if h : Pre then some (Effect
⟨_, h⟩) else none` in `Pool.apply` and `Adjudicator.apply`) is not built and not scheduled.

| Step | Content | Instances on armada-lean `integrated` (`ab5b476`) |
|---|---|---|
| 1 | The pass manager: the two-layer IR (Syntax and `Expr`), the dependency graph, change sets of Syntax rewrites, the reprint back end, typed input, the fixpoint, the failure rules of section 7. The alias pass of section 5.1: statements, signatures and call sites, with the old proofs carried across by adapters. | 36 internal findings at armada-lean `9c6ef1b` (the acceptance set) |
| 2 | `alias-proof` (section 5.2): every alias and every adapter removed from every proof, by replacement. The proof-level linter rule of section 9. | Every adapter from step 1, plus 10 restated statements and 8 `generalize` aliases already in the model |
| 3 | `alias` on specification statements, with the equivalence proofs | 17 findings |
| 4 | The boundary analysis of section 4: the boundary set, derived from the configuration's `boundaryRoots` (section 8). `refine` for one input (section 5.4), which builds each refined value at a boundary. | 217 hypotheses on one input, and 25 one-variable groups |
| 5 | Formal concept analysis, and `refine` for several inputs | 197 groups |
| 6 | `variant` | 9 groups |

The formal concept analysis is a self-contained algorithm, and its development can start at
any time. The other steps share the types of the pass manager, so step 1 defines those types
first. After that, steps 2, 3, 4 and 6 can be developed at the same time. Runs on the model
happen in the fixed pass order, because the passes edit the same files.

**Steps 1 and 2 have one merge.** Between 2026-11-18 and 2026-11-19, the proof-rewriting work
that belongs to step 2 was put into step 1, and step 1's acceptance counted how many proofs
survived it. See `docs/labbook/2026-11-19-alias-transport-and-step-split.md`. During
development, step 1 is measured by statements: each finding's alias is gone from the statement
and the signature, and Lean accepts the change set. Step 1's adapters add lines, so its result
does not merge alone. Step 2 is measured by proofs: the proof-level rule reports nothing. The
merge into armada-lean takes the result of both steps for the same findings, and it meets the
GATE of section 9: no type-doctrine count rises, the net line change of the model code is at
most 0, and no adapter remains. Steps 3 to 6 each merge on their own, under the same GATE.

**The strict gate of armada-lean waits for the last step.** It fails on any finding, so it
can merge only when the steps above bring armada-lean to zero findings. Until then, each step
measures with the current gate (`scripts/check.sh --base`). The port of that gate to Lean is
parked on armada-lean branch `gate/lean-port` (`f489d01`, worktree `.scratch/gate-lean`). It
gives the same `--json` and `--base` results as the Python gate at `ab5b476`, apart from the
intended strict difference. It is not acceptable yet, for four reasons:

- **Speed.** The decision-scope check starts one `lake env lean` process per model file, so the
  gate takes 12–20 minutes instead of 1–2. The fix is to run the `DecisionScope` linter inside
  the normal `lake build`. A command linter runs only in a compile whose import closure holds
  the linter's module, so a package option alone does nothing. Each model module's own compile
  must therefore load `ArmadaLean.Lint.DecisionScope`. An import in the root `ArmadaLean.lean` is
  not enough: the root imports the model modules, and they do not import the root. Two
  mechanisms remain. A base module that every model file already imports can import the linter.
  Or Lake's `plugins` option can load the compiled linter into each `lean` process, so that its
  `initialize` registers the linter with no edit to a model file (to be verified on Lake 4.35).
  Each compile then records its findings in its `.olean` (`Linter.recordLints`,
  `Lean/Elab/Frontend.lean:388`). The gate reads them with `Linter.getAllLints` and elaborates
  nothing again. Elaborating the files again inside the gate's own environment is wrong: that
  environment already holds their declarations. The acceptance limit is that, on a warm tree,
  the port is no slower than the Python gate.
- **Scan count.** The port reports 902 scanned files, but the model has 93.
- **Unverified claims.** The port claims that a large `unsafe def main` links to the wrong
  entry point, and it turned off `enableArtifactCache` for the whole package. Both need a
  minimal reproduction with the cache on and off. Without one, both changes are reverted.
- **Acceptance not run.** The theorem runs, the build-error comparison,
  `lake build && scripts/check.sh`, and `test_check_gate.lean` are not run.

## 11. Differences from the current tool

The current tool has one pass (`alias`), it writes on the wrong layer, and it has several
fallbacks. The design removes each of these defects:

- It no longer edits text. Today the alias pass decides on the info tree correctly, but it
  writes byte-range deletions, inserts the right-hand side as a string, and guesses
  parentheses (`atomic`). Its input is strings (`Finding`, with `at` split on `:`).
- When the tool cannot rewrite a proof directly, it no longer tries `generalize` instead.
  The alias pass uses one adapter form per case, decided in advance, and the `alias-proof`
  pass removes every adapter.
- When a caller does not fit the changed declaration, it no longer tries a series of casts
  until one works. The call-site form is decided in advance from the elaborated call, and a
  caller with the same alias is rewritten in the same change set.
- It no longer retries failed declarations a fixed second time. It repeats all passes until
  nothing changes.
- It reads the exit status of the project's gate, and a failed gate fails the run.
- When it cannot find a declaration in its file, it stops with an error. It no longer checks
  the edit against the start of the file.
- It checks every changed file through the REPL, and skips none.

## 12. References

- Ringer, Porter, Yazdani, Leo, Grossman. *Proof Repair across Type Equivalences.* PLDI 2021.
- Ganter, Wille. *Formal Concept Analysis: Mathematical Foundations.* Springer, 1999.
- King. *Parse, don't validate.* 2019.
- Christiansen. *Functional Programming in Lean*: the sections on subtypes and on the pitfalls
  of programming with dependent types.
- Mathlib, `Finset`: a list-like value bundled with the fact that it has no duplicates.
- LLVM `opt` and the MLIR canonicalization pass: compilers built from passes, fixpoints and
  postconditions.
