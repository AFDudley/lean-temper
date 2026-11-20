# Glossary

One word means one concept. The code, the documents and the reports of lean-temper use these words and no
synonyms. A new term enters here before it enters a document or the code (armada-laconic `docs/process.md`, Judgment
J0). Each row cites its source.

## The tool

- **Pass** (n) — one step of the compiler. A pass finds every instance of one pattern in the IR and applies one
  rewrite to each instance (`docs/design.md` §5).
- **Intermediate representation (IR)** (n) — the form of the program that the compiler works on. For each declaration
  it has two linked layers: the **Syntax** tree of its source command, with its source text, whitespace and comments
  (`SourceInfo.original`), so that `Syntax.reprint` gives back the original text byte for byte; and the elaborated
  **`Expr`** of its type and its value, which the kernel checks. The info tree links each Syntax node to the `Expr`
  that Lean elaborated from it. The IR also holds the dependency graph: for each declaration, the declarations that
  its type and its value use (`docs/design.md` §4).
- **Change set** (n) — a group of rewrites that the tool keeps or discards as one unit. A rewrite replaces a Syntax
  node of a declaration with a new Syntax node, never a range of bytes. When the signature of a declaration changes,
  the change set holds that declaration and every declaration that calls it (`docs/design.md` §6).
- **Postcondition** (n) — a property that must hold after a pass: its linter reports no finding (`docs/design.md` §3).
- **Fixpoint** (n) — the state in which running the passes again changes nothing. The tool repeats its passes until
  it reaches this state (`docs/design.md` §4).
- **Transport** (n) — moving a proof from one type to an equivalent type. Each pass replaces a type with an
  equivalent one, so each existing proof can be moved instead of written again [Ringer et al., PLDI 2021].
- **Translation validation** (n) — a way to make a compiler trustworthy without proving the compiler correct: an
  independent checker checks each output. For lean-temper, Lean is the checker, and the tool keeps a change set only
  if Lean accepts it [Pnueli, Siegel and Singerman 1998].
- **Adapter** (n) — a term in a proof that restores an old context for an old proof: a function over a variable and
  its equation applied to a value and `rfl`, a `subst` at a call site, or a transport along such an equation
  (`docs/design.md` §5.1, §5.2). No adapter stays in a merged result.

## What the tool finds

- **Finding** (n) — one report of a linter: one instance of one pattern at one declaration.
- **Linter** (n) — a program that reports the findings of one pattern. The linters of armada-lean are in
  `ArmadaLean/Lint/` (`docs/design.md` §10, roadmap phase 3).
- **Proof-level rule** (n) — the linter rule that reads the elaborated proof term and reports each adapter and each
  alias inside a proof (`docs/design.md` §9).
- **Alias** (n) — a variable that gives a second name to a value that other variables already determine, together
  with an equation that records that fact. Example: a theorem takes `c : Channel` and `hc : c = s.channel`. The value
  `c` adds no information, because `s.channel` already fixes it (`docs/design.md` §5.1).
- **Refined type** (n) — a type whose values carry a fact together with their data, so that a value without the fact
  cannot exist. Example: `{o : List Entry // o.Nodup}` holds only lists without duplicates. Lean writes such a type as
  a subtype or as a structure with a `Prop` field (`docs/design.md` §5.4).
- **Boundary** (n) — a declaration where data enters the model: an operation that creates a new state, an initial
  state, or a constructor of a reachable state. A refined value is built at a boundary. Everywhere else, statements
  receive it already built (`docs/design.md` §4).
- **Inventory** (n) — the list of the instances that a pass must rewrite, made by a Lean script from the linter's work
  list before the pass is built (armada-laconic `docs/process.md` R.1;
  `docs/labbook/2026-11-19-alias-inventory.md`).

## What the tool must keep

- **Specification statement** (n) — a statement that says what the system must do. In armada-lean it has a record
  under `ArmadaLean/Spec/`, and `#check_spec_bindings` binds its theorem to that record (`docs/design.md` §9.1).
- **Helper** (n) — every theorem that is not a specification statement. A helper exists only to prove the
  specification statements (`docs/design.md` §9.1).
- **Protected set** (n) — every definition that a specification statement reaches in the dependency graph
  (`docs/design.md` §9.1).
- **Weak form** (n) — a run that changes only theorems, and no specification statement and no definition
  (`docs/design.md` §9.1).
- **Strong form** (n) — one run on the whole model with one verdict. It changes a specification statement or a
  definition of the protected set only with a proof, checked by Lean, that the old and the new form are equivalent
  (`docs/design.md` §9.1).

## Checks

- **Gate** (n) — one check that runs, with an id, a kind (static, mutation or execution), the stratum it grades and
  the inputs it reads. A decision that a person or an agent makes is a judgment, not a gate. The full run of a
  repository's checks has no name: `.exophial/config.yaml` `gate.command` is the command that runs them, not a gate.
  Not a verb (armada-laconic `glossary.md`, "Gate").
- **Judgment** (n) — a decision that a person or an agent makes and that no machine checks again (armada-laconic
  `glossary.md`, "Judgment").
