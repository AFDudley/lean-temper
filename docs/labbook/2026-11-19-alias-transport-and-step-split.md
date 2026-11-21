# 2026-11-19: alias transport, and why the proof work belongs in step 2

A lab book entry. It records the work on build step 1 between 2026-11-18 and 2026-11-19, what
the measurements showed, the decisions the operator made, and the error in how the work was
divided between step 1 and step 2. The corrected design is in `../design.md` (sections 3, 5.1,
5.2, 9 and 10).

## The benchmark

Every run used armada-lean at `9c6ef1b` and the work list
`armada-lean/.scratch/alias-internal-36.json`: 36 `aliasHypothesis` findings in 26 declarations.
These findings are already fixed on armada-lean `ab5b476`, by the old tool with help from
workers. So the runs measured the tool, not remaining work on the model.

| Run | Tool | Wall time | Result |
|---|---|---|---|
| Baseline | Old tool, `integrated` `e64442f` | 98 min 23 s | 30 of 36 findings fixed |
| `2493d579` | Substitution into the proof text | 37 min 03 s | 1 of 36 |
| `2099e37d` | Plus position rules for the equation | — | 1 of 36 |
| `d430ed31` | Rebinding function for proofs | — | 2 of 26 declarations, 3 lines removed |
| `19658fa` | Plus the explicit transport at call sites | — | 5 of 26 declarations, 64 lines added (report not kept) |
| `94edba8f` run 1 | Plus the `subst` call-site form | 53 min 27 s, 21.9 GB peak | 5 of 26 declarations, 11 lines added |

## What the old tool's fallbacks were

The old tool tried a sequence of forms for each declaration and kept the first one that Lean
accepted: a plain rewrite, then a `generalize` preamble, then a `suffices` restatement, then a
chain of casts at each call site, then a fixed second pass over the failures. Lean checked each
candidate, so the output was correct. The fallbacks did not buy correctness. They bought
coverage by search. The second pass worked as a crude dependency order, and the casts worked as
call-site transports found by trial. The search was slower than one constructed form per case
(98 min against 37 min), because each rejected form cost a REPL check.

## The transport forms that were compared

The old proof proves the statement for every value of the variable, given the equation. The new
statement is about the value. Four ways exist to carry the old proof across:

1. **Substitute in the proof text.** Correct only if every tactic still works with the value in
   place of the variable. Tactic proofs name the variable in too many ways, and this fixed 1 of
   36.
2. **`generalize` before the old proof.** Rebuilds a context like the original one. It replaces
   every occurrence of the value, including occurrences that were the value in the original and
   not the variable, so the context can differ from the original.
3. **A rebinding function.** The old proof runs inside a function that binds the variable, the
   equation and the later hypotheses in their original form, applied to the value and to
   `rfl`. The operator chose this form.
4. **Substitute in the elaborated proof term.** Correct by construction, but the term of a
   tactic proof is large, and writing it back loses the source.

## Defects found along the way

- **Duplicate hypotheses.** With the rebinding function, a hypothesis that mentions the
  variable stayed in the theorem's signature and was also rebound by the function. Both copies
  were in the proof's local context. A tactic that collects hypotheses by dependency, such as an
  induction that generalizes, carried both, and the induction hypothesis then expected an extra
  argument. Example: `withPositionsFrom_leaf_matches`. The fix moves every parameter from the
  first rebound one onwards after the colon. A test on Lean 4.35 showed that the theorem's type
  is identical in both forms, and that callers which pass those parameters by name still
  compile.
- **Call sites inside rebound proofs.** Inside the rebinding function, the variable exists
  again, so every call from the old proof to another changed declaration passes arguments typed
  over the variable. Those calls need a transport. Most of the 26 declarations call each other,
  so the transports multiplied, and the model grew.
- **A dropped trailing argument.** A call that supplies more arguments than the callee's named
  parameters (they fill arrows in its conclusion) lost them when rewritten. Fixed in `94edba8f`.
- **The wrong REPL.** The unit tests used a REPL built for Lean 4.33.1. The correct one is
  `repl-v4350`.

## The error: proof work in step 1

The design has two alias passes: `alias` (step 1) for statements, and `alias-proof` (step 2)
for proofs. Each time the question was how proofs should be repaired, the answer went into
step 1: the induction rule, the rebinding function, three call-site forms, and finally a
proposal to move all proof replacement into step 1. Step 1's acceptance therefore measured
proof rewriting, which is step 2's hard problem, and its numbers (1, 2 and 5 of 26) measured the
wrong thing. Many worker-hours went into adapters that only step 2 can remove.

## The hedge, and the missing check

Section 5.2 said that `alias-proof` removes aliases "where it can rewrite the proof without
them". That phrase covers every case, because for every alias a proof with no alias exists: put
the value in for the variable and `rfl` in for the equation, and every transport along `rfl`
reduces away. The only open question is how to write that proof back as source, which is a
matter of effort, not possibility. The phrase gave an agent permission to stop at a hard proof
and leave an adapter.

Nothing would have caught that. armada-lean's type-doctrine linter checks statements only, so a
proof that keeps its alias through any adapter passes the strict gate at zero findings. The
counts of 10 restated statements and 8 `generalize` aliases in the build plan came from a manual
search, not from the linter.

## Decisions

- Step 1 removes aliases from statements, signatures and call sites, and carries proofs across
  with adapters. Its output is intermediate.
- Step 2 removes every alias and every adapter from every proof, by replacement, with one rule
  per kind of use. A proof it does not rewrite is a defect in the pass, and the run fails.
- The type-doctrine linter gains a proof-level rule, so that the gate checks the goal: no alias
  anywhere in the merged result.
- No pass rule says "where it can".
