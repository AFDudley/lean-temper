# Inventory of the 36 alias findings (armada-lean `9c6ef1b`)

This is the R.1 inventory (`armada-laconic/docs/process.md`, "Measure the gap before changing
anything") for build steps 1 and 2 of `../design.md` section 10.

Checked in Lean: `2026-11-19-alias-inventory.lean` imports `ArmadaLean` at `9c6ef1b` and reads
each finding from the elaborated declaration (its type's parameters, and the proof term with
those parameters applied). Its `main` runs in an armada-lean checkout at `9c6ef1b`, for example
with `lake env lean --run`. Output: `2026-11-19-alias-inventory-lean.txt`, one line per finding.
Run time 41 s, peak 4.2 GB. A first draft read the source text, not the elaborated
declarations. It was wrong in two places (below), and it is not kept.

## Classes

| Class | Shape | Count | Findings |
|---|---|---|---|
| A | The proof term does not use the equation | 6 | `t = net.chain.now` in `consensus_checkpoint_resolves`, `consensus_round_safe`, `round_keeps_status`, `latest_round_keeps_status_two`, `late_round_keeps_status`, `directly_funded_round` |
| B | Named equation; the value uses only parameters bound before the variable | 10 | `consensus_round_safe` Ω1, `withPositionsFrom_leaf_matches` start, `consensus_round_safe_core` Ω1, `concludeRound` Ω, `round_keeps_status` Ω, `withTreePositionsFrom_leaf_matches` start, `consensus_round_safe_nil` Ω1, `conclude_round_finalized` Ω, `insertLeaves_leavesAt_new_matches` tn, `conclude_strategy` Ω |
| C | The equation is an unnamed premise after the colon | 6 | `virtualTurnBound_mem` c, `exists_topo_list` n, `turboValueAlong_eq_add_credits_aux` order, `turboValues_order_indep` n, `mirror_land` sx and sy |
| D | Named equation; the value uses parameters bound **after** the variable | 14 | `latest_state_finalizable_two` c1 and c2, `consensus_checkpoint_resolves` c, `Adjudicator.dest_mem_requiredNodes` m, `before_remove_mid` l, `concludeRound` sent0, `recordStep_preserves_consistency` c, `latest_round_keeps_status_two` c1 and c2, `latest_round_keeps_status_two_ordered` c1 and c2, `late_round_keeps_status` c, `land_own_challenge_transitions_status` c, `not_edge_of_before_split` l |

Further facts from Lean:

- **15 of the 36 variables are implicit parameters**, so call sites never write them. Every
  class B and D finding in the `Ω` and channel groups is implicit.
- **Equation direction:** 26 findings state `value = variable`, and 10 state
  `variable = value`.
- **Class A is exact:** in all 6, the proof term never mentions the equation. In
  `directly_funded_round` the text shows `ht` in the proof, but that is a different hypothesis
  that reuses the name.
- **Class C is exactly the old tool's 5 losses** (6 findings): every equation there is
  unnamed and stands after the colon. Two of them, `exists_topo_list` and
  `turboValues_order_indep`, induct on the variable itself (`n` is the length of a list).
- **Named arguments:** a text search found 2 candidate uses of an alias variable by name. Both
  are false: the two calls (`Liveness.lean:1509` and `1550`) name `net1` and `net'`, not `c`. No
  caller passes an alias variable by name.

## Corrections to the text draft

1. The draft put 23 findings in "the value uses only earlier parameters". Lean shows that 14 of
   them use **later** parameters. Example: `latest_state_finalizable_two` declares `c1` as
   parameter 9, but its value `ss1.state.channel` uses `ss1`, declared later, and 6 parameters
   mention `c1`. Removing `c1` therefore needs every parameter that mentions it moved after
   `ss1`. Reordering is the common case (class D, 14), not a rare one.
2. The draft found only one implicit variable. Lean shows 15.

## Calls between the 26 declarations

| Group | Same alias passed down? |
|---|---|
| `latest_state_finalizable_two` → `latest_round_keeps_status_two` → `latest_round_keeps_status_two_ordered` → `land_own_challenge_transitions_status` | yes: the channel of `ss1`/`ss2` (or `ss`) at every level |
| `consensus_round_safe` → `consensus_round_safe_core`, `consensus_round_safe_nil`; `nil` → `core` | yes: `Ω1 = ss.state.outcome` |
| `conclude_round_finalized` → `round_keeps_status` | yes: `Ω = ss.state.outcome` |
| `conclude_strategy` → `concludeRound` | yes: `Ω = ss.state.outcome` |
| `withTreePositionsFrom_leaf_matches` → `withPositionsFrom_leaf_matches` | yes: `start = base.length` |
| `turboValues_order_indep` → `before_remove_mid`, `not_edge_of_before_split` | no |

10 of the 26 declarations call no other declaration in the list.

## Rules this requires

1. **One change set per call group** (5 groups that pass the same alias down). Every call then
   passes the value itself, and no call-site adapter is needed.
2. **Class A:** delete the equation, keep the variable, delete the `clear`. Callers drop one
   argument.
3. **Class B:** delete the variable and the equation, substitute the value.
4. **Class D:** before substituting, move every parameter that mentions the variable after the
   last parameter that the value uses. The theorem's meaning does not change: only independent
   parameters change order. Callers that pass arguments by position must follow the same order.
5. **Class C:** treat the premises after the colon as parameters. Remove the premise from the
   statement's chain, and remove the matching name from the proof's `intro`.
6. **Implicit variables:** call sites delete only the equation's argument.
7. **Proofs (step 1):** the rebinding function, with the moved parameters after the colon.
8. **Proofs (step 2):** replacement. The two inductions on a list's length (`exists_topo_list`,
   `turboValues_order_indep`) need an induction on the list's length with no equation.
