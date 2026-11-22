# Handoff: lean-temper

Written 2026-11-22 by session `01a1f9a0`.

## What is to be done

1. **Steps 1 and 2 of `docs/design.md` §10, the weak form (§9.1).** File them on this repository's bus through the
   intake verb, with specs written by hand. The bus has no pebble yet. The R.1 inventory is
   `docs/labbook/2026-11-19-alias-inventory.md` (36 findings). The acceptance is §9: the run is done in the weak form,
   and a merge into armada-lean passes gates GRa, GRb and GRc of armada-laconic `docs/process.md`. Each spec's oracle
   runs a runner that this repository tracks and declares under `oracle_entrypoints` in `.exophial/config.yaml`. That
   runner does not exist: the gate image has no armada-lean checkout and no REPL (`.exophial/gate/gate.sh` lines 7–9).
2. **Three rehearsals from 2026-11-19 are stale** (`.exophial/cache/dry-run/6b0d7cc3…`, `0bf91916…`, `e7e67258…`).
   Rehearse their reports again with item 1. Their subjects: no detector for an alias inside a proof term (step 2), no
   analysis that computes the boundary set (step 4), no proof that a rewritten specification statement is equivalent
   to the old one (step 3).

## State

- `integrated` is on GitHub, and armada-laconic-mono's `lean-temper/` equals it (subtree sync of 2026-11-22).
- Parked branches: `step1/pass-manager` (worktree `.scratch/step1`) and `concepts/fca` (worktree `.scratch/concepts`,
  222 of 222 `repeatedPremise` groups matched, `1b9e31a`).
- The last full run of the old alias pass: `.scratch/verify/report-run1.json`.
- `.scratch/filing/` and the other files in `.exophial/cache/dry-run/` came from a session that wrote them without
  agreement. Nothing depends on them, and they can be deleted.
