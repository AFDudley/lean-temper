# Handoff: lean-temper

Written 2026-11-22 by session `01a1f9a0`.

## What is to be done

1. **Steps 1 and 2 of `docs/design.md` §10, the weak form (§9.1).** File them on this repository's bus through the
   intake verb, with specs written by hand. The bus has no pebble yet. The R.1 inventory is
   `docs/labbook/2026-11-19-alias-inventory.md` (36 findings). The acceptance is §9: the run is done in the weak form,
   and a merge into armada-lean passes gates GRa, GRb and GRc of armada-laconic `docs/process.md`. Each spec's oracle
   runs a runner that this repository tracks and declares under `oracle_entrypoints` in `.exophial/config.yaml`. That
   runner does not exist. The gate image now has a built Lean REPL (`/opt/lean-repl`); it still has no armada-lean
   checkout (blocked, see State below).
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
- **The commit-boundary gate moved to a Nix flake** (`flake.nix`, `nix/gate.nix`, `nix/pins.nix`;
  `.exophial/config.yaml` `gate.image: flake`; docs/plans/nix-images.md Milestone 3, T3.x.a/T3.x.b). D10 parity
  measured: the Dockerfile gate and the flake gate gave the same verdict on the same tree. `.exophial/gate/Dockerfile`
  stays tracked, unused.
- **The gate image also carries the Lean REPL, built, at `/opt/lean-repl`** (`nix/repl.nix`, README.md "The gate
  image's acceptance-run paths"). Verified directly: given `{"cmd": "#eval 1 + 1"}` on stdin, with `lean` on PATH,
  it answers `"data": "2"`.
- **armada-lean, built, is NOT yet in the gate image.** It waits on armada-lean's own `lake-deps` flake output:
  armada-lean worktree `.scratch/nix-flake`, branch `nix-images/hooks-and-flake` (`e006b9d`), attribute
  `packages.x86_64-linux.lake-deps`. Not yet merged to armada-lean's `integrated` (`e2745b2`, no `flake.nix` there
  yet). Once merged, lean-temper's flake.nix takes armada-lean as a flake input pinned past that merge commit and
  imports `lake-deps` directly, rather than refetching or rebuilding Mathlib's own cache.
