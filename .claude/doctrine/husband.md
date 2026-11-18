# Husband doctrine

A HUSBAND drives one work item to MERGED, alongside a running reducer.

It is not a worker and not the coordinator. A worker does one pebble inside one
worktree and hands off. The coordinator decomposes and dispatches. A husband
takes a family that is stuck, and stays with it until every pebble is closed or
parked with a recorded cause, and the feature is readable in the tree.

Use a husband when a family has stalled: pebbles that will not drain, branches
that will not merge, or a decomposition that produced more records than work.

## Own a family exclusively, by root and by branch namespace

Name what the husband owns before it starts: the pebble root, its descendants,
and the branches named for them. Name what it does not own, and who does.

Overlapping husbands edit the same files. Disjoint husbands never need to agree
about anything. Ownership is the only coordination that scales.

## Contention is the throttle — do not remove it

The integration lock has one holder. Two husbands competing for it keep the
queue full while bounding the tokens spent per second, because each blocks
rather than starting more work.

Do NOT tell husbands to negotiate before integrating. The lock already
serialises them correctly, and a negotiation round trip only lowers throughput.
Two at a time is the working number.

## Every wait names its signal and its bound

A husband catches exophial's failures. That is the job. A husband that waits on
a step it cannot see failing has stopped doing the job. On 2026-11-03 and
2026-11-04, five husbands waited 5 to 19 hours each on steps that had already
failed.

Before every wait, write in the log the signal that ends it and the bound. When
the bound passes without the signal, diagnose at once and change the
precondition. Never wait a second time on the same step unchanged.

| Step | Signal | Bound (measured 2026-11-02 to 2026-11-05) | At the bound |
|---|---|---|---|
| reducer after a dispatch or a collision retry | a dispatch, gate or merge line for your pebble in `.exophial/logs/dispatcher.log` | 15 minutes | A reducer that logs only `N ready pebble(s)`, with no worker and no gate container, is stuck (exo-607). Run `exophial stop` (the stop rule below) and dispatch again. |
| worker after its spawn | a commit in the worker's worktree, or growth of its session transcript | 20 minutes | Read the container's processes (`podman top`) and its transcript. A worker with no process doing work is stalled. |
| gate run | a `gate-verdict:` comment on the pebble | 30 minutes | Read the gate log and the gate container. |
| your own background command | its exit | the bound of the step it runs | Read what it is blocked on. |

## The gate runs the installed wheel, not the branch

The integrator grades a branch with the INSTALLED exophial, not with the code on
the branch. A fix to exophial's own gate or oracle code takes effect only after
the installed wheel contains it.

Each `gate-verdict:` comment ends with the installed version
(`... failed 0.2.1+<sha>`). Before you trust a gate result after a fix to
exophial, check that `<sha>` contains the fix:

    git merge-base --is-ancestor <fix-sha> <sha>

If it does not, install first (`exophial self-update`, when no worker runs),
then dispatch again. On 2026-11-05 a husband read two failures of a fixed stdin
defect as "a second, unlocated code path". Both gate runs used a wheel without
the fix.

## A wheel install kills in-flight workers

Until exo-3745d merges, any `exophial self-update` or `exophial dispatch`
preflight install sends SIGTERM to the running reducer, and the reducer ends its
workers. Compare the `stop requested (signal 15)` time in the dispatcher log
with the install time (the mtime of the installed `exophial/__init__.py`). If
they match, the install killed the worker: unpark with a comment that names the
install time, and dispatch again. Do not install while a worker runs.

## Verify every merge by reading the tree

An integrate's own output is a claim. `git ls-tree`, or read the file, or import
the module. Report the sha you verified, not the sha the command printed.

`completed` from a subagent means it yielded, not that its artifact is good.

## A refused integrate names no failing hook — go and get it

The gate-rejection arm prints a verdict and often nothing else. Recover the
cause by running the gate yourself against the preserved tree:

    pre-commit run --all-files --hook-stage manual

Then read the failing hook. Two merges on 2026-08-11 were unblocked exactly this
way, and each time the answer was one test.

## Re-measure before acting

Divergence counts, ahead/behind numbers and lane membership go stale in minutes
while other husbands and the daemon merge. Treat every figure in your brief as a
hypothesis with a timestamp.

## Prefer merging existing work over re-authoring it

Look for the work before writing it: `wip/` branches, worker worktrees, epic
lanes, and the pebble's own history. A finished, gate-green fix stranded behind
an unrelated sibling is the common case, not the exception.

## Decomposition siblings are not dependency-ordered — watch for overlap

A decomposition's children merge on `epic/<root>` in declared order, but their
DISPATCH is unordered: decomposition does not add dependencies between
siblings, so their workers run in parallel from the same base. A sibling that
needs an earlier sibling's artifact authors its own copy, and its lane merging
then fails as an add/add conflict that neither resolution tier settles. On
2026-10-03, exo-d1f4.2 re-authored exo-d1f4.1's `src/exophial/handoff_cost.py`
and parked as `conflict_unresolved`.

This is an accepted limitation (wontfix). Do not file it. Watch a decomposed
family for siblings that create the same file. When it bites, work in the
parked sibling's own worktree: rebase onto `epic/<root>`, keep the
already-merged sibling's version of the shared files, re-run that sibling's
oracles and the gate, and point its handoff's `commits` at the rebased shas.
Then unpark it and dispatch the root; reconcile routes the completed handoff
straight to INTEGRATE.

## A repair that cannot succeed must not be retried

If a repair branch's precondition can never be satisfied, it re-fires every pass
forever. On 2026-08-10 a wheel-drift repair restarted the dispatcher twice in six
minutes, killing every in-flight worker and reporting `workers 0/8` after each.

Waiting is the correct action when the repair cannot work. Say what would let it
work, and stop.

## Unpark, then restart — an unpark alone is a no-op

A pebble that parked inside the current reducer process holds its claim-lease
file descriptor until that process exits. Re-admitting it changes nothing until
the lease is released, so batch the unparks and let the restart make them
claimable.

## A park triggers a subagent that drives the pebble to MERGED

The husband system exists to get the commit MERGED. That is the terminal
goal. Doctrine is followed as far as it goes, but a clean review handoff is
not the win condition. A merged commit is the win condition.

A park is not a stop signal. A park is not a retry signal. A park is the
trigger for the husband to dispatch a subagent.

The subagent diagnoses the parked cause and authors the fix. It then drives
the pebble to MERGED through existing exophial machinery:
`exophial apply` for a change that qualifies, `exophial integrate --branch
<name>` for a branch, or a fresh rehearsal
(`exophial intake` then `exophial intake --execute <id>`, Law L4,
`docs/merge_plan.md` Stage MLAW) when the derivation itself must run again.

**Never edit a claimed spec.** A spec that is found wrong is never patched
under a claim (`docs/merge_plan.md`, "The rule for a wrong spec"). No subagent
edits
`contracts/specs/derived-<id>.spec.json`, not even to narrow one clause. Close
the pebble as "spec found wrong" with the evidence, and file a new pebble
through `exophial intake` with that evidence; it gets a new spec, a new claim
and a new base. A worker commit that holds a correct fix stays on its branch,
and the new pebble names it.

Law L4 in `docs/merge_plan.md` removed `specify` and `specify --refresh`.
The only route to a new spec is a fresh rehearsal: close the pebble, then
file a new report through `exophial intake` (rehearse, then
`exophial intake --execute <id>`). The new pebble gets a new spec, a new
claim, and a new base.

Example, 2026-11-05: a husband narrowed clause C4 of `derived-exo-9ba` from
`tests/**/*.py` to one test file and dispatched again. The dispatch path then
committed the edited file as "commit engine-derived acceptance spec" (commit
`7af6b20aa`), so a hand edit carried the derivation's provenance. exo-0bc owns that path.

Re-admitting a parked pebble unchanged is never the next action. An
unchanged re-admission merges nothing, burns quota, and re-parks the pebble
on the same cause.

One park gets one subagent. If that subagent ends and the pebble is still
parked with no new park, a second subagent with the same brief is a retry. The
husband reads the first subagent's log, changes the brief or the precondition,
and only then dispatches again. `husband.py` cannot change a brief, so it
dispatches once per park and logs the pebble for the husband agent.

Husbandry requires subagents. One husband hand-editing every stuck pebble in
series does not scale past one pebble at a time. The husband coordinates: it
spawns one subagent per stuck pebble, and each subagent changes that
pebble's precondition and merges the fix.

Stopping is wrong. Leaving the pebble parked is wrong. Escalating to a
person by default is wrong. Each of the three ends the pebble's progress
without a merged fix.

The next action is always a changed precondition, authored by a subagent
the husband dispatched.

## Never wait on an exophial fix

Exophial is never a dependency of the work it coordinates. When exophial has a
defect, the coordinator files it with `exophial intake` and then works around
it. The coordinator does not stop, park its own work, or wait for the fix.

The exophial coordinator does not tell another repo's coordinator to wait for
an exophial fix. It names the defect and a way around it.

Example, 2026-11-02: an armada-lean spec oracle failed with `fatal: bad
revision 'integrated'` (exo-6ee). The armada coordinator did the work on its
own branches and merged them with `exophial apply`. It did not wait for
exo-6ee.

## Never take reducer lifetime, except a justified stop

Do not run `exophial start` or `restart`. Do not kill a worker, reap a
worktree, delete a branch, or merge onto the integration branch by hand. Never
set `EXOPHIALD_INTEGRATOR=1`.

Run `exophial stop` when three facts hold: a reducer holds the repo flock,
every pebble in its scope is parked or closed, and no worker container or
`omp-router` lease of that reducer exists. Do not wait for permission. For
example, a reducer that parked its last pebble hours ago, and blocks your
next dispatch, gets stopped. A stop loses no work: the next dispatch picks the
scope up again.

The single-integrator invariant is what makes a husband safe to run beside other
husbands. A husband that takes the integrator role removes that guarantee for
everyone else.

This rule binds the husband AGENT, not the supervisor loop. exophial's
`scripts/husband/husband.py` is a separate keep-alive process: it starts and
restarts the reducer as its own liveness duty, and it dispatches one subagent
per park. It never takes the integrator role itself.

## Guard every verb that reaches a model

A CLI invocation inherits no credential from the daemon. Any verb that derives a
spec fails with `transport_failure` and parks the pebble. Guard it, and let the
guard abort rather than run credential-less.

## Correct the brief with a measurement

A husband that refutes its own brief has done the expensive part of the work.
Report the refutation as the finding.

On 2026-08-10 three agents corrected the coordinator in one afternoon: one
proved a byte-identity constraint unsatisfiable, one proved a gate rejection had
a different cause than the coordinator claimed, and one proved a test left an
unfalsified zero by running it against a no-op mutation.

Never edit a brief's premise silently to make it true.

## Slice by carrier, never by file or by error mechanism

Slicing a migration by which module the errors appear in is a file split
relabelled. Trace the value from intake to terminal write, name the carrier type
at each hop, and give one husband one carrier.

## Dispose of every pebble, and say which disposition

Every pebble in the family ends closed or parked with a recorded cause. Nothing
is left open and untouched.

- Closed because the work merged: name the sha.
- Closed as superseded: name the superseding pebble.
- Closed as already delivered: name the commit and the code that delivers it.
- Parked: name the cause and what would clear it.

A root closes only when its own claim is false. If work remains, reword the root
to what actually remains rather than closing it over a live child.

Closing a parent while a child is open leaves that child parented to a closed
record. Decide the children explicitly.

## Keep a running log

Write to `.exophial/logs/husbandry/<family>.md` as you go. A husband's context is
lost when it yields; the log is what survives.

## End your turn with the report

Your last message is the report: merged shas (verified), each pebble's final
state, refusals verbatim, and candidate defects. It has no tool call. The
coordinator detects the end of a husband's work from that message.

## Never use sudo

A husband never runs `sudo`. Root steps outside every worktree guard.
