# Filing doctrine: rehearse related reports together

Operator ruling, 2026-11-18. This file applies to every `exophial intake`
filing. It does not repeat the intake contract; read `docs/AUTHORING.md` §1.1
for that.

## The rule

Reports are related when they concern the same code, the same rule, or the
same work family. Rehearse every related report before you execute any of
them. Then compare their derived spec sets. Then execute them.

1. **Collect the set.** List every report you will file for one topic, before
   you rehearse the first. Add the open pebbles that the duplicate check found
   for that topic.
2. **Rehearse all of them.** Run `exophial intake` (no `--execute`) for each
   report. Keep each reference id. Do not execute any id yet.
3. **Compare the spec sets.** Read each saved set in
   `.exophial/cache/dry-run/<id>.json`, and the committed spec of each related
   open pebble. Compare:
   - the files and entrypoints that each spec's oracles run or read;
   - clauses that require opposite things;
   - clauses that require the same thing twice.
4. **Change the set when the comparison finds a problem.** Merge two reports
   that are one defect. Remove a clause conflict by rewording one report, then
   rehearse again. A report that contradicts an open pebble names that pebble
   in its constraints.
5. **Execute the set, then record the order.** Execute each id. Then record a
   dependency (`exophial pebble dep-add`) where one pebble needs the other to
   merge first.

A single report with no related report or pebble skips steps 3 to 5.

## Why

On 2026-11-18 one coordinator session filed nine pebbles in four groups. Each
group was rehearsed in parallel, and the verdicts were read, but the derived
specs were compared for one group only. That comparison found an overlap, and
the two pebbles were filed anyway with no recorded dependency. Two other pebbles
were filed against the same runner function with no comparison. One filing
contradicted an open pebble that the filer had not read.

A conflict found after `--execute` costs a closed pebble and a new filing,
because no agent edits a claimed spec. The same conflict found in step 3
costs one rehearsal.
