# Implementation Summary: Task #141

**Completed**: 2026-08-10
**Duration**: ~1.5 hours

## Overview

Executed the salvage-and-retire plan for the nine stale, local-only branches identified in
`reports/01_stale-branch-triage.md`. Wrote the four `(c)`-classified findings into durable,
branch-independent documentation under `code/`, bundled and verified all nine branches to an
external archive, deleted the nine local branches behind an explicit three-gate check, and
records the full verdict table and verification evidence below. No source code changed and no
branch was classified `(b) reusable code as-is`, so no tests were added or run.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md` — added a new
  `## Witness Predicate Design History` section (three subsections: Falsity Constraints for Modal
  Operators, The Quantifier-Free Encoding and Why It Is Not Used, Non-Determinism: Diagnosed
  Causes) and its Table of Contents entry.
- `code/src/model_checker/solver/README.md` — added `## Background: Why a cvc5 Backend` (after
  `## Architecture`) and `## Known Issues` (immediately before `## Known Differences`).
- `specs/141_triage_stale_local_branches_and_salvage_value/bundle-manifest.md` — created: archive
  path, nine-row bundle table, verbatim `git bundle verify` output, restore recipe.
- `specs/141_triage_stale_local_branches_and_salvage_value/plans/01_stale-branch-retirement.md` —
  all five phases checked off, deviations annotated inline.
- `specs/141_triage_stale_local_branches_and_salvage_value/progress/phase-{1..5}-progress.json` —
  per-phase progress tracking with deviations.
- Nine local git branches deleted (`git branch -D`, local refs only — see verdict table below).
- `/home/benjamin/branch-archive/ModelChecker/*.bundle` — nine verified git bundles created
  outside the repository (external archive, not tracked by git).

## Verdict Table

All nine branches share one ancient merge-base with `master` (`fcf2b95`, 2024-02-08), so the raw
`master..branch` commit counts (1978-2108, reported in the original task description and
reconfirmed in research) measure inherited pre-restoration history, not branch-specific work.
The reliable deltas below are **pairwise-ancestor commit counts** (commits since the branch's
nearest real ancestor — either a shared base with a sibling branch, or `bimodal_refactor`'s own
tip for its two children, or `feature/cvc5-feasibility-test`'s tip for its pilot), established via
`git merge-base --is-ancestor` and `git log --oneline <ancestor>..<branch>` in
`reports/01_stale-branch-triage.md`.

| Branch | Verdict | Real delta (commits since nearest real ancestor) | Last commit date | Disposition | Bundle filename | `(c)` documentation home |
|---|---|---|---|---|---|---|
| `bimodal_refactor` | (a) superseded | 70 since `338f090e` (2025-09-18) | 2025-10-02 | deleted | `bimodal_refactor.bundle` | — |
| `feature/bimodal_witness` | (a) superseded | 16 since `338f090e` | 2025-09-24 | deleted | `feature__bimodal_witness.bundle` | — |
| `feature/bimodal_witness_backup` | (a) superseded | 2 since `338f090e` | 2025-09-23 | deleted | `feature__bimodal_witness_backup.bundle` | — |
| `feature/quantifier-free-witnesses` | (c) finding worth recording | 6 on `bimodal_refactor`'s tip (`274fa0e9`) | 2025-10-02 | deleted | `feature__quantifier-free-witnesses.bundle` | `bimodal/docs/ARCHITECTURE.md` § The Quantifier-Free Encoding, and Why It Is Not Used |
| `feature/witness-falsity-attempt` | (c) finding worth recording | 1 on `bimodal_refactor`'s tip (`274fa0e9`) | 2025-10-02 | deleted | `feature__witness-falsity-attempt.bundle` | `bimodal/docs/ARCHITECTURE.md` § Falsity Constraints for Modal Operators and § Non-Determinism: Diagnosed Causes |
| `feature/cvc5-feasibility-test` | (c) finding worth recording | 4 on `bimodal_refactor`'s tip (`274fa0e9`) | 2025-10-02 | deleted | `feature__cvc5-feasibility-test.bundle` | `solver/README.md` § Background: Why a cvc5 Backend |
| `feature/bimodal-cvc5-pilot` | (c) finding worth recording | 19 on `feature/cvc5-feasibility-test`'s tip (`26e0a067`) | 2025-11-05 | deleted | `feature__bimodal-cvc5-pilot.bundle` | `solver/README.md` § Known Issues |
| `refactor/exclusion` | (a) superseded | 2049 (no ancestor relation to any of the other 8) | 2025-10-01 | deleted | `refactor__exclusion.bundle` | — |
| `new_claude` | (a) superseded | 2108 (no ancestor relation to any of the other 8) | 2026-01-10 | deleted | `new_claude.bundle` | — |

No branch was classified `(b) reusable code as-is` and none was classified `(d) unclear` — every
verdict above is evidence-grounded per `reports/01_stale-branch-triage.md`.

## Archive

**Absolute path**: `/home/benjamin/branch-archive/ModelChecker/`

Outside `/home/benjamin/Projects/ModelChecker` (not in the working tree, not git-tracked) and
outside `/tmp` (survives reboot/tmpfs cleanup). Full details — per-bundle tip SHA, byte size,
sha256, and the restore recipe — are in
`specs/141_triage_stale_local_branches_and_salvage_value/bundle-manifest.md`.

Restore recipe (any one branch, does not touch `origin`):

```bash
git fetch /home/benjamin/branch-archive/ModelChecker/<bundle-file> refs/heads/<branch>:refs/heads/<branch>
```

## Verification Evidence

### All nine `git bundle verify` results (pre-deletion, from Phase 3 / re-run as Phase 4 Gate C)

```
/home/benjamin/branch-archive/ModelChecker/bimodal_refactor.bundle is okay
/home/benjamin/branch-archive/ModelChecker/feature__bimodal-cvc5-pilot.bundle is okay
/home/benjamin/branch-archive/ModelChecker/feature__bimodal_witness_backup.bundle is okay
/home/benjamin/branch-archive/ModelChecker/feature__bimodal_witness.bundle is okay
/home/benjamin/branch-archive/ModelChecker/feature__cvc5-feasibility-test.bundle is okay
/home/benjamin/branch-archive/ModelChecker/feature__quantifier-free-witnesses.bundle is okay
/home/benjamin/branch-archive/ModelChecker/feature__witness-falsity-attempt.bundle is okay
/home/benjamin/branch-archive/ModelChecker/new_claude.bundle is okay
/home/benjamin/branch-archive/ModelChecker/refactor__exclusion.bundle is okay
```

Each bundle's full verbatim `git bundle verify` output (including "The bundle records a complete
history" and hash-algorithm lines) is recorded in `bundle-manifest.md`. Each bundle's contained
tip SHA was cross-checked against the corresponding live branch's `git rev-parse
refs/heads/<branch>` via `git bundle list-heads <bundle>` before deletion — all nine matched
exactly, no mismatch.

### Deletion (Phase 4), `git branch -D` output

```
Deleted branch bimodal_refactor (was 274fa0e9).
Deleted branch feature/bimodal-cvc5-pilot (was 222add95).
Deleted branch feature/bimodal_witness (was 4a65f560).
Deleted branch feature/bimodal_witness_backup (was 399c9afb).
Deleted branch feature/cvc5-feasibility-test (was 26e0a067).
Deleted branch feature/quantifier-free-witnesses (was 01635e4a).
Deleted branch feature/witness-falsity-attempt (was c89f5327).
Deleted branch new_claude (was 814872a8).
Deleted branch refactor/exclusion (was 0b9ddd05).
```

Every deleted tip SHA prefix above matches the full tip SHA recorded for that branch in
`bundle-manifest.md` (e.g. `274fa0e9` -> `274fa0e93478528e690197a535dbb3e053e551ef`).

### Post-deletion `git branch --list` output

```
* master
  task-117-restore-model-checker
  task-140-fix-bimodal-order-dependence
```

(Current HEAD is `task-140-fix-bimodal-order-dependence`, unchanged throughout the task — the
working tree was never switched; all branch content was read with `git show <branch>:<path>` and
`git diff`, never by checkout.)

### Post-deletion bundle re-verification (Phase 4 verification step)

All nine bundles re-verified "is okay" after deletion (identical output to the pre-deletion run
above). A round-trip spot check on one bundle confirmed recoverability without mutating any ref:

```
$ git bundle list-heads /home/benjamin/branch-archive/ModelChecker/feature__cvc5-feasibility-test.bundle
26e0a067fd58048c89dace1f5784c6f4cbd1f4c7 refs/heads/feature/cvc5-feasibility-test
```

### Remote refs

`git branch -r --no-color | wc -l` returned **11** both before and after this task's phases (not
the `10` originally estimated in the plan/research — the live remote has 11 refs including
`origin/HEAD -> origin/master`; this was a pre-existing miscount, not a regression introduced by
this task). The count is identical before and after deletion, confirming `origin/*` was never
touched. The eleven remote refs (`origin/HEAD`, `origin/exclusion_attempt_9`,
`origin/false_premise`, `origin/finean_exclusion`, `origin/iterate`, `origin/master`,
`origin/new_defined_operator`, `origin/old_jupy`, `origin/pre-full-skolem`,
`origin/reduced_exclusion`, `origin/refactor_exclusion_single_strategy`) share no names with any
of the nine retired branches, confirming they were always a disjoint set.

## Testing & Validation

No code was ported (nothing classified `(b) reusable code as-is`), so no tests were added or run.
Validation was entirely documentation-content and git-state checks, all of which passed (see
Verification Evidence above). No `git push`, no `git merge` of any stale branch, and no mutation
of any `origin/*` ref occurred at any point in this task.

## Open Question Carried Forward

Whether bimodal's existing `'solver': 'cvc5'` setting produces correct countermodels end-to-end
through the current solver abstraction layer remains **unverified**. This is now documented in
`code/src/model_checker/solver/README.md` under `## Known Issues`, alongside the reproducible
segfault risk when applying a declared function through the cvc5 backend. Verifying the cvc5 path
end-to-end requires installing and running cvc5 and is candidate work for a separate task.

## Notes

- No branch required deviation from the plan's deletion ordering: all three gates (verdicts
  recorded, findings written, bundles green) passed on first evaluation before any `git branch -D`
  ran.
- Two documentation deviations from the plan's literal task wording are recorded in
  `progress/phase-1-progress.json` and `progress/phase-2-progress.json`: direct inspection of
  `witness_constraints.py`, `witness_registry.py`, `core.py`, and `cvc5_adapter.py` showed that
  (1) `_witness_constraint_for_falsity()` is an unreached placeholder rather than the active Box
  falsity mechanism (the real mechanism is `z3.ForAll`/`z3.Exists` directly in
  `NecessityOperator`, `operators.py`), and (2) `cvc5_adapter.py` has no `apply_function` method
  today, so the segfault risk is described as applying a declared function through the cvc5
  backend generally rather than citing a still-live call site. Both corrections keep the written
  documentation accurate to the current tree rather than repeating an imprecise characterization
  from the research report.
- A third deviation (remote-ref count 11 vs. the plan's stated 10) is recorded in
  `progress/phase-4-progress.json` and above under Remote refs.
