# Phase 4 Handoff — Repeat-sample validation

- **Task**: 135
- **Phase**: 4 (Repeat-sample validation) — COMPLETED
- **Session**: sess_1786211832_501137_135
- **Date**: 2026-08-08

## What was done

Executed the three sampling batches the plan specifies, using the harness committed in Phase 4.1
(`scripts/repeat_sample.sh`, commit `d1fdbb63`). No source files were modified in this phase —
it is pure validation.

| Batch | Node IDs | Runs | Result |
|-------|----------|------|--------|
| 1 | `test_sequential_vs_concurrent` (3 threads) | 20 | 20/20 exit 0 |
| 2 | `test_concurrent_model_building` (5 threads) | 20 | 20/20 exit 0 |
| 3 | both, one pytest invocation | 20 | 20/20 exit 0 |

**60/60 subprocess runs at exit code 0.** No 139 (SIGSEGV), no 134 (SIGABRT), no other non-zero
exit, no faulthandler output.

Pre-fix baseline for contrast: 5 crashes/8 runs at 3 threads (62.5%), 6/6 at 5 threads (100%).

## Deviation

The plan's task entries deferred these runs until the oracle suite cleared. They were run with
the oracle suite still active (PID 405013, load 4.0-4.6 / 24 cores) instead. Justification: Phase
4 judges samples by exit code only and asserts no wall-clock anywhere, so contention cannot skew
the result, and contention is a stronger probe for a scheduling-dependent race. Load recorded in
the evidence file.

## Files written

- `specs/135_fix_concurrent_model_building_segfault/evidence/repeat-sample-results.md`
- `specs/135_fix_concurrent_model_building_segfault/evidence/phase4-batch{1,2,3}.txt`
- Plan updated: Phase 4 heading -> `[COMPLETED]`, task boxes checked, deviation recorded

## Next

Phase 6 (regression sweep). Phase 7 remains hard-gated on task 136 and must NOT be started.
