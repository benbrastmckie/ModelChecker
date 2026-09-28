# Pre-Fix Baseline Summary

Captured before any Phase 3 production edit lands, per the plan's Phase 1.

## Shared-engine iterate suite

Command:
```
PYTHONPATH=code/src pytest code/src/model_checker/iterate/ -q
```

Result: `2 failed, 239 passed in 55.32s`

Failing tests (pre-existing, out of this task's scope -- generic-pinning territory):
- `code/src/model_checker/iterate/tests/integration/test_models.py::TestGenericPinningReachesRebuiltSolve::test_rebuilt_solve_matches_pinned_values[logos]`
- `code/src/model_checker/iterate/tests/integration/test_models.py::TestGenericPinningReachesRebuiltSolve::test_rebuilt_solve_matches_pinned_values[imposition]`

These are exactly the two failures this task's description names as another task's own
territory (the generic pinning loop and its dedicated test class), expected to still fail
before this fix lands (the persistent search solver being empty is *why* the pinned candidate
is currently satisfiable against an unconstrained search rather than genuinely reaching a
rebuilt, correctly-solved model). Not caused by, and not resolved by, this task.

Full output: `baselines/01_pre-fix-iterate.txt`

## Four-theory directory gate

Command:
```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/ code/src/model_checker/theory_lib/exclusion/ code/src/model_checker/theory_lib/imposition/ code/src/model_checker/theory_lib/bimodal/ -q
```

Result: `1695 passed in 353.51s (0:05:53)` -- **zero failures**.

**Deviation from the Scope Hypothesis**: the plan's Scope Hypothesis expected this gate to
reproduce a prior task's recorded pre-fix shape (`1 failed, ~1694 passed`, the one failure being
`theory_lib/bimodal/tests/integration/test_iterate.py::TestLiveIteration::
test_a_live_run_detects_a_genuine_rotation_permutation_duplicate`). That failure did **not**
reproduce in this run: all 1695 collected tests passed, including that specific test. Bimodal's
`test_iterate.py` was additionally run standalone (see below) and also passed cleanly (29/29).
This test exercises live Z3 search timing/rotation-permutation detection and its prior failure
record elsewhere is consistent with flakiness (timing- or solver-state-dependent), not a
deterministic failure this environment currently reproduces. Recorded here as required by the
plan rather than silently assumed; Phase 4's post-fix comparison uses this run's actual set
(empty) as the pre-fix baseline, not the prior task's stale record.

Full output: `baselines/01_pre-fix-theory-suites.txt`

## Bimodal iterate integration file, standalone

Command:
```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py -q
```

Result: `29 passed in 32.67s` -- no failures. This is the "unchanged in outcome" reference Phase 4
compares against.

Full output: `baselines/01_pre-fix-bimodal-iterate.txt`

## Representative iterate > 1 example captures (per affected theory)

Captured via `./dev_cli.py` against temporary example files
(`{theory}_example.py`, N/settings taken from the plan's `_search_solver_cases`), matching
this task's description exactly: logos `[] |- \neg A` N=2 max_time=40 iterate=3; exclusion
`EX_CM_6` N=3 max_time=40 iterate=3; imposition `IM_CM_0` N=4 max_time=40 iterate=3.

Pre-fix models-found counts (search running against an unconstrained persistent solver for
logos and imposition; exclusion already had a working search per the task description):
- **logos**: 1/3 models found (search converges almost immediately -- the persistent solver has
  0 assertions, so nearly every "new" candidate collides/skips).
- **exclusion**: 3/3 models found (exclusion's iteration already worked correctly pre-fix per
  the task description -- not populated by a workaround, but apparently not exposed by this
  particular example/timing the way logos and imposition are).
- **imposition**: 2/3 models found, timing out after 40s having checked 44 candidate models for
  the third (search thrashes against an unconstrained problem).

Full output: `baselines/01_pre-fix-logos-iteration.txt`, `baselines/01_pre-fix-exclusion-iteration.txt`,
`baselines/01_pre-fix-imposition-iteration.txt`. These are the diffs Phase 6 reviews against the
post-fix behavior.
