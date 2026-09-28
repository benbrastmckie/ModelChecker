# Phase 1 Handoff: Capture Pre-Fix Baseline

**Status**: COMPLETED

## What was done

Captured pre-fix baselines under `baselines/`:
- `01_pre-fix-iterate.txt` -- `iterate/` suite: 2 failed (both out-of-scope generic-pinning
  cases for logos/imposition), 239 passed.
- `01_pre-fix-theory-suites.txt` -- four-theory gate: 1695 passed, 0 failed.
- `01_pre-fix-bimodal-iterate.txt` -- bimodal's `test_iterate.py` standalone: 29 passed.
- `01_pre-fix-{logos,exclusion,imposition}-iteration.txt` -- `dev_cli.py` runs of the
  representative `iterate: 3` example per theory (temp example files built in the scratchpad
  matching the plan's exact parameters).
- `01_pre-fix-summary.md` -- consolidated summary, including a recorded deviation from the
  plan's Scope Hypothesis (the four-theory gate showed 0 pre-existing failures this run, not
  the 1 the plan expected from a prior task's stale record; treated as this run's actual
  baseline going forward per the plan's own instruction).

## Deviation

Four-theory gate's pre-existing-failure count differs from the plan's Scope Hypothesis (0 vs
expected 1). Documented in `baselines/01_pre-fix-summary.md`; Phase 4 will use this run's
actual empty failing-set as the comparison baseline, not the stale prior-task record.

## Next phase

Phase 2 (RED regression tests) is already drafted and confirmed RED against the pre-fix engine
(all 6 parametrized tests fail); Phase 3's fix is already drafted in
`code/src/model_checker/iterate/constraints.py` but not yet committed separately. Next dispatch
continues from Phase 2's formal closure and Phase 3's verification.
