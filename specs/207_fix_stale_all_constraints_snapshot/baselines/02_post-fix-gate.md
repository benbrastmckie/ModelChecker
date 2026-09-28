# Post-Fix Gate Result and Baseline Diff

Recorded after Phases 1-4 landed (all_constraints converted to a computed property, the one
production write site migrated, the three injection append sites redirected, and
`full_constraints()` delegated to the property), per Phase 5 of
`plans/01_fix-stale-all-constraints.md`. Same three invocations as
`baselines/01_pre-fix-gate.md`, run the same way.

## Invocation 1: CI parallel pass

```
cd code
PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread
```

**Result**: `3106 passed, 1 skipped, 5 warnings in 240.15s (0:04:00)`

**Diff against baseline** (`3084 passed, 15 skipped`): 0 failures either run. Total collected
items rose from 3099 to 3107 (+8): this task added 4 tests (three `models` unit-contract tests
plus one bimodal post-solve regression test); the remaining +4 collected items and the skip count
drop (15 -> 1) come from a concurrent sibling task's (197) uncommitted, in-progress changes to
`theory_lib/bimodal/tests/_lean_check.py` and `test_certificate_lean_agreement.py`, sharing this
working tree per the dispatch's territory note -- not a change made by this task, and not staged
or committed by it. No failure is present in either run.

## Invocation 2: CI xdist_serial pass

```
cd code
PYTHONPATH=src pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable" -q --timeout=300 --timeout-method=thread
```

**Result**: `9 passed, 3236 deselected in 3.55s`

**Diff against baseline** (`9 passed, 3232 deselected`): identical pass count; deselected count
shift matches the same +4 collected-item delta noted above. No failure in either run.

## Invocation 3: Bimodal suite explicit (`-v`)

```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -v
```

**Result**: `601 passed in 250.39s (0:04:10)`

**Diff against baseline** (`599 passed`): +2, matching the +1 test this task added
(`TestAllConstraintsReflectsCertificateAfterSolve`) plus +1 from the same concurrent sibling task
noted above. No failure in either run.

## Summary

Every failure count is zero in both the pre-fix baseline and this post-fix run, across all three
invocations CI itself runs plus the bimodal suite. There is no regression to name: every count
delta is fully accounted for by this task's own four new tests plus a concurrent sibling task's
independent, uncommitted, in-progress work sharing this working tree (never touched, staged, or
committed by this task). The fix is cross-theory safe: logos, exclusion, and imposition (the three
single-phase theories) show zero behavioural change, and bimodal's full suite -- including every
A2-triangle/pinned-eval test and the live, non-mocked `TestLiveIteration` iterate coverage -- is
green.
