# Pre-Fix Gate Baseline

Recorded before any production edit for the `all_constraints` stale-snapshot fix, per Phase 1 of
`plans/01_fix-stale-all-constraints.md`. All three invocations below are CI's own commands
(`.github/workflows/tests.yml`) plus the explicit bimodal suite run.

## Invocation 1: CI parallel pass

```
cd code
PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread
```

**Result**: `3084 passed, 15 skipped, 5 warnings in 329.37s (0:05:29)`

**Named pre-existing failures**: none.

## Invocation 2: CI xdist_serial pass

```
cd code
PYTHONPATH=src pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable" -q --timeout=300 --timeout-method=thread
```

**Result**: `9 passed, 3232 deselected in 4.60s`

**Named pre-existing failures**: none.

## Invocation 3: Bimodal suite explicit

```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/ -q
```

**Result**: `599 passed in 212.13s (0:03:32)`

**Named pre-existing failures**: none.

## Summary

The pre-fix gate is fully green across all three invocations — zero pre-existing failures to
carry forward. Any failure observed in the Phase 5 post-fix run is therefore a regression from
this task, with no exceptions to account for.

## Phase 1 RED failures (new tests, before production edit)

Recorded after adding the three `models` unit tests
(`code/src/model_checker/models/tests/unit/test_constraints.py`) and the bimodal post-solve
certificate-coverage test (`code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`,
new class `TestAllConstraintsReflectsCertificateAfterSolve`), and running them against the
pre-fix code. All four fail for the intended reason — none fails on a setup error, and the
recompute-not-stored test is NOT vacuous on the current code (correcting an earlier assumption
made while drafting this baseline before the tests were actually run: the pre-fix
`all_constraints` is a *stored* list attribute, not a value recomputed per access, so appending to
it mutates real state and the contract genuinely fails today too).

### `test_constraints.py` — live-view contract

`test_all_constraints_reflects_late_frame_constraint_mutation`: appending to
`constraints.frame_constraints` after construction was not reflected in
`constraints.all_constraints` (still the frozen 5-element snapshot). Observed:
`AssertionError: 5 != 6`.

### `test_constraints.py` — recompute-not-stored contract

`test_appending_to_all_constraints_value_does_not_mutate_the_source`: on the pre-fix code,
`all_constraints` is a stored list object (not computed per access), so
`constraints.all_constraints.append(...)` mutates that stored list in place and a subsequent read
sees the appended element — the opposite of the property's intended live-view/no-side-effect
contract. Observed: `AssertionError: 1 != 0`.

### `test_constraints.py` — assignment raises

`test_assigning_to_all_constraints_raises`: assigning `constraints.all_constraints = []` succeeded
silently on the current plain-attribute implementation (no exception raised). Observed:
`AssertionError: AttributeError not raised`.

### Bimodal post-solve certificate-coverage test

`test_all_constraints_contains_certificate_encoding_after_solve` (new,
`theory_lib/bimodal/tests/integration/test_iterate.py`, class
`TestAllConstraintsReflectsCertificateAfterSolve`): asserted
`len(structure.model_constraints.all_constraints) == len(full_constraints(structure))` on a real,
non-mocked `BM_CM_1` solve (`iterate_count=1`, no iteration). Observed:
`AssertionError: all_constraints (2) must match the true post-solve constraint set (132)` —
confirms the research report's measured gap (length-2 snapshot vs. 132-constraint true post-solve
set) exactly, and on a single non-iterated solve, matching F1's scope correction (every bimodal
solve, not only iterated ones).
