# Phase 1 Handoff: Raise on timeout instead of returning None

**Status**: COMPLETED

## What changed

- `oracle/bimodal_logic/errors.py` (new): `OracleTimeoutError(Exception)`, mirroring the shape
  (message + `context` dict + `suggestion`) of `Z3TimeoutError` without importing/subclassing it.
- `oracle/bimodal_logic/__init__.py`: exports `OracleTimeoutError`.
- `oracle/bimodal_logic/provider.py`: `find_countermodel()` now raises `OracleTimeoutError` when
  `structure.timeout` is true, instead of returning `None`. The `not structure.z3_model_status`
  branch (genuine UNSAT) is unchanged and still returns `None`. Docstrings updated with `Returns:`
  narrowed to its true meaning and a new `Raises:` section. `validate_self()` left structurally
  unchanged (exception propagates); docstring updated with a `Raises:` section.
- `oracle/bimodal_logic/tests/test_oracle_provider.py`: new `DEEPLY_NESTED_TEMPORAL_JSON` fixture
  (an until/since formula that dispatches to the M>=3 solve path) and
  `test_budget_exhausted_raises_oracle_timeout_error` in `TestFindCountermodelContract`.

## RED confirmed

`Failed: DID NOT RAISE <class 'bimodal_logic.errors.OracleTimeoutError'>` — not an ImportError.

## GREEN verification

```
PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_oracle_provider.py::TestFindCountermodelContract oracle/bimodal_logic/tests/test_oracle_provider.py::TestValidateSelf -q
20 passed in 3.65s
```

Import check (note: required `PYTHONPATH=code/src:oracle`, not just `code/src` as the plan's
verification command literally states — `oracle/` has no `__init__.py` so pytest's own rootdir
insertion handles it during test runs, but a bare `python -c` needs it added explicitly):
```
python -c "from bimodal_logic import OracleTimeoutError; print(OracleTimeoutError)"
<class 'bimodal_logic.errors.OracleTimeoutError'>
```

No task-number citations introduced (`grep -rn "task [0-9]" oracle/bimodal_logic/errors.py oracle/bimodal_logic/provider.py` → no matches).

## Expected RED elsewhere (not yet fixed, by design)

Confirmed `test_oracle_interface.py::test_timeout_handling` is now broken (its formula
`_all_future(_all_past(_some_future(_some_past(A))))` at `timeout_ms=1` now raises
`OracleTimeoutError` instead of returning `None`, so its `assert result is None` fails). This is
the intentional RED window named in the plan; Phase 3 owns the fix. Did not run the full
interface/differential suites in this phase (deliberately out of scope per the plan's
phase-scoped verification).

## Deviation from plan (sequencing only)

The plan's task list writes "RED first" as the very first bullet, before "Create errors.py" and
"Export it from __init__.py". Taken literally, writing the test before those two exist would make
the test fail with `ImportError`, not `DID NOT RAISE` — which the plan's own success criterion
rules out. Resolved by creating `errors.py` and the `__init__.py` export first (pure scaffolding,
no behavior change to `provider.py`), then writing/running the RED test, then editing
`provider.py` for GREEN. All content matches what the plan specifies; only the execution order of
the first three bullets was adjusted to make the stated RED criterion achievable.

## Next phase

Phase 2 (CLI fix) and Phase 3 (interface/provider test migration) are both unblocked (depend only
on Phase 1) and may run concurrently — they touch disjoint files.
