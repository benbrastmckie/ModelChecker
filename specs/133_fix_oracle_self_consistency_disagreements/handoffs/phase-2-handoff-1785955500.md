# Phase 2 Handoff: Fix the live CLI correctness bug

**Status**: COMPLETED

## What changed

- `oracle/bimodal_logic/cli.py`: `main()`'s `check` handler now wraps
  `provider.find_countermodel(...)` in `try/except OracleTimeoutError`, emitting
  `{"result": "inconclusive", "countermodel": None}` and `sys.exit(2)`. Module docstring's
  `Output format` and `Exit codes` blocks document the third outcome.
- `oracle/bimodal_logic/tests/test_cli.py`: new `TestCLIInconclusive` class (3 tests: exit code 2,
  `result == "inconclusive"`, `countermodel is None`) using a temporal formula that dispatches to
  the M>=3 solve path at `--timeout 1`. Widened `test_result_is_string` to accept `"inconclusive"`.

## RED confirmed

All three new tests failed before the fix with `OracleTimeoutError` propagating uncaught out of
`main()` — not a `SystemExit`, so `pytest.raises(SystemExit)` itself failed to trigger.

## GREEN verification

```
PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cli.py -q
21 passed in 1.14s
```

No task-number citations introduced in `cli.py` or `test_cli.py`.

## Deviation from plan

The plan's manual-confirmation command literally invokes `python -m bimodal_logic.cli check ...`.
`cli.py` has no `if __name__ == "__main__":` guard (pre-existing, unrelated to this plan), so
running the module this way is a silent no-op — it defines `main`/`run` but calls neither. Used an
equivalent direct call to `main()` instead and observed `{"result": "inconclusive", "countermodel":
null}` with `exit=2`, confirming the fix. Did not add a `__main__` guard — out of this plan's
scope, and the console-script entry point (`run()`) is unaffected since it does not rely on
`python -m`.

## Next phase

Phase 3 (interface/provider test migration, disjoint files) is unblocked and was run concurrently
with this phase per the plan's wave declaration.
