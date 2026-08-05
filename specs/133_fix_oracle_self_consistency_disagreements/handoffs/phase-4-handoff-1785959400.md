# Phase 4 Handoff: Make the differential harness three-valued

**Status**: COMPLETED

## What changed

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`:
  - New `_StubOracle` class (Z3-free, outcome table keyed by formula `name`) and three RED-first
    stub tests in `TestDifferentialReport`.
  - New `_reference_verdict(oracle, formula_json, timeout_ms=None) -> str` helper next to
    `_run_differential_comparison`.
  - `_generate_differential_report`'s `ref_result = reference_fn(formula_json)` call now guarded
    with `try/except OracleTimeoutError: ref_result = "TIMEOUT"` (the highest-risk migration
    point named in the plan).
  - Counting logic changed from `if record["mc_result"] == "TIMEOUT"` to `if
    record["mc_result"] == "TIMEOUT" or record["reference_result"] == "TIMEOUT"`, fixing the
    inversion where a TIMEOUT reference against a decided subject was miscounted as a
    disagreement.
  - All 6 inventoried `"SAT" if result is not None else "UNSAT"` closures (lines 1286, 1373,
    1400, 1420, 1528, 1544 in the pre-Phase-4 file) migrated to one-line `_reference_verdict`
    delegations.
  - `test_temporal_only_self_consistency` (Bucket 3, runs in normal CI) rewritten to classify
    each side via `_reference_verdict` and compare only when both are conclusive, printing the
    inconclusive count unconditionally.
  - Docstrings of `_run_differential_comparison` and `_generate_differential_report` updated to
    document `"TIMEOUT"` as a reachable value and its source.

## RED confirmed (three distinct, correct reasons)

- `test_stub_three_way_classification_counts`: `NameError: name '_reference_verdict' is not
  defined`.
- `test_reference_fn_timeout_survives_report_generation`: `OracleTimeoutError` propagated
  uncaught out of `_generate_differential_report`.
- `test_reference_timeout_not_counted_as_disagreement`: `disagreements=1` instead of
  `timeout_count=1` (the exact counting inversion the fix targets).

## GREEN verification

```
PYTHONPATH=code/src pytest \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialComparison \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestCIGate -q
22 passed, 1 xfailed in 110.24s
```

The 1 xfail is `test_oracle_baseline_agreement`, untouched Phase 6 territory.
`test_temporal_only_self_consistency` (real Z3, 30 sampled formulas) took 84.60s, passed with 0
inconsistencies and 0 reported inconclusive in this run.

`grep -c 'is not None else "UNSAT"'` returns 1 (only inside `_reference_verdict`'s own body).
`grep -n "_reference_verdict"` returns the definition plus 8 further references.

## Next phase

Phase 5 (budget calibration and scan assertion rewrite) depends on this phase and is next.
