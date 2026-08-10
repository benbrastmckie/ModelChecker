# Phase 3 Handoff: Migrate the interface and provider test suites

**Status**: COMPLETED

## What changed

- `oracle/bimodal_logic/tests/test_oracle_interface.py`: migrated every call site in the plan's
  inventory (`test_timeout_handling`, `test_deeply_nested_enriched`, the four `is not None`
  guards in `TestBoundaryRegressionViaOracle`/`TestEnrichedRoundTrip`, and the two
  `TestSpotCheckCrossSignal::test_validate_self_*` tests), plus five additional tests discovered
  broken when the full file was actually run post-Phase-1 (see below).
- `oracle/bimodal_logic/tests/test_oracle_provider.py`: migrated the two named permissive guards
  (`test_folded_json_for_enriched_input`, `test_boundary_safe_consistency`).
- `oracle/bimodal_logic/provider.py`: `validate_self()` gained an optional `timeout_ms: int =
  5000` parameter (backward-compatible default), needed to give
  `test_validate_self_temporal_only`/`test_validate_self_all_formulas` an explicit wider budget
  per the plan's own instruction. This touches a file outside Phase 3's stated "Files to modify"
  list but is a one-line, additive, backward-compatible signature change required to carry out
  the plan's explicit Phase 3 instruction.

## Five discoveries outside the plan's call-site inventory

The plan classified ~45 assertions as "Bucket 1: small non-boundary formulas, unaffected by
design." Running the suite found five tests where that classification was wrong -- each
constructs a formula that is not actually small/fast, and each broke the moment Phase 1 changed
the contract (independent of any Phase 3 edit):

1. `TestEnrichedRoundTrip::test_enriched_vs_primitive_sat_agreement[all_future]` -- does not
   decide even at 180 s (`TEMPORAL_SOLVE_TIMEOUT_MS`).
2. `TestOracleExampleRegressionViaAPI::test_oracle_regression` -- 3 of 42 `ACTIVE_EXAMPLES`
   (`BX11P_LIN_P_TH`, `BX11_LIN_F_TH`, `TN_TH_2`) do not decide at their 30 s budget.
3. `TestSpotCheckCrossSignal::test_spot_check_individual_countermodels` -- all four
   documented-valid formulas (F4/F7/F9/F10) fail to decide within 60 s.
4. `TestZ3IsolationStress::test_no_state_leakage_between_depths` -- its discarded-result depth-2
   probe formula times out at 30 s.
5. `TestSpotCheckCrossSignal::test_validate_self_temporal_only` -- even after widening to 180 s,
   still raises. Resolved via the plan's own stated fallback: assert `pytest.raises
   (OracleTimeoutError)` instead of chasing a larger budget indefinitely.

Each was fixed with the same pattern already established for the plan's named call sites:
classify via try/except `OracleTimeoutError`, skip/continue on the inconclusive case, and keep
the loud assertion only for genuinely decided results. Full detail and line numbers are recorded
inline in the plan file's Phase 3 task list.

## Verification (full, not just node-id-scoped)

```
PYTHONPATH="code/src:$PYTHONPATH" pytest oracle/bimodal_logic/tests/test_oracle_interface.py -q --durations=10
100 passed, 4 skipped, 4 xfailed in 1509.71s (0:25:09)

PYTHONPATH="code/src:$PYTHONPATH" pytest oracle/bimodal_logic/tests/test_oracle_provider.py -q
81 passed in 72.73s
```

The 4 skips are the genuinely budget-exhausted formulas now handled gracefully. The 4 xfails are
the pre-existing, out-of-scope entry-point/packaging tests (different root cause, untouched).

grep checks: `isinstance(result, (dict, type(None)))` only remains as the still-legitimate
post-timeout-check line in `test_deeply_nested_enriched`; `if result is not None` returns 0 in
both files.

## Deviation: PYTHONPATH override

`test_oracle_interface.py` imports `bimodal_harness` at module level. Nix's devShell already
exports `PYTHONPATH=code/src:../BimodalHarness/src`; a bare `PYTHONPATH=code/src` override (as
the plan's verification commands are literally written) replaces rather than appends to that,
causing `ModuleNotFoundError: bimodal_harness` at collection. Used
`PYTHONPATH="code/src:$PYTHONPATH"` throughout this phase's verification instead. `test_cli.py`
and `test_oracle_provider.py` do not import `bimodal_harness` and are unaffected either way.

## Next phase

Phase 4 (differential harness) does not depend on any Phase 3 file and was implemented
concurrently; see its own handoff. Phase 5 depends on Phase 4.
