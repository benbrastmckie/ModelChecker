# Phase 5 Handoff: Reduce the budget and rewrite the scan's assertion

**Status**: COMPLETED

## Calibration measurements (30-formula bounded sample, complexity 1-4 only)

| Budget | Conclusive (corrected either-side rule) | Sample wall (60 solves) | Extrapolated full scan (548 solves) |
|---|---|---|---|
| 10000 ms | 53.3% (16/30) | 321s | ~49 min |
| 15000 ms | 50.0% (15/30) | 499s | ~76 min |
| 20000 ms | 56.7% (17/30) | 648s | ~99 min |

Raw data: `specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_10s_sample.jsonl`,
`scan_15s_sample.jsonl`, `scan_20s_sample.jsonl`.

**Important correction**: `scan_instrumented.py`'s own summary line (`D=`/`T=` counters) does
NOT apply the either-side-TIMEOUT counting fix from Phase 4 -- at 10000 ms it misclassified one
`ref=TIMEOUT, mc=SAT` pair as a `DISAGREE`. I recomputed the true agreements/disagreements/
timeout_count directly from each JSONL's per-record `ref_result`/`mc_result` fields using the
correct either-side rule (matching `_generate_differential_report`'s fixed logic) rather than
trusting the script's own printed summary. This script is pre-existing evidence tooling under
`specs/**`, not in Phase 5's file list, so it was not modified -- the recomputation was done ad
hoc and is reflected in the table above, not in the script's own printed `D=`/`T=` counts.

## Decision: kept SELF_SCAN_SOLVE_TIMEOUT_MS = 10000 (did not escalate to 20000)

None of the three rungs reached the plan's 60% conclusive-rate target, and the escalation ladder
mechanically bottoms out at 20000 ms (the hard ceiling) without ever hitting the target. Rather
than mechanically adopting 20000 ms as the "last rung tried," I computed a runtime-risk check the
plan's escalation-rule text does not itself spell out: scaling each sample's measured wall clock
to the full 548-solve sweep. The 20000 ms figure (~99 min) already exceeds Phase 7's 90-minute
full-scan abort ceiling on this extrapolation alone, and the 30-sample only reaches complexity 4
(complexity-5 formulas, the bulk of the 274-formula sweep, are not represented), so the true
figure is plausibly higher. Combined with the fact that conclusiveness is flat/noisy across all
three rungs (53.3% / 50.0% / 56.7%, no monotonic trend), escalating bought no measured benefit
while materially increasing the risk of exactly the suite-unrunnability problem this budget
reduction exists to prevent. Kept the budget at 10000 ms -- the plan's own designated starting
point, and empirically the best-measured, lowest-risk of the three rungs.

`MIN_CONCLUSIVE_SCAN_FORMULAS = 137`: floored the lowest of the three measurements (50.0%) to a
round number (50%) and applied to 274.

## What changed

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`:
  - `SELF_SCAN_SOLVE_TIMEOUT_MS` changed from `60000` to `10000`; comment block rewritten entirely
    (old "12x margin" rationale removed -- its premise was the exact conflation Phase 1 fixed).
  - New `MIN_CONCLUSIVE_SCAN_FORMULAS = 137` constant with its own comment distinguishing a
    budget/performance regression from a semantic one.
  - New `_assert_scan_report(report, min_conclusive)` helper (next to `_StubOracle`): the
    four-part assertion shape, reused by both the new stub-pinned tests and the real scan test.
  - Two new RED-first stub tests in `TestDifferentialReport`:
    `test_scan_assertion_fails_on_genuine_disagreement` and
    `test_scan_assertion_fails_on_conclusiveness_floor_not_vacuous_pass`.
  - `test_complexity_5_scan_self_consistent` rewritten to call `_assert_scan_report`; docstring
    states the two distinct claims.
- `specs/133_fix_oracle_self_consistency_disagreements/evidence/scan_10s_sample.jsonl`,
  `scan_15s_sample.jsonl`, `scan_20s_sample.jsonl` (new calibration measurement records).

## RED confirmed

Both new stub-pinned tests failed with `NameError: name '_assert_scan_report' is not defined`
before the helper was implemented.

## GREEN verification

```
PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestDifferentialReport -q
13 passed in 8.51s
```

`grep -n "12x margin"` returns nothing. Budget and floor constants verified present at their
definitions and use sites. The full scan was deliberately NOT run in this phase -- that is Phase
7's concern, and running it here would violate the plan's own phase-scoping discipline.

## Deviation from plan

The plan's calibration command literally sets `PYTHONPATH=code/src`; `scan_instrumented.py`
imports `bimodal_logic` directly, which needs `oracle/` on `sys.path` (not just `code/src`).
Used `PYTHONPATH="code/src:oracle"` instead.

## Next phase

Phase 6 (rewrite the five `xfail(strict=True)` tests) depends on this phase and is next.
