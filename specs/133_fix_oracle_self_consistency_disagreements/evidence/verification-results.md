# Verification results — find_countermodel contract fix

All runs below were performed with no competing pytest processes (checked via `ps` before each
launch, per `code/docs/core/TESTING_GUIDE.md` section 8.6). Earlier runs that reported tail
failures were contaminated by two concurrent `-n 6` sessions competing for cores — the exact
CPU-contention mode the suite's two-pass split exists to avoid.

## Deployed constants

| Constant | Value | Meaning |
|---|---|---|
| `SELF_SCAN_SOLVE_TIMEOUT_MS` | 10000 | Per-solve Z3 budget for the exhaustive self-consistency sweep |
| `MIN_CONCLUSIVE_SCAN_FORMULAS` | 90 | Conclusiveness floor; a miss is a budget/performance regression, not a semantic one |

The floor is deliberately set *below* every real full-sweep measurement (101, 103, 106 of 274) so
it tolerates run-to-run variance and parallel contention while still catching a genuine
conclusiveness collapse.

## Exhaustive self-consistency sweep (complexity<=5, 274 formulas x 2 solves)

Run via `oracle/run-oracle-exhaustive-scan.sh`, which is the **only** vehicle for this claim.
`oracle/run-oracle-suite.sh` deselects `slow` on both passes and does not touch the sweep at all
(see `code/docs/core/TESTING_GUIDE.md` section 8.8, "Oracle Suite: Gating vs. Exhaustive Split").

Latest run — `oracle/scan-results/20260807T155847Z/`, `SCAN_COMPLETE` marker present:

| Metric | Value |
|---|---|
| Total formulas | 274 |
| Conclusive (both sides decided) | 103 |
| **Disagreements among conclusive results** | **0** |
| Inconclusive (either side timed out) | 171 |
| Wall clock | 3651.2 s (60.9 min), serial |

Counts were recomputed independently from `report.json`'s 274 raw `entries` rather than read from
its summary fields: 103 entries with neither side `TIMEOUT`, of which **0** have mismatched
verdicts; 171 entries with at least one side `TIMEOUT`. This matches the reported
`agreements=103 disagreements=0 timeout_count=171` exactly.

Against the deployed floor: `conclusive = 274 - 171 = 103 >= 90` — both teeth of
`_assert_scan_report` are satisfied (zero disagreements, floor cleared).

## Conclusiveness across measurements

| Budget | Conclusive | Rate | Disagreements |
|--------|-----------|------|---------------|
| 5000 ms (pre-fix baseline) | 101/274 | 36.9% | 0 |
| 10000 ms (deployed) | 106/274 | 38.7% | 0 |
| 10000 ms (deployed, repeat) | 103/274 | 37.6% | 0 |

Doubling the budget bought 5 formulas. Bounded 30-formula samples at 10/15/20 s measured
53.3% / 50.0% / 56.7% — flat, and unrepresentative because they under-sample complexity 5 (218 of
the 274 formulas). Conclusiveness is essentially budget-independent in this range; widening the
budget is not the lever that moves it. The 106-vs-103 spread across two runs at the *same* budget
is the run-to-run variance the floor of 90 exists to absorb.

Zero disagreements in all three full sweeps, across two budgets and roughly three hours of real
Z3 solving, is the plan's central soundness claim.

## Note on run duration

The gating passes take ~19 minutes combined; the exhaustive sweep takes ~60 minutes. Any
verification harness that truncates a run at 10 minutes will cut a pass off mid-flight and produce
a misleading partial result. Detach long runs and detect completion from the summary line (or, for
the sweep, from the `SCAN_COMPLETE` marker) — never from process liveness. A vanished PID is not a
verdict.
