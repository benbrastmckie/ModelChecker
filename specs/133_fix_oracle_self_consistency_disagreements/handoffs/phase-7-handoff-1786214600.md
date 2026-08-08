# Phase 7 Handoff (final continuation): verification complete

**Status**: COMPLETED. The plan's substantive claim is verified green against the correct vehicle.
The gating suite is separately RED on three timeout-shaped, out-of-scope failures.

## The two carried soft blockers were already closed before this dispatch

Neither was this dispatch's work. Both were closed by commit `c8087c4d`. Verified at HEAD, not
assumed:

1. `MIN_CONCLUSIVE_SCAN_FORMULAS = 90` (`test_cross_oracle_differential.py:117`), not 137 —
   recalibrated below both real 274-formula measurements rather than at them.
2. `test_soundness_regression.py`'s five `OracleTimeoutError` failures migrated to
   `pytest.raises(OracleTimeoutError)` (import at line 32; raises sites at 434, 843, 895, 928,
   946, 1121, 1138).

## Green: the exhaustive scan

`oracle/run-oracle-exhaustive-scan.sh` completed — `oracle/scan-results/20260807T155847Z/`, with
the `SCAN_COMPLETE` marker (the script's sanctioned completion signal; never process exit status).

`agreements=103 disagreements=0 timeout_count=171` over 274 formulas, 3651.2 s (60.9 min) serial.
Recomputed independently from the 274 raw `report.json` entries and reproduces exactly.
`conclusive = 103 >= floor 90`, so both teeth of `_assert_scan_report` pass and
`test_complexity_5_scan_self_consistent` passes at HEAD.

Third consecutive full sweep with zero disagreements (101, 106, 103 conclusive).

## RED: the gating suite, and why it does not bear on the claim

`run-oracle-suite.sh`: pass 1 `1 failed, 557 passed, 2 skipped, 4 xfailed in 671.62s`; pass 2
`2 failed, 8 passed, 566 deselected in 740.90s`. Log:
`run/gating-suite-head-1786212046.log`.

**All three failures are timeout/conclusiveness failures. None is a disagreement.**

The run was measurably contended: `ps` was clean before launch, but a sibling task's
`pytest code/tests/integration/...` appeared mid-run at ~100% CPU, and an unrelated `pytest -m slow`
was still at 84-94% afterwards. Pass 2 — the nominally contention-free serial pass — ran 66% over
its measured basis, the signature of external load.

Isolated in separate pytest sessions:

| Test | Isolated | Disposition |
|---|---|---|
| `test_all_sat_task_relation_ternary` | PASSED 26.35s vs 180 s budget | Contention artifact |
| `test_spot_check_individual_countermodels` | PASSED 131.42s vs 180 s budget | Known same-session Z3-state flake; `xdist_serial` does not close it |
| `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` | 99, then 98, then **100** | Straddles its floor of 100 |

## The one reproducing failure is a calibration finding

Four measurements: conclusive `99, 98, 100` against a floor of exactly `100`, `disagreements=0`
every time. It passes only at the top of its own observed range.

Same mistake this plan already corrected once: `MIN_CONCLUSIVE_SCAN_FORMULAS` went from 137 (at
the sample's level, permanently failing) to 90 (below every measurement, stable).
`MIN_CONCLUSIVE_GATING_FORMULAS = 100` against `{98, 99, 100}` needs the same re-floor. Its own
comment corroborates: the manifest's slowest conclusive solve was 10.094 s against a 10000 ms
budget — ~0.9% *over* nominal.

**Not changed.** It is another task's constant guarding another task's manifest, and its comment
directs an investigator to "investigate instead" of raising it. `run-oracle-suite.sh`'s header
likewise forbids adjusting constants to paper over a contended run. Recommending the re-floor is
in scope; performing it is not.

## Vehicle correction (load-bearing for anyone re-verifying)

`oracle/run-oracle-suite.sh` deselects `slow` on **both** passes and no longer runs
`test_complexity_5_scan_self_consistent` at all. A green run of it confirms nothing about this
plan's claim; a red one does not refute it. Use `oracle/run-oracle-exhaustive-scan.sh`
(`code/docs/core/TESTING_GUIDE.md` section 8.8).

## Follow-ups (not this task)

1. Re-floor `MIN_CONCLUSIVE_GATING_FORMULAS` from the observed `{98, 99, 100}`.
2. Decide the disposition of `test_spot_check_individual_countermodels`'s session-order sensitivity.
3. Investigate the 13 genuine temporal-only disagreements kept `xfail`'d in
   `test_temporal_only_agreement_complexity_5` — a real soundness finding this fix surfaced.
