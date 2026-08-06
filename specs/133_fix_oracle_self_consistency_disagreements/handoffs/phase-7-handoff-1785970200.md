# Phase 7 Handoff: Full-suite verification and the downstream exit criterion

**Status**: PARTIAL (verification work complete; suite did not go green)

## Scan-alone run

```
PYTHONPATH="code/src:$PYTHONPATH" pytest "...::TestFullScanReport::test_complexity_5_scan_self_consistent" -q -s --durations=0
```

- Exit 1 (FAILED). Wall clock: 3606.39s (1:00:06) -- well inside the 90-minute abort ceiling; no
  abort needed.
- Recorded counts: `agreements=106 disagreements=0 timeout_count=168 conclusive=106/274`.
- **Failed on the conclusiveness floor (106 < 137), not on disagreements (0).** This is exactly
  the distinction the two-tooth `_assert_scan_report` assertion exists to make: the soundness
  claim (zero disagreements among conclusive results) holds; the performance floor does not.

## Why the floor missed

`MIN_CONCLUSIVE_SCAN_FORMULAS = 137` was calibrated in Phase 5 from a 30-formula sample that only
reached complexity 4 (the enumerator's first 30 formulas, in ascending complexity order, never
reach complexity 5). That sample measured 50.0-56.7% conclusive across the three budget rungs.
The real, full 274-formula sweep measured 38.7% conclusive (106/274) -- meaningfully lower,
confirming the under-representation caveat already flagged in the Phase 5 handoff. Complexity-5
formulas are evidently harder to decide than complexity<=4 ones on average.

**The floor was deliberately not adjusted in this session.** Recalibrating it downward and
re-running to chase a green result was considered and rejected: (1) the coordinator's explicit
instruction was to report this honestly rather than force green; (2) even a corrected floor would
not have produced a green suite, because of the independent `test_soundness_regression.py`
failures below; (3) each re-run costs another ~60-77 minutes and this session had already spent
well over 3 hours on Phase 7. Recalibration is left as an explicit follow-up recommendation.

## Full two-pass suite run

```
nix develop --command bash oracle/run-oracle-suite.sh
```

- Pass 1 (parallel, `-n 6`, not `xdist_serial`): **FAILED**, 5 failed / 538 passed / 4 skipped /
  5 xfailed, 4313.42s (1:11:53).
- Pass 2 (serial, `xdist_serial`): **FAILED**, 1 failed / 6 passed / 552 deselected, 285.74s
  (0:04:45).
- Total suite wall clock: ~76.7 minutes.

### The six failures

One is this plan's own test (`test_complexity_5_scan_self_consistent`, covered above). **The
other five are all in `test_soundness_regression.py`**, a file never touched by any phase of this
plan and not in its file list:

- `TestKnownBoundaryUnsafe::test_gf_p_returns_none_at_m4`
- `TestKnownBoundaryUnsafe::test_imp_gg_p_gf_p_returns_none_at_m4`
- `TestKnownBoundaryUnsafe::test_ff_p_returns_none_at_m4`
- `TestOracleMFormulaBoundarySafe::test_oracle_m_formula_depth2_returns_none`
- `TestStateIsolationRegression::test_no_semantics_reference_leak_with_temporal` (pass 2)

All five share an **identical failure signature**: `OracleTimeoutError: Z3 solver did not decide
the formula within 5000 ms (temporal_depth=2, time_bound M=4)`, raised out of a test asserting
`result is None`. Each test's own docstring documents the formula as "M4 boundary-unsafe --
returns None" -- i.e. these tests encode the exact same timeout/UNSAT conflation this whole plan
exists to remove, just in a third file the plan's inventory never enumerated. Before Phase 1, a
budget-exhausted solve at this M=4/depth=2/5000ms combination silently returned `None`, which
these tests then asserted as correct. Phase 1 correctly stopped that silent behavior; these tests
were never migrated because they were never in scope.

**Per the plan's own Phase 7 instruction ("If any test other than the ones this plan migrated
fails, report it with its node id and output and stop. Fixing it is out of scope.") these five
are reported here, not fixed.** Recommend a follow-up task scoped to `test_soundness_regression.py`
specifically, applying the same resolved-and-wrong/inconclusive bucketing pattern established in
this plan's Phase 3 and Phase 6. Given the identical failure signature across all five, it is
plausible (not yet verified) that all five are simply inconclusive rather than resolved-and-wrong
-- but that determination is exactly the follow-up task's job, not something to guess here.

## Exit criterion status

**NOT MET.** No green two-pass suite run was produced in this session. The counts that were
recorded (`agreements=106 disagreements=0 timeout_count=168` for the scan; 5 pre-existing
out-of-scope failures for the rest of the suite) are the honest, actual result -- not a
hypothetical green run's counts. See the implementation summary for the exit-criterion text
adapted to this actual outcome.

## What Phase 7 did accomplish

- Confirmed the core contract fix works: **zero semantic disagreements** across the full
  274-formula complexity<=5 self-consistency sweep, at 10000 ms, over 60+ minutes of real Z3
  solving. This is the plan's central soundness claim, and it holds.
- Confirmed the two-tooth assertion behaves exactly as designed: it distinguished a
  budget/performance regression (floor miss) from a semantic one (would have been disagreements)
  cleanly and automatically, with no manual disambiguation needed.
- Surfaced a second, independent instance of the exact bug this plan targets, in a file outside
  this plan's scope -- itself confirmation that the underlying defect (a solver timeout silently
  reported as `None`) was real and not confined to the files this plan enumerated.

## Next steps (not part of this task)

1. Follow-up task: migrate `test_soundness_regression.py`'s five affected tests using the
   resolved-and-wrong/inconclusive pattern.
2. Follow-up task or plan revision: recalibrate `MIN_CONCLUSIVE_SCAN_FORMULAS` from the real
   274-formula measurement (106, or lower under `-n 6` contention) rather than the optimistic
   30-sample estimate, and re-run `oracle/run-oracle-suite.sh` to confirm green.
3. Once both are green, `oracle/run-oracle-suite.sh`'s summary block plus the scan's three counts
   become the artifact the downstream regression-baseline task consumes.
