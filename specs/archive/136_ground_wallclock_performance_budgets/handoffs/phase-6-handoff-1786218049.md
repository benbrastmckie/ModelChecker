# Phase 6 handoff — 3-invocation unfiltered verification

- Three SEPARATE invocations of `PYTHONPATH=src python -m pytest -q -p no:cacheprovider` (unfiltered,
  quarantine already deleted): 2190 passed / 0 failed / 0 deselected each, in 336.81s / 387.33s / 418.11s.
- Identical result set, established structurally: collection is a deterministic 2190 with 0 deselected,
  and every run reported 2190 passed with zero FAILED/ERROR/skipped/xfail. Passed set == collected set
  in all three.
- All 3 research-measured failures pass 3/3. No out-of-scope failure appeared; the contingency
  (revert Phase 5, mark PARTIAL) was NOT triggered.
- Honest note: a first attempt at run 3 was killed at 580s by the harness command timeout at 55%
  progress with zero failures so far. Truncated measurement, not a result; discarded and re-run
  detached. Recorded in the evidence file.
- Evidence: specs/136_ground_wallclock_performance_budgets/evidence/unfiltered-repeat-results.md
  plus raw unfiltered-run-{1,2,3}.txt.
