# Phase 1 Handoff: Widen the scan's solve budget and retract the stale classification

**Status**: COMPLETED

## What was done

- Added `SELF_SCAN_SOLVE_TIMEOUT_MS = 60000` as a module-level constant in
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`, with a comment recording the
  measured 4.7796s/5.0003s solve-time band and citing `code/docs/core/TESTING_GUIDE.md` section
  8.6 for the sizing rule. No task-number reference in the comment (file lives outside `specs/`).
- Added an optional `timeout_ms: int | None = None` keyword parameter to
  `_run_differential_comparison` and `_generate_differential_report`, defaulting to `None` (no
  behavior change at any of the other 8 + 5 call sites). Docstrings updated.
- `test_complexity_5_scan_self_consistent`'s `ref_fn` and its `_generate_differential_report` call
  both now pass `timeout_ms=SELF_SCAN_SOLVE_TIMEOUT_MS`, so both per-formula solves carry the same
  widened budget.
- Added the corrective note (two blockquote insertions) to
  `specs/127_close_oracle_suite_regression_baseline/plans/01_close-oracle-regression-baseline.md`,
  retracting the "Category C contention flake" label for this specific test in place (original
  text preserved), citing the disposition document and this task's research report.

## Verification performed

- `python -m py_compile` on the modified test file: passed.
- `grep -n "SELF_SCAN_SOLVE_TIMEOUT_MS" oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
  returns exactly 3 matches (constant, `ref_fn` call, report call) — matches the plan's
  verification criterion.
- Fast consumers of both modified helpers (foreground, not marked `slow`):
  `TestDifferentialComparison`, `TestDifferentialReport`, `TestCIGate` — **19 passed, 1 xfailed**,
  exit 0, 152.86s.
- `grep -n "Correction" specs/127_.../plans/01_close-oracle-regression-baseline.md` returns 2
  matches (both inserted blockquotes).

## Next phase

Phase 2: run `test_complexity_5_scan_self_consistent` alone in the background (expected ~30+ min,
abort at 2h30m) and record its wall clock and pass/fail.
