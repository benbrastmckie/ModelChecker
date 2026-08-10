# Phase 6 Handoff: Rewrite the five xfail(strict=True) tests rooted in this cause

**Status**: COMPLETED

## Outcome per test

BimodalHarness is present on this machine's path, so all five tests ran (none skipped).

| Test | Resolved-and-wrong | Inconclusive | xfail after |
|---|---|---|---|
| `test_known_invalid_return_countermodel` | 0 | 9/20 | removed (was XPASS) |
| `test_temporal_only_agreement_complexity_3` | 0 | 7/14 | removed (was XPASS) |
| `test_spot_check_all` | 0 | 4 | removed (was XPASS) |
| `test_oracle_baseline_agreement` | 0 | 9 (invalid-side only) | removed (was XPASS) |
| `test_temporal_only_agreement_complexity_5` | **13/158** | 101/158 | **kept** (genuine XFAIL) |

Four of the five now pass unconditionally -- their non-agreements were entirely
budget/performance (inconclusive), not soundness bugs, once the timeout/UNSAT conflation was
removed. `test_temporal_only_agreement_complexity_5` is the exception the plan explicitly
anticipated: 13 of 158 temporal-only formulas at complexity<=5 have both MC and BH decide and
genuinely disagree. This is a real, previously-masked soundness finding, separate from and not
diluted by the 101 formulas that are merely inconclusive. Its `reason=` was rewritten to state
this precisely (counts included) rather than blaming timeout conflation, which no longer applies.
Investigating the 13 resolved-and-wrong formulas is out of this plan's scope -- a real defect
surfaced by the contract fix, not something this task fixes.

## RED/GREEN discipline via the strict xfail safety net

For each of the four now-passing tests, the rewritten body (with the resolved-and-wrong /
inconclusive bucketing) was run first with the `xfail(strict=True)` decorator still in place.
Each produced `[XPASS(strict)]` -- a pytest-reported FAILURE, since `strict=True` treats an
unexpected pass as a test failure -- confirming the bucketing surfaced 0 resolved-and-wrong
before the decorator was removed. This is the safety net the plan names: "An XPASS under
strict=True is a failure, so any test left xfail'd that now passes will surface here rather than
silently."

## What changed

- `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`: five test bodies rewritten to
  bucket outcomes via `try/except OracleTimeoutError`; four `@pytest.mark.xfail` decorators
  removed; the fifth's `reason=` rewritten with counts and durable anchors, no task-number or
  `specs/` path citations.

## Verification

```
PYTHONPATH="code/src:$PYTHONPATH" pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py -q -m "not slow" -rxX
56 passed, 3 deselected in 271.81s (0:04:31)
```

`test_temporal_only_agreement_complexity_5` run separately (it is itself `slow`-marked):
`1 xfailed in 543.23s (0:09:03)` with the rewritten reason -- confirmed XFAIL, not XPASS.

`grep -n "task [0-9]\|baselines/differential-disposition"` returns nothing.

## Deviation from plan

The plan's verification command literally sets `PYTHONPATH=code/src`; this file's module-level
`_try_import_bimodal_harness()` inserts the BH path defensively at runtime (not a hard import
failure), so this particular deviation matters less here than in Phase 3, but
`PYTHONPATH="code/src:$PYTHONPATH"` was used consistently throughout for uniformity with the
rest of this task's verification commands.

## Next phase

Phase 7 (full-suite verification) depends on Phases 2, 3, and 6, all now complete. It is next,
and per the plan and the coordinator's instructions, its long scan runs go in the background with
a 90-minute abort rule -- unlike every prior phase's foreground, bounded verification.
