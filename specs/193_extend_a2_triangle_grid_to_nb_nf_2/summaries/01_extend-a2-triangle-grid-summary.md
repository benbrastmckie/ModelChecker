# Implementation Summary: Extend the A2-triangle exhaustive grid to nb=nf=2

- **Task**: 193 - Extend the A2-triangle encoding-completeness test's exhaustive grid beyond back=mid=fwd=1 to cover nb=nf=2
- **Status**: [COMPLETED]
- **Started**: 2026-09-26T00:00:00Z
- **Completed**: 2026-09-26T18:59:34Z
- **Effort**: ~4 hours
- **Dependencies**: None
- **Artifacts**: plans/01_extend-a2-triangle-grid.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`tests/integration/test_certificate_a2_triangle.py`'s Tier 1 exhaustive enumeration was pinned to
`back = mid = fwd = 1`, which cannot see the one A2 violation known to have actually occurred (a
narrow-window local-coherence defect requiring `nb = 2` to manifest). This task generalized the
candidate generator and closed-form count to arbitrary `nb`/`nm`/`nf`, then added
`back = 2, mid = 1, fwd = 2` (production's `DEFAULT_EXAMPLE_SETTINGS`) grid points: two box-free
closures unconditionally, and one size-2 box-carrying closure under the existing `slow` marker,
selected by an implementation-time measurement gate. All work stayed inside
`test_certificate_a2_triangle.py` and `docs/ADEQUACY.md` section 7.3; no production code changed.

## What Changed

- `_candidates()`: segment construction generalized from hard-coded single-element tuples
  (`back=(back_label,)`) to `itertools.product(labels, repeat=nb)` / `repeat=nm` / `repeat=nf`,
  reading `nb`/`nm`/`nf` from `semantics.witness_registry`. At `nb=nm=nf=1` this reduces to
  exactly the previous construction (verified: all three pre-existing closures' expected counts
  unchanged).
- `_expected_candidate_count()`: exponent generalized from the literal `3` to
  `witness_registry.slots_per_lasso` (`= nb+nm+nf`), with a comment naming the
  `target_window_len == slots_per_lasso == nb+nm+nf` identity the previous code relied on
  silently.
- `_assert_exhaustive_triangle_agrees()` and `TestExhaustiveTriangleBoxFree`'s parametrize
  signature now take `back`/`mid`/`fwd`; every pre-existing case passes `1, 1, 1` explicitly.
- Two new unconditional (non-`slow`) box-free `nb=nf=2` cases added to
  `TestExhaustiveTriangleBoxFree`:
  - `box_free_until_conclusion_sat_nb2_nf2` (`[] |- (q \Until p)`, closure size 3): measured
    **163,840 candidates / 926 accepted / SAT / 1.06s** — matches research's prediction exactly.
  - `box_free_contradiction_unsat_nb2_nf2` (`["A"] |- ["A"]`, closure size 1): measured
    **160 candidates / 0 accepted / UNSAT / ~0s**.
- One new `slow`-marked box-carrying `nb=nf=2` case added to `TestExhaustiveTriangleWithBox`:
  `test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2` (`[] |- [\Box A]`, closure size 2):
  measured **10,485,760 candidates / 5,115 accepted / SAT / ~64-78s** (idle-host isolated run:
  64.30s; inside the full-suite run: 69.69s; inside the CI-timeout-shaped module-only run:
  78.28s — all comfortably under the 300s per-test ceiling).
- The pre-existing size-3 boxed closure (`\Box A |- B`) is untouched, still `back=mid=fwd=1`-only,
  per the task's explicit Non-Goal (its `nb=nf=2` enumeration is ~10.7 billion candidates, ~19h
  extrapolated — documented as infeasible, not attempted).
- Module docstring and `ADEQUACY.md` section 7.3's "Deciding test for A2" paragraph updated to
  describe both grid sizes, why `nb=2` matters, and the standing size-3 coverage gap.

## Decisions

- **Measurement gate (Phase 3)**: two closure-size-2 boxed candidates were measured directly
  before selecting one: `[] |- [\Box A]` (candidate A: SAT, 5,115 accepted, 64.52s) and
  `[\Box A] |- [A]` (candidate B: UNSAT, 0 accepted, 67.09s — matches research's prediction for
  this formula closely). Both passed the gate (closure size 2, wall clock <= 100s); candidate A
  was selected because SAT additionally exercises the extracted-certificate `recheck` leg that
  `_assert_exhaustive_triangle_agrees` only runs when `expected_sat` is true. The one-sided
  `back=2, mid=1, fwd=1` contingency branch was not needed.
- Every new case's expected `total`/`accepted`/`z3_model_status` was pinned from the test's own
  run output (never copied blind from the research report), and cross-checked against
  `_expected_candidate_count()`'s independent closed form via the existing triple assertion.

## Plan Deviations

- None (implementation followed plan). Phase 3's contingency branch (one-sided
  `back=2, mid=1, fwd=1`) was documented but not exercised, since candidate A passed the gate
  outright — this is the plan's own documented "no contingency needed" path, not a deviation.

## Impacts

- No production code (`witness_constraints.py`, `witness_registry.py`, `certificate.py`,
  `core.py`) was touched.
- Total added wall clock for `test_certificate_a2_triangle.py`: ~1.06s (two box-free `nb=nf=2`
  cases) + ~64-78s (one boxed `nb=nf=2` case) — module total rose from a documented ~11s (Tier 1
  boxed) baseline to 9 tests / 147.44s under the CI-timeout-shaped run.
- Full bimodal suite: **441 passed in 150.46s** (`pytest code/src/model_checker/theory_lib/bimodal -q --durations=15`), no regressions in any other test's duration.
- Module alone under CI's exact timeout shape (`--timeout=300 --timeout-method=thread`): **9
  passed in 147.44s**, slowest single test 78.28s — no per-test breach of the 300s ceiling.
- No genuine three-way disagreement surfaced at `nb=nf=2` for any closure — every
  `_assert_exhaustive_triangle_agrees` triple-comparison assertion passed in both runs. **No
  finding to report**; this task adds forward regression coverage, consistent with research
  Finding 5 (the narrow-window defect is already fixed).
- `TestBoundedLeanCrossCheck` (Tier 2) confirmed untouched: `git diff` over the task's commit
  range shows every hunk ending before the Tier 2 section banner, and the class still carries
  `@pytest.mark.skipif(SKIP_REASON is not None, ...)`.

## Follow-ups

- None. The size-3 boxed closure's standing `nb=nf=2` coverage gap is now documented in both the
  module docstring and `ADEQUACY.md` section 7.3 as a permanent limitation (not a TODO), per the
  task's explicit Non-Goals.

## References

- `specs/193_extend_a2_triangle_grid_to_nb_nf_2/plans/01_extend-a2-triangle-grid.md`
- `specs/193_extend_a2_triangle_grid_to_nb_nf_2/reports/01_extend-a2-triangle-grid.md`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` (section 7.3)
