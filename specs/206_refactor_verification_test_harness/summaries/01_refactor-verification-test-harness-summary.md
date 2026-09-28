# Implementation Summary: Refactor Verification Test Harness

- **Task**: 206 - Refactor Verification Test Harness
- **Plan**: `specs/206_refactor_verification_test_harness/plans/01_refactor-verification-test-harness.md`
- **Status**: COMPLETED (all 8 phases; Phase 7 COMPLETED WITH EXCLUSIONS -- not taken, gate found adequate)

## What Changed

**Organization**:
- New `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py`: the single shared
  `_settings`/`_build` pipeline-construction helper, replacing four byte-equivalent local copies
  in `test_certificate_a2_triangle.py`, `test_search_period_coverage.py`, `test_structure.py`,
  and `test_pinned_eval.py`. `test_structure.py` keeps a four-line local `_build` wrapper that
  defaults `'verify'` to `'off'` -- a real behavioral difference introduced by a concurrent task
  (205) after this plan was authored, preserved rather than silently reverted; documented in
  both modules' docstrings and in `tests/README.md`.
- Three declined reorganizations recorded in place, with reasons, in `tests/README.md`'s new
  "Declined Reorganizations" section: the three grids stay separate (each pins an independent
  property); tier-gating mechanics (prose + `slow` marker + `skipif`) are unchanged (three
  distinct mechanisms, not one restated fact); `_pinned_eval.py` stays inside `tests/` (matches
  `_lean_check.py`'s own precedent), with a coordination note on where it would move if a future,
  separately-tracked trust-boundary decision promotes a checker onto the production path.

**Performance** (the primary deliverable):
- `semantic/certificate.py`: pure extract-method split of `recheck()` into `_recheck_family`
  (the target-time-independent structural/(C1)/(C2)/(C3) legs) and the unchanged `recheck()` as
  a thin composition with (C4). Guarded by a new equivalence test covering all five failure
  classes plus an accepting candidate.
- `tests/_pinned_eval.py`: `PinnedAssignmentBuilder` partitions its entries into family-only
  (`lab_`/`bx_`) and target-time (`sel_`) groups at construction time, exposing `base_row(family)`
  and `apply_target(row, family, target_time)`; `assign()` is unchanged behaviorally, now
  implemented as `base_row` + `apply_target`.
- `tests/integration/test_certificate_a2_triangle.py`: `_candidates` became `_families`, yielding
  one `(family, target_window)` per family instead of flattening to `(family, target_time)` per
  candidate -- the harness's own enumeration now explicitly amortizes each family's
  target-time-independent work once, in both `_run_exhaustive_triangle` and `_sampled_candidates`.
  Every candidate is still individually counted and compared; nothing is skipped, no stride
  introduced, no count changed.

## Measured Results (CI's exact invocation shape, same host)

| Case | Candidates | Before | After | Reduction |
|---|---|---|---|---|
| Widest boxed (`nb=nf=2`) | 10,485,760 | 121.78s | **33.90s** | 72.2% (3.59x) |
| Second boxed | 1,572,864 | 17.93s | **7.14s** | 60.2% (2.51x) |

Both exceed the research report's 70.9%/3.43x script-level projection. Headroom against the 300s
per-test ceiling improved from ~59% (2.4x CI-hardware slowdown tolerance) to **88.7% (8.85x)**.
All three counts (`total`/`accepted`/`pinned_accepted`) are bit-for-bit identical to the
pre-refactor baseline for both boxed cases.

**Decision (Phase 6 gate)**: Adequate. The scheduled-run contingency (Phase 7) was not taken;
closed `[COMPLETED WITH EXCLUSIONS]` citing this measurement.

## Preserved Invariants

All six invariants named in the dispatch/plan are confirmed intact -- see the baseline record's
"Final Verification (Phase 8)" section for citations: Tier 2's clean-skip/pass-for-real
discipline (untouched file, confirmed via `git log`); the `timeout is False` assertions
(byte-identical in the full diff); the retained aggregate SAT/UNSAT assertion (byte-identical);
the first-divergence raise with both attribution branches (scratch-verified); `_sampled_candidates`
selection determinism (directly compared against the pre-change module); and the
`len(closure) <= 4` bound (byte-identical, still asserted on every call).

## Verification

- Bimodal suite (including `slow`): 640 passed, 68.90s.
- Four-theory gate: 645 passed, 5 skipped, 50.42s.
- Repository-wide target set, CI's exact shape: parallel pass 3143 passed / 1 skipped / 1 failed
  (106.79s); serial pass 10 passed (2.45s).
- The one failure (`test_checker.py::TestLazyBoundedMemoizedProbe::test_import_performs_no_subprocess_call`)
  is a pre-existing, out-of-scope, `-n 4`-contention-sensitive flake in a module owned entirely by
  a concurrent task's commits (task 205/197), confirmed passing standalone in every measurement
  round this task took (baseline, post-refactor, and final verification) -- not a regression from
  this task.
- No task-number reference introduced in any file this task touched under `code/`.

## Plan Deviations

- **`test_structure.py`'s local `_build` wrapper** (Phase 2): task 205 landed on this working
  tree between this plan's authoring and its execution, adding a `'verify': 'off'` default to
  `test_structure.py`'s `_settings` for determinism (item 1's output gate). This broke the
  plan's "byte-equivalent apart from annotations" assumption for one of the four call sites.
  Resolution: the shared `_build_support.py` carries the annotated form (matching the other
  three call sites); `test_structure.py` keeps a four-line local wrapper defaulting `'verify'`
  to `'off'` before delegating to the shared helper, preserving task 205's fix rather than
  silently reverting it. Documented in both modules and in `tests/README.md`.
- **Scope boundary confirmed, not expanded** (Phase 2): the mechanical
  `grep -rn "^def _settings\|^def _build"` check found seven further modules with their own,
  independent `_settings`/`_build`-shaped helpers, none named by the dispatch's ORGANIZATION
  paragraph or this plan's Scope Hypothesis. Left untouched, out of this task's declared scope;
  recorded in `tests/README.md` for a future task.
- **Baseline re-measured against the current tree** (Phase 1): task 205 also landed additional
  commits while this task's own Phase 1 baseline was being recorded. The baseline file records
  both the pre-205 and post-205 measurements; the post-205 measurement is the one Phase 6
  compares against, since it reflects the tree Phase 2 onward actually edited.
- No other deviations. Every other item in the plan was implemented as written.

## Files Changed

- `code/src/model_checker/theory_lib/bimodal/tests/_build_support.py` (new)
- `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py`
- `code/src/model_checker/theory_lib/bimodal/tests/README.md`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_certificate.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py`
- `specs/206_refactor_verification_test_harness/baselines/01_ci-shaped-baseline.md` (new)
