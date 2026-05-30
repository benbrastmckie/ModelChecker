# Implementation Summary: Frame Constraints (nullity, compositionality, converse)

- **Task**: 92 - Add frame constraints for bimodal task relation
- **Status**: [COMPLETED]
- **Started**: 2026-05-29T00:00:00Z
- **Completed**: 2026-05-29T00:20:00Z
- **Effort**: ~30 minutes (all 3 phases)
- **Dependencies**: 91 (ternary task relation refactor, completed)
- **Artifacts**: plans/01_frame-constraints-plan.md, summaries/01_frame-constraints-summary.md
- **Standards**: status-markers.md, artifact-management.md, tasks.md

## Overview

Implemented three frame constraints for the bimodal task relation in `semantic.py` that align with the Lean ProofChecker's `TaskFrame` axioms and `Compositional` typeclass from `Frame.lean`. The constraints are `nullity_identity` (zero-duration tasks relate a state to itself), `converse` (time-reversal symmetry), and `forward_comp` (compositionality of sequential tasks). All three builder methods were added to `BimodalSemantics` and integrated into `build_frame_constraints()`, along with a dedicated test file with 8 tests across 4 test classes.

## What Changed

- `code/src/model_checker/theory_lib/bimodal/semantic.py` -- Added three new builder methods (`build_nullity_identity_constraint()`, `build_converse_constraint()`, `build_forward_comp_constraint()`) and integrated all three into the `build_frame_constraints()` return list. Frame constraint count increased from 9 to 12.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py` -- Created new test file with `TestNullityIdentity`, `TestConverse`, `TestForwardComp`, and `TestConstraintInteractions` test classes (8 tests total).

## Decisions

- Implemented `forward_comp` alongside Phases 1 and 2 in a single pass since all three methods were needed simultaneously in `build_frame_constraints()`.
- Used `z3.MultiPattern(task_rel(w, d1, v), task_rel(v, d2, u))` in `build_forward_comp_constraint()` to guide Z3 quantifier instantiation and reduce solver overhead from the 5-variable quantifier.
- Used `N=2` (4 states) in test fixtures instead of `N=3` (8 states) to avoid solver timeout with the `skolem_abundance_constraint` + all frame axioms combined.
- Left `task_restriction` (currently commented out) disabled, following the research recommendation that `forward_comp` may derive `task_rel` values not directly witnessed by world histories.

## Impacts

- The bimodal semantics now enforces three additional TaskFrame axioms that align with the Lean ProofChecker's `Frame.lean` formalization.
- Any solver query involving `task_rel` now carries three additional quantified formulas. For N=2, M=2, solver time remains under 0.5s per test.
- All 12 existing (non-timeout) bimodal tests continue to pass unchanged.

## Plan Deviations

- **Phase 2.1** (altered): `build_forward_comp_constraint()` was implemented in Phase 1 alongside the other two methods since `build_frame_constraints()` integration required all three simultaneously. No separate Phase 2 implementation step was needed.
- **Phase 3.1** (altered): Test fixture changed from N=3 to N=2 to prevent solver timeout in `TestConstraintInteractions` tests when all frame constraints (including `skolem_abundance_constraint`) are loaded together.

## Verification

- Build: N/A (Python module, no compile step)
- Tests: 8 new tests pass, 12 original tests continue to pass
- Files verified: Both modified/created files confirmed present and non-empty
- Frame constraints: `solver.check()` on full constraint set returns `sat` in ~0.25s (N=2, M=2)

## References

- `specs/092_add_frame_constraints_nullity_comp_converse/plans/01_frame-constraints-plan.md`
- `specs/092_add_frame_constraints_nullity_comp_converse/reports/01_frame-constraints-research.md`
- `code/src/model_checker/theory_lib/bimodal/semantic.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py`
