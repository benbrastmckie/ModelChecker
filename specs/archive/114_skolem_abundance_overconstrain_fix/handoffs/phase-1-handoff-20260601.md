# Phase 1 Handoff: Write Tests for New Behavior (TDD Red)

**Date**: 2026-06-01
**Status**: COMPLETED
**Phase**: 1 of 4

## Summary

Added TDD tests to `test_soundness_regression.py` defining expected post-fix behavior.

## Tests Added

Two new test classes appended to the file:

### TestGroundedDispatch
- `test_grounded_dispatch_at_m3`: verifies `build_grounded_abundance_constraints()` returns a non-empty list at M=3 -- PASSES (method already exists)
- `test_capped_dispatch_at_m2`: verifies `capped_skolem_abundance_constraint()` returns a single Z3 expression (not list) -- PASSES
- `test_m3_solver_no_timeout_on_atom`: verifies M=3 solves atom('p') without timeout -- will FAIL until Phase 2 fix

### TestOracleMFormulaBoundarySafe
- `test_oracle_m_formula_depth0_boundary_safe`: expects M=3, boundary_safe=True for depth-0 -- FAILS (current M=2)
- `test_oracle_m_formula_depth1_boundary_safe`: expects M=3, boundary_safe=True for depth-1 -- FAILS (current M=2)
- `test_oracle_m_formula_depth2_boundary_safe`: expects M=4, boundary_safe=True for depth-2 -- FAILS (current M=2)
- `test_gg_p_returns_countermodel_at_m4`: expects non-None for G(G(p)) at M=4 -- FAILS (current returns None)
- `test_fg_p_returns_countermodel_at_m4`: expects non-None for F(G(p)) at M=4 -- FAILS (current returns None)

## Deviations

None. All planned tests were added.

## Next Phase

Phase 2: Fix constraint dispatch in semantic.py (`build_frame_constraints()`) to use `build_grounded_abundance_constraints()` when M>=3 and handle list unpacking in the return statement.
