# Phase 1 Handoff: Test Infrastructure and Helpers

**Task**: 108  
**Phase**: 1  
**Status**: COMPLETED  
**Date**: 2026-06-01  

## Summary

Created `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` with:
- All imports (Z3OracleProvider, temporal_depth, BimodalSemantics, isolated_z3_context)
- JSON formula constants for 10 test formulas across depth-0, depth-1, depth-2
- 5 shared helper functions: `_task_rel_as_set`, `_check_forward_comp`, `_check_converse`, `_check_nullity`, `_check_shift_closure`

## Key Discovery

FG_P (F(G(p))) returns None at M=2, not non-None as originally predicted in research.
Mechanism: ~F(G(p)) = G(~G(p)) is unsatisfiable because ~G(p) at t=1 is vacuously false
(G(p) at t=1 is vacuously true over empty {t''>1}). Tests updated to reflect actual behavior.

## Collection Verified

`--collect-only` produces 23 tests with no import errors.

## Next Phase

Phases 2-5 were implemented in same pass. All 22 pass, 1 xfailed.
