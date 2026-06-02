# Implementation Summary: Task #108

- **Task**: 108 - Soundness regression test suite for boundary and shift-closure edge cases
- **Status**: [COMPLETED]
- **Session**: sess_1780354243_1181c9
- **Date**: 2026-06-01

## Overview

Created `test_soundness_regression.py` with 22 passing tests and 1 expected xfail across 5 test classes targeting specific soundness gap points in the bimodal oracle.

## Artifacts Produced

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` (primary deliverable)
- `specs/108_soundness_regression_test_suite/plans/01_soundness-regression-plan.md` (updated, all phases COMPLETED)
- `specs/108_soundness_regression_test_suite/summaries/01_soundness-regression-summary.md` (this file)

## Test Classes and Results

### TestBoundaryVacuity (6 tests, all pass)
- `test_depth0_boundary_safe_is_true`: atom(A) at M=2, boundary_safe=True (2>1)
- `test_depth1_boundary_safe_is_false`: F(p) at M=2, boundary_safe=False (2>2 is False)
- `test_depth2_boundary_safe_is_false`: G(F(p)) at M=2, boundary_safe=False (2>3 is False)
- `test_gg_p_returns_none_at_m2`: G(G(p)) → None (spurious theorem at M=2)
- `test_fg_p_returns_none_at_m2`: F(G(p)) → None (spurious theorem at M=2, discovery)
- `test_depth1_countermodel_correct_despite_boundary_unsafe`: F(p) → non-None with all required fields

### TestShiftClosure (2 tests: 1 pass, 1 xfail)
- `test_shift_closure_trivial_at_m2`: Trivially satisfied at M=2 (no valid non-zero shifts)
- `test_shift_closure_on_extracted_worlds_m3`: XFAIL -- M=3 solver over-constraint documented

### TestGuardedCompositionality (6 tests, all pass)
- `test_forward_comp_in_oracle_output`: No forward_comp violations in oracle's task_relation
- `test_converse_in_oracle_output`: No converse violations in oracle's task_relation
- `test_nullity_in_oracle_output`: No nullity violations in oracle's task_relation
- `test_all_durations_in_valid_range`: All durations within [-(M-1), M-1]
- `test_forward_comp_with_temporal_formula_output`: All 3 axioms satisfied for F(p)
- `test_nullity_with_depth2_formula_output`: Nullity satisfied for G(F(p))

### TestStateIsolationRegression (4 tests, all pass)
- `test_100_calls_mixed_temporal_depths`: 100 calls (5-formula rotation) consistent
- `test_sat_unsat_interleaving_stability`: 50 pairs of G(F(p)) and A→A stable
- `test_temporal_propositional_interleaving`: 50 pairs of F(p) and atom(A) stable
- `test_no_semantics_reference_leak_with_temporal`: _semantics=None after each depth-2 call

### TestKnownBoundaryUnsafe (5 tests, all pass)
- `test_gg_p_spurious_unsat`: G(G(p)) → None (documented mechanism)
- `test_fg_p_spurious_unsat`: F(G(p)) → None (documented mechanism)
- `test_gf_p_genuine_countermodel`: G(F(p)) → non-None (correct result despite boundary)
- `test_ff_p_boundary_behavior`: F(F(p)) → non-None (boundary-influenced but valid)
- `test_imp_gg_p_gf_p_boundary_unsafe`: G(G(p))→G(F(p)) → non-None (compound interaction)

## Plan Deviations

- **F(G(p)) behavior**: Research predicted F(G(p)) would return non-None (spurious SAT) at M=2. Actual oracle behavior is None (spurious theorem), same as G(G(p)). Mechanism: ~F(G(p)) = G(~G(p)) is unsatisfiable at M=2 because ~G(p) at t=1 is vacuously false (G(p) at t=1 is vacuously true). Both `TestBoundaryVacuity.test_fg_p_returns_result_at_m2` and `TestKnownBoundaryUnsafe.test_fg_p_spurious_sat` were renamed and updated to assert the correct (None) oracle behavior. This is a net improvement: the test now documents a more surprising boundary vacuity pattern (both F(G(p)) and G(G(p)) return None).
- **Phase implementation**: All 5 phases were implemented in a single pass rather than sequentially, since all tests go in one file. No functional deviation from plan.
- **Shift closure at M=3**: As predicted by the plan, solver timeout/over-constraint at M=3 caused xfail. The xfail documents the known skolem_abundance over-constraint issue.

## Key Technical Findings

1. **Dual spurious theorem boundary pattern**: Both G(G(p)) and F(G(p)) exhibit the same M=2 boundary vacuity. The unifying mechanism: any formula whose inner G is evaluated at t=1 (the last future time point) is vacuously true. This includes both formulas whose inner G is in consequent position (G(G(p))) and whose inner G is in the existential witness position (F(G(p))).

2. **Frame axioms in serialized output**: All three TaskFrame axioms (nullity, converse, forward_comp) hold in the oracle's serialized task_relation dict. This confirms the serialization pipeline preserves the frame guarantees established by the Z3 frame constraints.

3. **State isolation with temporal depth**: 100+ sequential calls with mixed propositional, depth-1, and depth-2 formulas show no state leakage. The isolated_z3_context() and finally block cleanup work correctly for temporal formulas.

4. **Shift closure at M=2 is trivial**: At M=2, the time domain is {-1, 0, 1}. A world spanning all 3 points has no valid non-zero shifts within the domain, so shift closure is vacuously satisfied. This is the expected behavior, documented in the test.

## Verification Results

```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py -v
22 passed, 1 xfailed
```
