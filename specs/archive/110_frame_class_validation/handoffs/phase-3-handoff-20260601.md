# Phase 3 Handoff: Write Post-Hoc Frame Axiom Validation Tests

**Task**: 110
**Phase**: 3
**Status**: COMPLETED
**Timestamp**: 2026-06-01

## What Was Done

Added 5 test classes to `test_frame_class_mapping.py`:

1. **TestNullityIdentityPostHoc** (2 tests):
   - `test_no_zero_duration_between_distinct_states` - Checks no (s, 0, u) pair with s != u exists
   - `test_every_state_has_zero_duration_self_task` - Checks all states have (s, 0, s) pair

2. **TestConversePostHoc** (1 test):
   - `test_converse_holds_for_all_pairs` - For each (s, d, u) in model, checks (u, -d, s) present (within valid duration bounds)

3. **TestForwardCompPostHoc** (1 test):
   - `test_forward_composition_holds` - For all composable pairs (s,d1,v) and (v,d2,u) where d1+d2 is valid, checks (s, d1+d2, u) present

4. **TestLawfulHistoryPostHoc** (1 test):
   - `test_consecutive_states_have_unit_task_rel` - For all consecutive time pairs in world histories, checks task_rel(state_t, 1, state_t+1) present

5. **TestFrameClassDeclarationConsistency** (4 tests):
   - `test_base_means_taskframe_axioms_not_frameclassbase` - Verifies Z3OracleProvider has supported_frame_classes attribute
   - `test_three_taskframe_axioms_present_in_frame_constraints` - Frame constraints are satisfiable (consistent)
   - `test_nullity_axiom_enforced_in_frame` - task_rel(0, 0, 1) with nullity in frame is unsat
   - `test_converse_axiom_enforced_in_frame` - One-way task with negated converse is unsat

## Verification

- All 13 tests: PASSED in 8.82s
- Test count: 13 (4 smoke + 2 nullity + 1 converse + 1 forward_comp + 1 lawful + 4 frame-class)
- TestFixtureSmoke confirms fixtures produce non-empty data
- Post-hoc tests confirm all three TaskFrame axioms hold in extracted models
