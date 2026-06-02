# Implementation Plan: Task #108

- **Task**: 108 - Soundness regression test suite for boundary and shift-closure edge cases
- **Status**: [IMPLEMENTING]
- **Effort**: 3 hours
- **Dependencies**: 103 (OracleProvider implementation -- completed)
- **Research Inputs**: specs/108_soundness_regression_test_suite/reports/01_soundness-regression.md
- **Artifacts**: plans/01_soundness-regression-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Create `test_soundness_regression.py` with five test classes targeting specific soundness gap points in the bimodal oracle. The research report identified concrete coverage gaps: boundary vacuity at M=2 for depth-2 formulas (G(G(p)) returns None spuriously), untested shift closure of extracted world histories, untested frame axioms on the oracle's serialized output (only raw Z3 model tested), state isolation limited to propositional formulas, and no hand-crafted boundary-unsafe formula suite. All tests go in a single file with shared helpers and JSON formula constants.

### Research Integration

Key findings from `reports/01_soundness-regression.md` integrated into this plan:

1. **G(G(p)) is the prime boundary-unsafe formula** -- oracle returns None at M=2 (spurious theorem), should return non-None at M=4. The test documents this as a known limitation and asserts `boundary_safe=False`.
2. **Shift closure tests require M>=3** -- at M=2 the only valid shift for a world spanning {-1,0,1} is delta=0 (trivial). Tests must use BimodalSemantics directly with M=3, bypassing the oracle's M=max(depth,2).
3. **Oracle's serialized task_relation is NOT tested against frame axioms** -- existing `test_frame_class_mapping.py` tests raw Z3 model, not the public oracle output dict. Phase 3 tests the serialized list.
4. **State isolation uses only 4 propositional formulas** -- must add depth-1 and depth-2 temporal formulas to the rotation (5+ formulas total).
5. **All 5 boundary-unsafe formulas designed** with expected oracle outcomes documented.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items found (template only).

## Goals & Non-Goals

**Goals**:
- Create a comprehensive soundness regression test suite in a single file
- Cover all 5 test categories from the task description
- Document known boundary-unsafe behavior (G(G(p)) at M=2) via test assertions
- Test oracle public output (task_relation list), not internal Z3 model
- Ensure state isolation covers temporal depth-1 and depth-2 formulas

**Non-Goals**:
- Fixing the M=max(depth,2) deviation in provider.py (that is a separate task)
- Duplicating tests already covered by test_boundary_regression.py or test_oracle_provider.py
- Testing BimodalHarness integration (that is task 109)
- Implementing dynamic M=max(depth+2,3) correction

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Shift closure tests with M=3 hit solver timeout from skolem_abundance over-constraint | M | M | Use small N (N=2) and short timeout; skip test with xfail if solver consistently times out |
| G(G(p)) oracle behavior changes if provider.py M formula is updated | L | L | Tests document current behavior; update assertions if M formula changes |
| State isolation 100+ calls slow in CI | L | M | Use lightweight formulas for bulk calls; deeper formulas only in targeted interleave test |
| BimodalSemantics direct construction for shift closure test is fragile | M | L | Follow exact pattern from test_frame_class_mapping.py fixture |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Test infrastructure and helpers [COMPLETED]

**Goal**: Create the test file with imports, JSON formula constants, and shared helper functions.

**Tasks**:
- [ ] Create `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py`
- [ ] Add imports: `Z3OracleProvider` from `bimodal_logic`, `temporal_depth` from `bimodal_logic.translation`, `BimodalSemantics` from `model_checker.theory_lib.bimodal.semantic`, `isolated_z3_context` from `model_checker.utils.context`, `z3`, `pytest`
- [ ] Define JSON formula constants for all 17 test formulas:
  - Depth-0: `ATOM_A` (SAT), `TAUTOLOGY` (A->A, UNSAT/valid)
  - Depth-1: `F_P` (some_future(atom(p)), SAT), `G_TAUT` (all_future(A->A), UNSAT/valid)
  - Depth-2: `FG_P`, `GG_P`, `GF_P`, `FF_P`, `G_IMP_FG` (G(p)->F(G(p)))
- [ ] Implement `_task_rel_as_set(task_relation)` helper: converts list of {source, duration, target} dicts to set of tuples
- [ ] Implement `_check_forward_comp(task_relation, M)` helper: returns list of compositionality violations
- [ ] Implement `_check_converse(task_relation, M)` helper: returns list of converse axiom violations
- [ ] Implement `_check_nullity(task_relation)` helper: returns list of nullity violations
- [ ] Implement `_check_shift_closure(world_histories, M)` helper: verifies shift closure on extracted world histories
- [ ] Run file with `pytest --collect-only` to verify no import errors

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` - create new file

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py --collect-only` succeeds with 0 tests collected (helpers only, no test functions yet)

---

### Phase 2: Boundary vacuity tests [COMPLETED]

**Goal**: Test that the oracle correctly flags boundary-unsafe formulas and that boundary vacuity artifacts are documented.

**Tasks**:
- [ ] Create `TestBoundaryVacuity` class
- [ ] `test_depth0_boundary_safe_is_true`: atom(A) with oracle, verify `result["boundary_safe"] is True`
- [ ] `test_depth1_boundary_safe_is_false`: F(p) depth=1, verify `boundary_safe=False` (M=2, depth=1: 2 > 2 is False)
- [ ] `test_depth2_boundary_safe_is_false`: GG(p) depth=2, verify `boundary_safe=False`
- [ ] `test_gg_p_returns_none_at_m2`: G(G(p)) with oracle returns None (spurious UNSAT -- the prime boundary artifact). Document this is a known limitation with a comment explaining the vacuity mechanism.
- [ ] `test_fg_p_returns_result_at_m2`: F(G(p)) with oracle returns non-None (spurious SAT due to vacuous G at t=1). Verify `boundary_safe=False`.
- [ ] `test_depth1_countermodel_correct_despite_boundary_unsafe`: F(p) at M=2 returns non-None with correct countermodel (p false at all times). Verify result contains expected fields.
- [ ] Run tests, all must pass

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` - add TestBoundaryVacuity class

**Verification**:
- All `TestBoundaryVacuity` tests pass
- `boundary_safe` flag values match research predictions

---

### Phase 3: Shift closure and guarded compositionality tests [COMPLETED]

**Goal**: Test that extracted countermodels satisfy shift closure and that the oracle's serialized task_relation satisfies frame axioms (nullity, converse, forward_comp).

**Tasks**:
- [ ] Create `TestShiftClosure` class
- [ ] `test_shift_closure_on_extracted_worlds_m3`: Use a SAT formula, construct BimodalSemantics directly with M=3, extract world_histories, verify shift closure using `_check_shift_closure` helper. If M=3 causes solver timeout, mark test with `@pytest.mark.xfail(reason="M=3 skolem_abundance over-constraint")`.
- [ ] `test_shift_closure_trivial_at_m2`: Use oracle (M=2) for a SAT formula, verify shift closure is trivially satisfied (no non-zero valid shifts for world spanning full domain)
- [ ] Create `TestGuardedCompositionality` class
- [ ] `test_forward_comp_in_oracle_output`: Call oracle with a SAT formula (e.g., negation of a complex formula), extract `task_relation` from result, run `_check_forward_comp`, assert no violations
- [ ] `test_converse_in_oracle_output`: Same SAT result, run `_check_converse`, assert no violations
- [ ] `test_nullity_in_oracle_output`: Same SAT result, run `_check_nullity`, assert no violations (task_rel(s, 0, u) iff s=u)
- [ ] `test_all_durations_in_valid_range`: All durations in task_relation are within [-(M-1), M-1]
- [ ] Run tests, all must pass

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` - add TestShiftClosure and TestGuardedCompositionality classes

**Verification**:
- All shift closure and compositionality tests pass
- No frame axiom violations found in oracle output

---

### Phase 4: State isolation with temporal depth-2 formulas [COMPLETED]

**Goal**: Verify that 100+ sequential oracle calls with a mix of propositional, depth-1, and depth-2 formulas show no state leakage or cross-contamination.

**Tasks**:
- [ ] Create `TestStateIsolationRegression` class
- [ ] Define 5-formula rotation: depth-0 SAT (atom(A)), depth-0 UNSAT (A->A), depth-1 SAT (F(p)), depth-1 UNSAT (G(A->A)), depth-2 SAT (G(F(p)))
- [ ] `test_100_calls_mixed_temporal_depths`: Run 100 sequential calls cycling through the 5 formulas (20 calls each), assert each call returns the expected SAT/UNSAT classification consistently
- [ ] `test_sat_unsat_interleaving_stability`: Alternate between a depth-2 SAT formula and a depth-0 UNSAT formula for 50 pairs, verify every SAT call returns non-None and every UNSAT call returns None
- [ ] `test_temporal_propositional_interleaving`: Alternate between F(p) (SAT, temporal) and atom(A) (SAT, propositional) for 50 pairs, verify both always return non-None
- [ ] `test_no_semantics_reference_leak_with_temporal`: Run 10 calls with depth-2 formulas, verify `provider._semantics is None` after each call
- [ ] Run tests, all must pass

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` - add TestStateIsolationRegression class

**Verification**:
- All 4 state isolation tests pass
- 100+ sequential calls complete without assertion failures

---

### Phase 5: Known-boundary-unsafe formula suite [COMPLETED]

**Goal**: Create 5 hand-crafted formulas with temporal_depth >= 2 and verify the oracle's behavior matches documented expectations for each.

**Tasks**:
- [ ] Create `TestKnownBoundaryUnsafe` class with detailed docstrings explaining each formula's boundary behavior
- [ ] `test_gg_p_spurious_unsat`: G(G(p)) depth=2 -- oracle returns None at M=2 (spurious theorem). Assert `boundary_safe=False`. Document: "G(G(p)) at t=0 with M=2: outer G checks t'=1 only; inner G(p) at t'=1 is vacuously true (no t''>1 in domain). So oracle finds no countermodel to G(G(p)), treating it as valid -- but G(G(p)) IS invalid (p can be false at t=3 with M=4)."
- [ ] `test_fg_p_spurious_sat`: F(G(p)) depth=2 -- oracle returns non-None at M=2 (G(p) at t=1 vacuously true makes F(G(p)) trivially SAT). Assert `boundary_safe=False`, result non-None.
- [ ] `test_gf_p_genuine_countermodel`: G(F(p)) depth=2 -- oracle returns non-None at M=2 (genuine countermodel: F(p) at t=1 fails because no t''>1 in domain). Assert `boundary_safe=False`, result non-None. This is a correct result despite boundary_safe=False.
- [ ] `test_ff_p_boundary_behavior`: F(F(p)) depth=2 -- oracle at M=2: F(F(p)) at t=0 needs t'>0 with F(p) at t'. At t'=1: F(p) needs t''>1, none in domain. Countermodel exists (correct). Assert `boundary_safe=False`, result non-None.
- [ ] `test_imp_gg_p_gf_p_boundary_unsafe`: (G(G(p)) -> G(F(p))) depth=2 -- compound formula testing boundary interaction of two depth-2 subformulas. Assert `boundary_safe=False`. Document expected behavior.
- [ ] Add gate verification: run full test suite to confirm no regressions
- [ ] Run: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py -v`

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` - add TestKnownBoundaryUnsafe class

**Verification**:
- All 5 boundary-unsafe formula tests pass
- All tests in the file pass: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py -v`
- Full bimodal suite passes: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`

## Testing & Validation

- [ ] All tests in `test_soundness_regression.py` pass
- [ ] No regressions in existing bimodal test suite
- [ ] Each test class independently executable: `pytest -v -k TestBoundaryVacuity`, etc.
- [ ] `boundary_safe` flag values match research predictions for all depth levels
- [ ] Frame axiom checks (nullity, converse, forward_comp) find no violations in oracle output
- [ ] State isolation passes with 100+ sequential calls using mixed temporal depths
- [ ] All 5 known-boundary-unsafe formulas document expected oracle behavior

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` - the test file (primary deliverable)
- `specs/108_soundness_regression_test_suite/plans/01_soundness-regression-plan.md` - this plan
- `specs/108_soundness_regression_test_suite/summaries/01_soundness-regression-summary.md` - implementation summary (created during implementation)

## Rollback/Contingency

- The implementation creates a single new test file with no modifications to existing code. Rollback is trivial: delete `test_soundness_regression.py`.
- If shift closure tests at M=3 consistently timeout, mark with `@pytest.mark.xfail` and document the skolem_abundance over-constraint issue.
- If oracle behavior for any formula differs from research predictions, update the test assertion and add a comment explaining the discrepancy.
