# Implementation Plan: Boundary Effect Analysis and temporal_depth Mitigation

- **Task**: 107 - Boundary effect analysis and temporal_depth mitigation
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: 102 (completed)
- **Research Inputs**: specs/107_boundary_temporal_depth_mitigation/reports/01_boundary-depth-mitigation.md
- **Artifacts**: plans/01_boundary-depth-mitigation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

This plan delivers the formal boundary effect analysis and regression testing for the finite time domain problem in BimodalSemantics. The research report established that `temporal_depth()` is already complete (task 102) and that the boundary claim "M >= d+2 prevents spurious countermodels" is sound. The implementation work is: (1) documenting the boundary claim as code-level docstrings in `translation.py` and `semantic.py`, (2) creating a boundary-regression test file with hand-crafted formulas that demonstrate boundary vacuity at insufficient M and correct behavior at sufficient M, (3) creating a dedicated 43-example regression test verifying all active examples produce correct SAT/UNSAT results, and (4) running gate validation. No Z3 constraint changes are made to BimodalSemantics -- the research report explicitly recommends against this, as dynamic M belongs in OracleProvider (task 103).

### Research Integration

Key findings from the research report integrated into this plan:

- **temporal_depth() is complete**: Implemented in `translation.py` lines 183-252 by task 102, with 26 test cases covering all 17 tags. No additional implementation needed.
- **Boundary claim proven**: For formulas of temporal depth d evaluated at t=0 with M >= d+2, boundary effects cannot create spurious countermodels. The formal argument is in research report Section 3.
- **Do NOT add Z3 constraints**: Adding Z3 boundary buffer constraints to BimodalSemantics would break existing examples that use specific M values for computational efficiency. The correct implementation point for dynamic M is OracleProvider (task 103).
- **43 examples currently pass**: 10 SAT (countermodel) + 33 UNSAT (theorem), all producing correct results today. Many use M values that do not satisfy M >= d+2 but still produce correct results because the boundary vacuity for those specific formulas does not create spurious models.
- **Concrete boundary example**: `F(G(p))` with depth 2 and M=2 produces spurious satisfaction (G(p) vacuously true at t=1). With M=4, G(p) is genuinely checked.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Document the formal boundary claim as code-level docstrings in `temporal_depth()` and `ForAllTime()`/`is_valid_time()`
- Create hand-crafted boundary-unsafe formula tests demonstrating the boundary effect with insufficient M and correct behavior with sufficient M
- Create a dedicated regression test verifying all 43 active examples produce correct SAT/UNSAT results
- Validate that `temporal_depth()` handles all 17 JSON formula tags correctly (already done, but explicitly gate-checked)

**Non-Goals**:
- Adding Z3 constraints to BimodalSemantics (research recommends against this)
- Implementing dynamic M in OracleProvider (task 103 scope)
- Modifying any operational code in semantic.py or operators.py
- Re-implementing or modifying `temporal_depth()` (it is complete and tested)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Boundary-unsafe test formulas produce non-deterministic Z3 results | M | L | Use `isolated_z3_context()` for each test, keep M values well-separated from boundary |
| F(G(p)) boundary test at M=2 may not produce the expected spurious SAT due to Z3 optimization | M | M | Test multiple formulas (F(G(p)), G(G(p)), H(F(p))), document which demonstrate boundary vacuity |
| 43-example regression test may be slow (some examples use large N/M) | L | L | Set per-test timeout of 60s, exclude known-timeout examples as the existing suite does |
| Docstring additions accidentally change function behavior | L | L | Only modify docstrings/comments, run full test suite after each documentation edit |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Boundary Claim Documentation [COMPLETED]

**Goal**: Add the formal boundary argument as code-level documentation in the key functions.

**Tasks**:
- [ ] Add boundary claim docstring to `temporal_depth()` in `code/src/bimodal_logic/translation.py` -- include the formal argument: "For formulas of temporal depth d evaluated at t=0 with M >= d+2, boundary effects cannot create spurious countermodels. The key invariant is M - 1 - t >= d for evaluation at time t; at t=0 this requires M >= d+1. For strict safety (no vacuous truth at any reachable sub-evaluation point), M >= d+2 is required."
- [ ] Add boundary context docstring to `ForAllTime()` in `code/src/model_checker/theory_lib/bimodal/semantic.py` -- document that ForAllTime quantifies over the full domain D = (-M, M) and that boundary vacuity occurs when a formula of depth d is evaluated at t = M-1 (no future time points exist)
- [ ] Add boundary context comment to `is_valid_time()` in `semantic.py` -- document the domain structure: open interval (-M, M) giving 2*M-1 integer time points, and note that M >= d+2 ensures d+1 future time points from t=0
- [ ] Run existing test suite to verify documentation-only changes cause no regressions: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `code/src/bimodal_logic/translation.py` -- extend `temporal_depth()` docstring with boundary claim
- `code/src/model_checker/theory_lib/bimodal/semantic.py` -- extend `ForAllTime()` and `is_valid_time()` docstrings with boundary context

**Verification**:
- All existing tests pass with no changes in behavior
- `temporal_depth()` docstring contains the formal boundary argument
- `ForAllTime()` docstring explains the boundary vacuity mechanism

---

### Phase 2: Boundary-Unsafe Formula Tests [NOT STARTED]

**Goal**: Create `test_boundary_regression.py` with hand-crafted formulas that demonstrate boundary vacuity with insufficient M and correct behavior with M = max(depth+2, 3).

**Tasks**:
- [ ] Create test file `code/src/model_checker/theory_lib/bimodal/tests/unit/test_boundary_regression.py`
- [ ] Write test helper function that runs a formula string through the existing pipeline at a given N and M, returning whether a countermodel was found (SAT) or not (UNSAT)
- [ ] Write `test_temporal_depth_dynamic_m_formula()` -- parametric test verifying max(d+2, 3) for d in 0..4 produces the expected M values: d=0->3, d=1->3, d=2->4, d=3->5, d=4->6
- [ ] Write `test_fg_boundary_vacuity_insufficient_m()` -- F(G(p)) at M=2: G(p) at t=1 should be vacuously true. Document whether Z3 returns SAT (boundary artifact) or UNSAT. This test documents the boundary effect rather than asserting a specific result, since the overall formula result depends on Z3's handling of vacuous universals.
- [ ] Write `test_fg_correct_with_sufficient_m()` -- F(G(p)) at M=4 (d=2, M>=d+2=4): verify the formula produces a genuine (non-vacuous) result
- [ ] Write `test_gg_boundary_insufficient_m()` -- G(G(p)) at M=2 (d=2, need M>=4): document boundary behavior
- [ ] Write `test_gg_correct_with_sufficient_m()` -- G(G(p)) at M=4: verify genuine result
- [ ] Write `test_hf_boundary_formulas()` -- H(F(p)) tests with past+future interaction, testing both insufficient and sufficient M
- [ ] Write `test_boundary_safe_flag_computation()` -- verify that for a given (depth, M) pair, the boolean M > depth + 1 correctly classifies boundary safety
- [ ] Run the new test file: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_boundary_regression.py -v`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_boundary_regression.py` -- new file, boundary-unsafe formula tests

**Verification**:
- All boundary-unsafe formula tests pass
- Tests explicitly document which formulas exhibit boundary vacuity at insufficient M
- Tests verify correct behavior at sufficient M = max(depth+2, 3)
- At least 5 distinct boundary-sensitive formulas are tested

---

### Phase 3: 43-Example Regression Test [NOT STARTED]

**Goal**: Create a dedicated regression test that verifies all 43 active examples still produce correct SAT/UNSAT results, serving as the gate baseline for this task and future boundary-related changes.

**Tasks**:
- [ ] Add a `TestExampleRegression` class to `test_boundary_regression.py` (or extend test_bimodal.py) that explicitly asserts the expected result for each of the 43 active examples
- [ ] For each of the 10 SAT examples: assert `run_test` returns a countermodel (result is not None / expectation=True is met)
- [ ] For each of the 33 UNSAT examples: assert `run_test` returns no countermodel (result is None / expectation=False is met)
- [ ] Add a `test_temporal_depth_all_17_tags()` test that explicitly constructs one formula for each of the 17 JSON tags and verifies `temporal_depth()` returns the expected value (supplements existing 26 tests with an explicit all-tags coverage check)
- [ ] Run the full regression suite: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`

**Timing**: 0.75 hours

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_boundary_regression.py` -- add regression test class

**Verification**:
- All 43 active examples produce correct SAT/UNSAT results
- `temporal_depth()` explicitly tested for all 17 JSON formula tags in a single test
- No regressions in the existing test suite

---

### Phase 4: Gate Validation [NOT STARTED]

**Goal**: Run the complete test suite and verify all gate criteria are met.

**Tasks**:
- [ ] Run full bimodal test suite: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`
- [ ] Verify gate criterion 1: All 43 examples produce correct results (from Phase 3 regression test)
- [ ] Verify gate criterion 2: `temporal_depth()` is correct for all 17 tags (from Phase 3 explicit tag test + existing 26 tests)
- [ ] Verify no regressions in any existing test files (test_bimodal.py, test_json_translation.py, test_foralltime.py, test_frame_constraints.py, test_until_since.py, test_frame_class_mapping.py, test_next_prev.py, test_witness_constraints.py, test_witness_registry.py, test_modal_witness_integration.py)
- [ ] Run full project test suite: `PYTHONPATH=code/src pytest code/tests/ -v`

**Timing**: 0.25 hours

**Depends on**: 2, 3

**Files to modify**:
- None (validation only)

**Verification**:
- All tests pass across the entire test suite
- Gate criteria explicitly confirmed: 43 examples correct, 17 tags correct

## Testing & Validation

- [ ] All existing bimodal tests pass (no regressions from documentation changes)
- [ ] Boundary-unsafe formula tests demonstrate vacuity at insufficient M
- [ ] Boundary-unsafe formula tests verify correct behavior at sufficient M
- [ ] All 43 active examples produce correct SAT/UNSAT in dedicated regression test
- [ ] `temporal_depth()` handles all 17 JSON formula tags correctly
- [ ] `temporal_depth()` docstring contains the formal boundary claim
- [ ] `ForAllTime()` docstring explains boundary vacuity mechanism
- [ ] Full project test suite passes

## Artifacts & Outputs

- `specs/107_boundary_temporal_depth_mitigation/plans/01_boundary-depth-mitigation.md` (this plan)
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_boundary_regression.py` (new test file)
- Updated docstrings in `code/src/bimodal_logic/translation.py` and `code/src/model_checker/theory_lib/bimodal/semantic.py`
- `specs/107_boundary_temporal_depth_mitigation/summaries/01_boundary-depth-mitigation-summary.md` (generated on completion)

## Rollback/Contingency

All changes are additive: new test file and expanded docstrings. If any changes cause issues:
1. Revert the docstring changes in `translation.py` and `semantic.py` to their pre-edit state
2. Delete `test_boundary_regression.py`
3. No operational code is modified, so there is no risk to existing functionality
