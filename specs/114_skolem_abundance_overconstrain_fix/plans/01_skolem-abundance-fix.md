# Implementation Plan: Fix skolem_abundance Over-constraint at M>=3

- **Task**: 114 - Fix skolem_abundance over-constraint at M>=3
- **Status**: [IN PROGRESS]
- **Effort**: 2.5 hours
- **Dependencies**: 108 (soundness regression test suite)
- **Research Inputs**: specs/114_skolem_abundance_overconstrain_fix/reports/01_skolem-abundance-fix.md
- **Artifacts**: plans/01_skolem-abundance-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The `capped_skolem_abundance_constraint` in BimodalSemantics uses a triply-nested quantifier structure (`ForAll[src, shift] -> ForAll[time]`) that triggers Z3 MBQI instantiation loops at M>=3, causing solver timeouts and spurious UNSAT on no-premise queries. The fix conditionally dispatches to `build_grounded_abundance_constraints()` at M>=3, which enumerates concrete (interval, shift) pairs as independent `ForAll[src]` constraints that Z3 handles via E-matching. After fixing the constraint dispatch, the oracle's M formula is restored from `max(depth, 2)` to `max(depth+2, 3)`, making `boundary_safe=True` for all formulas. The existing xfail test for M=3 shift closure becomes a passing regression gate.

### Research Integration

Key findings from report 01_skolem-abundance-fix.md:
- Root cause: triply-nested `ForAll[src, shift] -> ForAll[time]` with array selects on quantified indices is a pathological MBQI pattern. At M=3 there are 6 valid (interval, shift) pairs across 5 time points.
- `build_grounded_abundance_constraints()` already exists (semantic.py:1317-1393) and returns a list of per-pair `ForAll[src]` constraints with concrete integer indices.
- Task 98 benchmarks rejecting the grounded form were conducted at M=2 only; the conclusion does not apply at M>=3 where the quantified form is intractable.
- Four files need changes: semantic.py (dispatch + list handling), provider.py (M formula), test_soundness_regression.py (update assertions).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items identified for this task.

## Goals & Non-Goals

**Goals**:
- Enable M=max(depth+2, 3) without solver timeout or spurious UNSAT
- Restore boundary_safe=True for all formulas (since max(depth+2,3) > depth+1 always)
- Pass the xfail shift-closure test at M=3
- Preserve M=2 performance characteristics (capped form unchanged at M=2)

**Non-Goals**:
- Rewriting or removing `capped_skolem_abundance_constraint` (kept for M=2)
- Optimizing `build_grounded_abundance_constraints` for M>5 (out of scope)
- Changing BimodalSemantics constructor API or solver adapter settings

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Grounded constraints slower than capped at M=3 | M | L | Grounded eliminates MBQI entirely; verify BM_TH_1/BM_TH_2 still solve within 10s timeout |
| Tests relying on M=2 behavior break at new M values | H | M | Phase 1 writes tests first (TDD); Phase 3 systematically updates every assertion referencing M=2 |
| G(G(p)) returns countermodel at M=4 but solver times out | M | L | M=4 produces 12 grounded constraints (manageable); test with 10s timeout; fall back to 30s if needed |
| List flattening in build_frame_constraints breaks constraint ordering | H | L | Verify return list preserves MBQI seed ordering; skolem_abundance position unchanged |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Write Tests for New Behavior (TDD Red) [COMPLETED]

**Goal**: Write failing tests that define the expected behavior after the fix, establishing the test-first contract.

**Tasks**:
- [ ] Add a new test `test_grounded_dispatch_at_m3` in test_soundness_regression.py that directly instantiates BimodalSemantics with M=3 and verifies `build_grounded_abundance_constraints()` returns a non-empty list of constraints (not a single formula)
- [ ] Add a test `test_capped_dispatch_at_m2` confirming BimodalSemantics with M=2 still uses `capped_skolem_abundance_constraint` (single formula)
- [ ] Add a test `test_oracle_m_formula_boundary_safe` that creates Z3OracleProvider and verifies:
  - depth=0 formula: M=3 (from max(0+2,3)=3), boundary_safe=True
  - depth=1 formula: M=3 (from max(1+2,3)=3), boundary_safe=True
  - depth=2 formula: M=4 (from max(2+2,3)=4), boundary_safe=True
- [ ] Add a test `test_gg_p_returns_countermodel` that verifies G(G(p)) returns a non-None result at the new M=max(2+2,3)=4 (was previously None at M=2 due to boundary vacuity)
- [ ] Add a test `test_fg_p_returns_countermodel` that verifies F(G(p)) returns a non-None result at M=4 (was previously None at M=2)
- [ ] Run tests and confirm all new tests fail (red phase)

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` -- add new test methods

**Verification**:
- New tests exist and fail with expected error messages
- Existing tests continue to pass unchanged
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py -v --tb=short 2>&1 | tail -20`

---

### Phase 2: Fix Constraint Dispatch in semantic.py [COMPLETED]

**Goal**: Modify `build_frame_constraints()` to use `build_grounded_abundance_constraints()` when M>=3, and handle the list return type in the constraint aggregation.

**Tasks**:
- [ ] In `build_frame_constraints()` (semantic.py ~line 658), replace:
  ```python
  skolem_abundance = self.capped_skolem_abundance_constraint()
  ```
  with conditional dispatch:
  ```python
  if self.M >= 3:
      skolem_abundance = self.build_grounded_abundance_constraints()
  else:
      skolem_abundance = [self.capped_skolem_abundance_constraint()]
  ```
- [ ] Update the return statement (semantic.py ~lines 783-803) to flatten the `skolem_abundance` list. Replace the single `skolem_abundance` entry with `*skolem_abundance` list unpacking:
  ```python
  return [
      valid_main_world,
      valid_main_time,
      enumeration_constraint,
      convex_world_ordering,
      world_interval,
      lawful,
      nullity_identity,
      converse,
      forward_comp,
      *skolem_abundance,   # list of constraints (1 for M=2, multiple for M>=3)
      world_uniqueness,
  ]
  ```
- [ ] Update the Task 98 comment block (semantic.py ~lines 647-657) to document the conditional dispatch and why grounded is used at M>=3
- [ ] Run existing tests to verify M=2 behavior is unchanged:
  `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py::TestShiftClosure::test_shift_closure_on_extracted_worlds_m2 -v`

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` -- conditional dispatch at ~line 658, list unpacking at ~line 798, comment update at ~lines 647-657

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v -k "not test_shift_closure_on_extracted_worlds_m3" --tb=short 2>&1 | tail -5` -- all existing tests pass
- The xfail test `test_shift_closure_on_extracted_worlds_m3` should now pass (xfail becomes xpass, which pytest reports as unexpected pass)

---

### Phase 3: Restore M Formula and Update Tests [NOT STARTED]

**Goal**: Change provider.py's M formula from `max(depth, 2)` to `max(depth+2, 3)` and update all test assertions that depend on specific M values or boundary_safe flags.

**Tasks**:
- [ ] In provider.py (~line 215), change `M = max(depth, 2)` to `M = max(depth + 2, 3)`
- [ ] Update the comment block at provider.py ~lines 207-213 to document the restored formula and reference the fix
- [ ] In test_soundness_regression.py, update `TestBoundaryVacuity`:
  - `test_depth0_boundary_safe_is_true`: Update docstring. M is now max(0+2,3)=3, boundary_safe=(3>1)=True. Assertion stays True but update M check from 2 to 3
  - `test_depth1_boundary_safe_is_false`: Rename to `test_depth1_boundary_safe_is_true`. M=max(1+2,3)=3, boundary_safe=(3>2)=True. Change assertion from False to True, update M from 2 to 3
  - `test_depth2_boundary_safe_is_false`: Rename to `test_depth2_boundary_safe_is_true`. M=max(2+2,3)=4, boundary_safe=(4>3)=True. Change assertion from False to True, update M from 2 to 4
  - `test_gg_p_returns_none_at_m2`: Remove or replace. G(G(p)) now runs at M=4 where it should find a countermodel. Replace with `test_gg_p_returns_countermodel` asserting result is not None
  - `test_fg_p_returns_none_at_m2`: Remove or replace. F(G(p)) now runs at M=4. Replace with `test_fg_p_returns_countermodel` asserting result is not None
  - `test_depth1_countermodel_correct_despite_boundary_unsafe`: Update: boundary_safe is now True, time_bound is 3
- [ ] In test_soundness_regression.py, update `TestShiftClosure`:
  - `test_shift_closure_on_extracted_worlds_m3`: Remove @pytest.mark.xfail decorator and the internal pytest.xfail fallback; this test should now pass
- [ ] In test_soundness_regression.py, update `TestKnownBoundaryUnsafe`:
  - `test_gg_p_spurious_unsat`: G(G(p)) now uses M=4, should find countermodel. Change assertion from `result is None` to `result is not None`, update docstring
  - `test_fg_p_spurious_unsat`: Same change -- result should be not None at M=4
  - `test_gf_p_genuine_countermodel`: M now 4, boundary_safe now True. Update assertions
  - `test_ff_p_boundary_behavior`: M now 4, boundary_safe now True. Update assertions
  - `test_imp_gg_p_gf_p_boundary_unsafe`: M now 4, boundary_safe now True. G(G(p)) may no longer be vacuously true at M=4, so the implication behavior may change -- verify and update assertion
- [ ] Update class-level docstrings for TestBoundaryVacuity and TestKnownBoundaryUnsafe to reflect the new M=max(depth+2,3) formula
- [ ] Update module-level docstring at top of test_soundness_regression.py (lines 1-25) to reflect the new M formula

**Timing**: 45 minutes

**Depends on**: 2

**Files to modify**:
- `code/src/bimodal_logic/provider.py` -- line 215 M formula change, comment update
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py` -- extensive assertion updates across TestBoundaryVacuity, TestShiftClosure, TestKnownBoundaryUnsafe

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_soundness_regression.py -v --tb=short` -- all tests pass, no xfails
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v --tb=short 2>&1 | tail -10` -- full bimodal suite passes

---

### Phase 4: Full Regression and Gate Validation [NOT STARTED]

**Goal**: Run the complete test suite to verify no regressions and confirm all gate criteria are met.

**Tasks**:
- [ ] Run full bimodal test suite: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v --tb=short`
- [ ] Run oracle interface tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_interface.py -v --tb=short`
- [ ] Run enriched operator equivalence tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_enriched_equivalence.py -v --tb=short`
- [ ] Run boundary regression tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_boundary_regression.py -v --tb=short`
- [ ] Verify gate criteria:
  - Gate 1: `test_shift_closure_on_extracted_worlds_m3` passes (no xfail)
  - Gate 2: Oracle uses M=max(depth+2,3) -- verified by boundary_safe=True in depth-0 and depth-1 test results
  - Gate 3: All existing tests pass (no regressions)
  - Gate 4: boundary_safe=True for depth-0 and depth-1 formulas -- verified by TestBoundaryVacuity tests
- [ ] If any test fails, investigate and fix before completing

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- None (validation only; fixes if needed go back to modified files)

**Verification**:
- Zero test failures across full bimodal suite
- All 4 gate criteria confirmed in test output
- No xfail markers remaining in test_soundness_regression.py

## Testing & Validation

- [ ] `test_shift_closure_on_extracted_worlds_m3` passes without xfail (Gate 1)
- [ ] Oracle returns M=max(depth+2,3) for all formulas -- verified via boundary_safe=True assertions (Gate 2)
- [ ] Full bimodal test suite passes with no regressions (Gate 3)
- [ ] boundary_safe=True for depth-0 (M=3) and depth-1 (M=3) formulas (Gate 4)
- [ ] G(G(p)) at M=4 returns a countermodel (no longer spurious theorem)
- [ ] F(G(p)) at M=4 returns a countermodel (no longer spurious theorem)
- [ ] BM_TH_1 and BM_TH_2 perpetuity tests still pass (shift closure holds at M>=3)
- [ ] 100+ sequential oracle calls in TestStateIsolationRegression pass (no state leakage)

## Artifacts & Outputs

- `specs/114_skolem_abundance_overconstrain_fix/plans/01_skolem-abundance-fix.md` (this file)
- `specs/114_skolem_abundance_overconstrain_fix/summaries/01_skolem-abundance-fix-summary.md` (after implementation)

## Rollback/Contingency

If the grounded constraints at M>=3 cause unexpected regressions:
1. Revert semantic.py dispatch back to unconditional `capped_skolem_abundance_constraint()`
2. Revert provider.py M formula back to `max(depth, 2)`
3. Re-add xfail marker on the M=3 shift closure test
4. Restore all test assertions to their pre-fix values
5. All changes are localized to 3 files, making clean revert straightforward via `git checkout`
