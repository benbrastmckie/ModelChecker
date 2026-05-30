# Implementation Plan: Fix test_update_types_atomic in syntactic Package

- **Task**: 48 - fix_test_update_types_atomic_syntactic
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_research-report.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
- **Type**: python
- **Lean Intent**: true

## Overview

The test `test_update_types_atomic` fails because it uses a `MagicMock` object for the sentence letter return value, but `store_types()` requires a Z3 `Const` object. The Z3 `is_const()` function returns `False` for `MagicMock` objects, causing the atomic sentence detection logic to fail with `ValueError`. The fix is straightforward: replace the `MagicMock` with a real Z3 `Const` object in the test.

### Research Integration

The research report identified:
- Root cause: `is_const(MagicMock())` returns `False`, bypassing atomic detection
- Impact: Only `test_update_types_atomic` fails; other tests pass
- Recommended fix: Use `Const("p", AtomSort)` instead of `MagicMock()`
- No production code changes needed

## Goals and Non-Goals

**Goals**:
- Fix the failing `test_update_types_atomic` test
- Maintain test isolation while using real Z3 objects
- Verify all related tests continue to pass

**Non-Goals**:
- Modifying production code in `sentence.py`
- Refactoring other tests in the file
- Changing the `store_types()` detection logic

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| AtomSort import fails | High | Low | Verify import path in existing tests |
| Other tests affected by import | Medium | Low | Run full test suite after change |

## Implementation Phases

### Phase 1: Fix Test [COMPLETED]

**Goal**: Replace MagicMock with real Z3 Const object

**Tasks**:
- [ ] Add Z3 `Const` import to test file
- [ ] Add `AtomSort` import from `model_checker.syntactic.atoms`
- [ ] Replace `mock_atom = MagicMock()` with `real_atom = Const("p", AtomSort)`
- [ ] Update assertion to use `real_atom`

**Timing**: 10 minutes

**Files to modify**:
- `code/src/model_checker/syntactic/tests/unit/test_sentence.py` - Update test_update_types_atomic

**Verification**:
- Run `python -m pytest code/src/model_checker/syntactic/tests/unit/test_sentence.py::TestUpdateMethods::test_update_types_atomic -v`
- Verify test passes

---

### Phase 2: Verify Test Suite [COMPLETED]

**Goal**: Ensure no regressions in related tests

**Tasks**:
- [ ] Run all sentence tests to verify no regressions
- [ ] Run full syntactic package tests

**Timing**: 5 minutes

**Verification**:
- `python -m pytest code/src/model_checker/syntactic/tests/unit/test_sentence.py -v` passes
- `python -m pytest code/src/model_checker/syntactic/tests/ -v` passes

## Testing and Validation

- [x] `test_update_types_atomic` passes
- [x] All tests in `TestUpdateMethods` class pass
- [x] Full `test_sentence.py` test file passes (21 tests)
- [x] Full syntactic package tests pass (71 tests)

## Artifacts and Outputs

- `plans/01_implementation-plan.md` (this file)
- `summaries/01_execution-summary.md` (after implementation)

## Rollback/Contingency

If the fix introduces regressions:
1. Revert the test file to previous state using `git checkout`
2. Investigate whether `AtomSort` import has side effects
3. Consider alternative approach using `AtomVal` helper function
