# Implementation Plan: Task #54

- **Task**: 54 - fix_mod_comp_solver_comparison_test_failures
- **Status**: [NOT STARTED]
- **Effort**: 0.25 hours
- **Dependencies**: None
- **Research Inputs**: specs/054_fix_mod_comp_solver_comparison_test_failures/reports/01_lambda-error-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: true

## Overview

Fix the MOD_COMP_1/2/3 solver comparison test failures by adding `first_order` to the modal subtheory dependencies in test_solver_comparison.py. The MOD_COMP examples use `\forall` operator which internally requires `\lambda`, both defined in the first_order subtheory. The test's `subtheory_deps` dictionary was not updated when these examples were added.

### Research Integration

- Root cause: MOD_COMP examples use first-order quantification (`\forall`) but test only loads `['extensional', 'modal']`
- The `\forall` operator desugars to `\forall(\lambda v. ...)`, requiring the lambda operator
- Lambda operator is only registered in `first_order` subtheory
- Fix location identified: `get_required_subtheories` function in test_solver_comparison.py (lines 86-105)

## Goals & Non-Goals

**Goals**:
- Fix all 6 MOD_COMP test failures (z3 and cvc5 backends)
- Ensure modal tests still pass with the additional dependency

**Non-Goals**:
- Restructuring the example organization
- Adding per-example dependency metadata
- Performance optimization

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Other modal tests break with first_order | M | L | Run full modal test suite after fix |
| first_order adds unwanted overhead | L | L | first_order only adds 4 operators; negligible |

## Implementation Phases

### Phase 1: Update Subtheory Dependencies [NOT STARTED]

**Goal**: Add `first_order` to modal subtheory dependencies in test file

**Tasks**:
- [ ] Edit `subtheory_deps` dictionary to include `first_order` for modal key
- [ ] Run MOD_COMP tests to verify fix
- [ ] Run full modal test suite to ensure no regressions

**Timing**: 0.25 hours

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/tests/integration/test_solver_comparison.py` - add `first_order` to modal deps

**Change**:
```python
# Before (line ~88):
'modal': ['extensional', 'modal'],

# After:
'modal': ['extensional', 'modal', 'first_order'],
```

**Verification**:
- `pytest test_solver_comparison.py -k "MOD_COMP" -v` - all 6 tests pass
- `pytest test_solver_comparison.py -k "modal" -v` - all modal tests pass

---

## Testing & Validation

- [ ] Run `pytest test_solver_comparison.py -k "MOD_COMP" -v` - 6 tests should pass
- [ ] Run `pytest test_solver_comparison.py -k "modal" -v` - all modal tests pass
- [ ] Verify no regressions in full test suite (optional, if time permits)

## Artifacts & Outputs

- Modified test file: `test_solver_comparison.py`
- 6 passing MOD_COMP tests

## Rollback/Contingency

If the fix causes other test failures, revert the single line change. The original value is:
```python
'modal': ['extensional', 'modal'],
```
