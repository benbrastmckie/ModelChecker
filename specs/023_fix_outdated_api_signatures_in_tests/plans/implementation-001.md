# Implementation Plan: Task #23

- **Task**: 23 - fix_outdated_api_signatures_in_tests
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/023_fix_outdated_api_signatures_in_tests/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Fix 22+ test failures caused by 5 distinct API signature mismatches across 8 test files. The tests were written against older API signatures but the source implementations have evolved. This plan follows the research-recommended order: quick wins first (STANDARD_SETTINGS, OutputManager, path fix), then progressively more complex fixes (Syntax, ModelDefaults).

### Research Integration

From research-001.md:
- `Syntax.__init__()` requires `(infix_premises, infix_conclusions, operator_collection)` - 3 files affected
- `ModelDefaults.__init__()` requires `(model_constraints, settings)` - 4 files affected (most complex)
- `OutputManager.__init__()` requires `(config: OutputConfig, prompt_manager=None)` - 2 files affected
- `STANDARD_SETTINGS` needs to be added to `tests/fixtures/example_data.py`
- `builder/example.py` path reference in test uses incorrect relative path

## Goals & Non-Goals

**Goals**:
- Fix all 22+ test failures caused by API signature mismatches
- Update tests to use current API signatures correctly
- Create helper functions where needed to reduce verbosity (especially for ModelDefaults)
- Maintain test intent and coverage

**Non-Goals**:
- Changing the source API signatures
- Adding new test cases
- Refactoring tests beyond what's needed for signature fixes

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Breaking other tests during fix | High | Medium | Run full test suite after each phase |
| Misunderstanding test intent | Medium | Low | Review each test's purpose before fixing |
| ModelDefaults complexity | Medium | Medium | Create helper function to encapsulate model creation |
| Missing edge cases | Low | Low | Verify affected test count matches research findings |

## Implementation Phases

### Phase 1: Add STANDARD_SETTINGS Export [COMPLETED]

**Goal**: Add the missing STANDARD_SETTINGS export to unblock test_error_handling.py

**Tasks**:
- [ ] Examine existing TEST_SETTINGS structure in example_data.py
- [ ] Add STANDARD_SETTINGS definition (either new dict or alias to existing)
- [ ] Verify import works from test_error_handling.py

**Timing**: 15 minutes

**Files to modify**:
- `code/tests/fixtures/example_data.py` - Add STANDARD_SETTINGS export

**Verification**:
- Run `PYTHONPATH=code/src pytest code/tests/integration/test_error_handling.py -v -k STANDARD` to verify import works

---

### Phase 2: Fix OutputManager Signature [COMPLETED]

**Goal**: Update OutputManager instantiations to use OutputConfig

**Tasks**:
- [ ] Update test_simple_output_verify.py line 42 to use OutputConfig
- [ ] Update test_batch_output_integration.py lines 65, 137, 180 to use OutputConfig
- [ ] Add required imports for OutputConfig

**Timing**: 20 minutes

**Files to modify**:
- `code/tests/e2e/test_simple_output_verify.py` - Fix 1 OutputManager call
- `code/tests/integration/test_batch_output_integration.py` - Fix 3 OutputManager calls

**Verification**:
- Run `PYTHONPATH=code/src pytest code/tests/e2e/test_simple_output_verify.py code/tests/integration/test_batch_output_integration.py -v`

---

### Phase 3: Fix builder/example.py Path Reference [COMPLETED]

**Goal**: Fix incorrect relative path in test_model_building_sync.py

**Tasks**:
- [ ] Update path construction at line 106-108 to use correct relative path
- [ ] Consider using module introspection as more robust alternative

**Timing**: 15 minutes

**Files to modify**:
- `code/tests/integration/test_model_building_sync.py` - Fix path reference

**Verification**:
- Run `PYTHONPATH=code/src pytest code/tests/integration/test_model_building_sync.py -v -k "build_example"`

---

### Phase 4: Fix Syntax.__init__() Calls [COMPLETED]

**Goal**: Update all Syntax instantiations to use correct signature

**Tasks**:
- [ ] Fix test_performance.py lines 284, 356 - replace `Syntax()` with proper signature
- [ ] Fix test_error_handling.py lines 90, 112, 259 - replace `Syntax()` with proper signature
- [ ] Fix test_model_building_sync.py lines 52, 60 - replace dict with OperatorCollection
- [ ] Add required imports for OperatorCollection where missing

**Timing**: 30 minutes

**Files to modify**:
- `code/tests/integration/test_performance.py` - Fix 2 Syntax calls
- `code/tests/integration/test_error_handling.py` - Fix 3 Syntax calls
- `code/tests/integration/test_model_building_sync.py` - Fix 2 Syntax calls

**Verification**:
- Run `PYTHONPATH=code/src pytest code/tests/integration/test_performance.py code/tests/integration/test_error_handling.py code/tests/integration/test_model_building_sync.py -v`

---

### Phase 5: Fix ModelDefaults.__init__() Calls [COMPLETED]

**Goal**: Update all ModelDefaults instantiations to use correct signature with ModelConstraints

**Tasks**:
- [ ] Create helper function in tests/utils/helpers.py for model creation
- [ ] Fix tests/utils/base.py line 150 - update create_model() method
- [ ] Fix test_performance.py lines 102, 124, 158, 247, 336
- [ ] Fix test_error_handling.py lines 134, 148, 208
- [ ] Fix test_timeout_resources.py lines 32, 86, 106, 128, 141, 195, 225, 252, 280
- [ ] Add required imports for ModelConstraints, Syntax, OperatorCollection, theory

**Timing**: 60 minutes

**Files to modify**:
- `code/tests/utils/helpers.py` - Add create_test_model() helper function
- `code/tests/utils/base.py` - Fix BaseModelTest.create_model()
- `code/tests/integration/test_performance.py` - Fix 5 ModelDefaults calls
- `code/tests/integration/test_error_handling.py` - Fix 3 ModelDefaults calls
- `code/tests/integration/test_timeout_resources.py` - Fix 9 ModelDefaults calls

**Verification**:
- Run `PYTHONPATH=code/src pytest code/tests/integration/test_performance.py code/tests/integration/test_error_handling.py code/tests/integration/test_timeout_resources.py -v`

---

### Phase 6: Final Verification [IN PROGRESS]

**Goal**: Verify all affected tests pass and no regressions

**Tasks**:
- [ ] Run full test suite for affected test files
- [ ] Verify test count matches expected (22+ tests passing)
- [ ] Run broader test suite to check for regressions

**Timing**: 10 minutes

**Files to modify**:
- None (verification only)

**Verification**:
- Run `PYTHONPATH=code/src pytest code/tests/ -v --tb=short` and verify no failures in affected files

## Testing & Validation

- [ ] All 8 affected test files pass with no failures
- [ ] No regressions in other test files
- [ ] Helper function create_test_model() works correctly
- [ ] Total passing test count increases by ~22 tests

## Artifacts & Outputs

- `plans/implementation-001.md` - This plan
- `summaries/implementation-summary-YYYYMMDD.md` - Implementation summary after completion

## Rollback/Contingency

If implementation causes unexpected regressions:
1. Revert changes using git
2. Analyze which specific fix caused the regression
3. Re-apply fixes incrementally to isolate the issue
4. Consult source API documentation for correct usage patterns
