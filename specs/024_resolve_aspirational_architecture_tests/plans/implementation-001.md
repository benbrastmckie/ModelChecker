# Implementation Plan: Task #24

- **Task**: 24 - resolve_aspirational_architecture_tests
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/024_resolve_aspirational_architecture_tests/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Delete two aspirational test files that test non-existent APIs. Research confirmed these tests were created as specifications for a planned architecture refactoring that was never implemented. The tests define interfaces (`TheoryInterface`, `ExampleInterface`, `TheoryRegistry`) and APIs (`check_example`, `BuildProject.from_example()`) that do not exist in the codebase. Rather than implement extensive changes for unclear benefit, the recommendation is to delete both files, removing 12 test failures immediately.

### Research Integration

From research-001.md:
- Both files created in commit `0161871f` during directory restructure from `Code/` to `code/`
- Tests explicitly document themselves as "aspirational specifications for clean architecture"
- Existing architecture provides equivalent functionality through duck typing and existing patterns
- 12 of 14 tests fail due to missing APIs; implementing would require extensive changes

## Goals & Non-Goals

**Goals**:
- Remove 12 failing tests that test non-existent APIs
- Clean up test suite to reflect actual codebase architecture
- Verify no regressions in remaining test suite

**Non-Goals**:
- Implementing the missing interfaces and APIs
- Preserving aspirational architecture documentation elsewhere
- Addressing the coupling issue identified in `test_builder_has_no_theory_imports` (separate task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Loss of architectural vision | Low | Low | Research report documents the aspirational design; can be recreated if needed |
| Accidental deletion of valid tests | Medium | Low | Verify file contents match research findings before deletion |
| Breaking other tests | Medium | Very Low | Run full test suite after deletion to verify |

## Implementation Phases

### Phase 1: Verify Current State [COMPLETED]

**Goal**: Confirm test files exist and match research findings before deletion.

**Tasks**:
- [ ] Verify `code/tests/integration/test_architecture_validation.py` exists
- [ ] Verify `code/tests/integration/test_batch_output_integration.py` exists
- [ ] Run affected tests to confirm they fail as documented
- [ ] Document current test count for comparison

**Timing**: 10 minutes

**Files to examine**:
- `code/tests/integration/test_architecture_validation.py` - 11 tests total (1 passing, 10 failing)
- `code/tests/integration/test_batch_output_integration.py` - 3 tests total (all failing)

**Verification**:
- Both files exist
- Tests fail with import/attribute errors for missing APIs
- Test count matches research (14 total tests)

---

### Phase 2: Delete Test Files [COMPLETED]

**Goal**: Remove the aspirational test files from the codebase.

**Tasks**:
- [ ] Delete `code/tests/integration/test_architecture_validation.py`
- [ ] Delete `code/tests/integration/test_batch_output_integration.py`
- [ ] Verify files are removed

**Timing**: 5 minutes

**Files to delete**:
- `code/tests/integration/test_architecture_validation.py`
- `code/tests/integration/test_batch_output_integration.py`

**Verification**:
- Files no longer exist
- Git status shows files as deleted

---

### Phase 3: Verify Test Suite [COMPLETED]

**Goal**: Confirm test suite passes and no regressions were introduced.

**Tasks**:
- [ ] Run full integration test suite
- [ ] Run complete project test suite
- [ ] Verify no new failures introduced
- [ ] Document final test count

**Timing**: 15 minutes

**Commands**:
```bash
PYTHONPATH=code/src pytest code/tests/integration/ -v
PYTHONPATH=code/src pytest code/tests/ -v
```

**Verification**:
- Integration tests pass (minus the 12 removed failures)
- Full test suite passes
- No unexpected failures

## Testing & Validation

- [ ] Both target files are deleted
- [ ] `pytest code/tests/integration/` passes without the deleted test files
- [ ] `pytest code/tests/` passes (full test suite)
- [ ] Test count reduced by 14 (the tests in deleted files)
- [ ] No new test failures introduced

## Artifacts & Outputs

- plans/implementation-001.md (this file)
- summaries/implementation-summary-20260302.md (after completion)

## Rollback/Contingency

If deletion causes unexpected issues:
1. Restore files from git: `git checkout HEAD -- code/tests/integration/test_architecture_validation.py code/tests/integration/test_batch_output_integration.py`
2. Investigate which tests or code depended on deleted files
3. Create follow-up task if restoration is needed with modifications
