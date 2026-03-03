# Implementation Plan: Task #22

- **Task**: 22 - Fix test helper run_cli_command code directory lookup
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/022_fix_test_helper_code_directory_lookup/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Fix the project root detection logic in two test files that currently look for a directory named `'Code'` (capital C), but task 16 renamed the directory to `'code'` (lowercase). The recommended approach from research is to use `pyproject.toml` as the project root marker instead of hardcoding the directory name, making the code robust against future directory renames.

### Research Integration

Research identified:
- Two files need modification: `code/tests/utils/helpers.py` (line 29) and `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` (line 22)
- 5 failing tests in `test_error_handling.py` due to PYTHONPATH not being set correctly
- 3 skipped tests in `test_full_pipeline.py` because `dev_cli.py` is not found
- `pyproject.toml` marker approach is preferred over simple case change for robustness

## Goals & Non-Goals

**Goals**:
- Fix project root detection to work with lowercase `code/` directory
- Use `pyproject.toml` as the marker file for robustness
- Restore 5 failing tests in `test_error_handling.py` to passing
- Restore 3 skipped tests in `test_full_pipeline.py` to running

**Non-Goals**:
- Refactoring the overall test infrastructure
- Centralizing PYTHONPATH setup in conftest.py (out of scope)
- Modifying pytest configuration

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| pyproject.toml not found | L | L | File exists at `code/pyproject.toml`; loop has root check |
| Multiple pyproject.toml files | L | L | Only one exists; pattern finds nearest ancestor |
| I/O overhead from existence check | L | L | Negligible; only during test setup |

## Implementation Phases

### Phase 1: Fix helpers.py [COMPLETED]

**Goal**: Update `run_cli_command()` in helpers.py to use pyproject.toml marker instead of 'Code' directory name.

**Tasks**:
- [ ] Change line 29 from `while current_dir.name != 'Code'` to `while not (current_dir / 'pyproject.toml').exists()`
- [ ] Update comment on line 27 to reflect marker-based approach
- [ ] Run failing tests to verify fix

**Timing**: 10 minutes

**Files to modify**:
- `code/tests/utils/helpers.py` - Change directory lookup condition (lines 27-30)

**Verification**:
- Run: `PYTHONPATH=code/src pytest code/tests/integration/test_error_handling.py -v`
- Expected: All 5 tests pass (previously FAILED)

---

### Phase 2: Fix test_full_pipeline.py [COMPLETED]

**Goal**: Update `setUp()` in test_full_pipeline.py to use pyproject.toml marker instead of 'Code' directory name.

**Tasks**:
- [ ] Change line 22 from `while current.name != 'Code'` to `while not (current / 'pyproject.toml').exists()`
- [ ] Update comment on line 20 to reflect marker-based approach
- [ ] Run skipped tests to verify fix

**Timing**: 10 minutes

**Files to modify**:
- `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` - Change directory lookup condition (lines 20-23)

**Verification**:
- Run: `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/e2e/test_full_pipeline.py -v`
- Expected: Tests run (no longer skipped), may pass or fail based on actual test logic

---

### Phase 3: Verification [COMPLETED]

**Goal**: Confirm all affected tests are fixed and no regressions introduced.

**Tasks**:
- [ ] Run all tests in test_error_handling.py
- [ ] Run all tests in test_full_pipeline.py
- [ ] Run broader test suite to check for regressions

**Timing**: 10 minutes

**Files to modify**:
- None (verification only)

**Verification**:
- Run: `PYTHONPATH=code/src pytest code/tests/integration/test_error_handling.py code/src/model_checker/builder/tests/e2e/test_full_pipeline.py -v`
- Expected: All tests pass or run without skip due to directory lookup

## Testing & Validation

- [ ] All 5 tests in `TestCLIErrorHandling` pass
- [ ] All 3 tests in `TestFullPipeline` are no longer skipped
- [ ] No regressions in related test modules

## Artifacts & Outputs

- plans/implementation-001.md (this file)
- Modified: `code/tests/utils/helpers.py`
- Modified: `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py`
- summaries/implementation-summary-YYYYMMDD.md

## Rollback/Contingency

If the pyproject.toml approach causes issues:
1. Revert to simple case change: replace `'Code'` with `'code'`
2. Both files use identical logic, so rollback is straightforward
3. Git history preserves original state
