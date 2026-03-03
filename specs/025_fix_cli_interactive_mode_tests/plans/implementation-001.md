# Implementation Plan: Task #25

- **Task**: 25 - Fix CLI interactive mode tests
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/025_fix_cli_interactive_mode_tests/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Delete orphaned test files that test an "interactive mode" feature that was intentionally refactored to "sequential mode" in September 2025. The existing `--sequential/-q` flag and `SequentialSaveManager` class already provide the tested functionality. These tests were left behind during the refactor and now cause 21 test failures.

### Research Integration

Key findings from research-001.md:
- Tests are **orphaned from an intentional refactor** (commit `27e84720` on 2025-09-15)
- The `--interactive/-I` flag was never added to argparse
- `model_checker.output.interactive` module was **renamed** to `sequential_manager`
- Sequential mode with `-q/--sequential` flag already provides the same functionality
- Implementing `-I` would create redundant, confusing functionality

## Goals & Non-Goals

**Goals**:
- Remove 21 failing tests that reference non-existent functionality
- Eliminate import errors from `model_checker.output.interactive`
- Ensure test suite passes without these orphaned tests

**Non-Goals**:
- Implement `--interactive/-I` flag (redundant with `--sequential`)
- Modify `IInteractiveManager` protocol (keep for potential future use)
- Add new tests (sequential mode has existing coverage)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Deleting tests removes planned feature | Low | Very Low | Git history preserves tests; can restore if needed |
| Missing test coverage | Low | Low | Verify sequential mode tests cover same scenarios in Phase 2 |
| IInteractiveManager protocol issues | Very Low | Very Low | Keep protocol unchanged; protocols are cheap |

## Implementation Phases

### Phase 1: Delete Orphaned Test Files [COMPLETED]

**Goal**: Remove the two test files causing 21 failures

**Tasks**:
- [ ] Delete `code/tests/integration/test_cli_interactive.py`
- [ ] Delete `code/tests/integration/test_build_module_interactive.py`
- [ ] Run test suite to confirm failures are resolved

**Timing**: 15 minutes

**Files to modify**:
- `code/tests/integration/test_cli_interactive.py` - DELETE
- `code/tests/integration/test_build_module_interactive.py` - DELETE

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/integration/test_cli_interactive.py -v` returns "no tests found" or file not found
- `PYTHONPATH=code/src pytest code/tests/integration/test_build_module_interactive.py -v` returns "no tests found" or file not found
- Full test suite shows reduction in failures

---

### Phase 2: Verify Sequential Mode Coverage [COMPLETED]

**Goal**: Confirm sequential mode has adequate test coverage for the scenarios these tests described

**Tasks**:
- [ ] Review existing sequential mode tests at `code/src/model_checker/output/tests/`
- [ ] Confirm tests cover prompting behavior (should_save, should_find_more)
- [ ] Run sequential mode tests to confirm they pass
- [ ] Document test coverage status

**Timing**: 15 minutes

**Files to modify**:
- None (verification only)

**Verification**:
- Sequential mode unit tests exist and pass
- Test coverage includes `SequentialSaveManager` core methods

## Testing & Validation

- [ ] Full test suite runs without the 21 interactive mode failures
- [ ] Sequential mode tests (`test_sequential_manager.py`) pass
- [ ] No new test failures introduced
- [ ] `pytest code/tests/ -v` completes successfully

## Artifacts & Outputs

- plans/implementation-001.md (this file)
- summaries/implementation-summary-YYYYMMDD.md (upon completion)

## Rollback/Contingency

If tests need to be restored:
1. Retrieve files from git history: `git show HEAD~N:code/tests/integration/test_cli_interactive.py`
2. Restore with: `git checkout HEAD~N -- code/tests/integration/test_cli_interactive.py`
3. Alternatively, find commit `276f6ec1` which originally added the tests
