# Implementation Plan: Task #33

- **Task**: 33 - fix_premature_progress_bar_display
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/033_fix_premature_progress_bar_display/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

When running examples with `iterate > 1`, the iteration progress bar appears BEFORE the example header (e.g., "EXAMPLE NAME: there is a countermodel."), creating visual confusion. The fix will use a `Spinner` (which clears itself) for model 1's initial solve instead of `TimeBasedProgress` (which prints a permanent progress line), ensuring the example header appears first before any progress tracking output.

### Research Integration

The research report identified:
- **Root cause**: In `_process_with_iterations`, `progress.complete_model_search()` prints the final progress state BEFORE `_capture_and_save_output()` prints the example header
- **Recommended fix**: Use `Spinner` for model 1 (matches single-model pattern from `run_model_check`), then create `UnifiedProgress` for models 2+ after the header is printed
- **Key insight**: The `Spinner.stop()` method clears its line without leaving any permanent output, while `TimeBasedProgress.complete()` prints a permanent progress line

## Goals & Non-Goals

**Goals**:
- Fix the progress bar appearing before the example header for `iterate > 1` examples
- Maintain consistent behavior between single-model examples (`iterate=1`) and multi-model examples
- Preserve progress tracking for models 2+ during iteration
- Follow TDD methodology per project standards

**Non-Goals**:
- Adding new progress tracking features
- Changing the progress bar format or appearance
- Modifying single-model example behavior (already works correctly)
- Refactoring the entire progress tracking system

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Regression in iteration output format | Medium | Low | Comprehensive testing with iterate=2,3,10 |
| Progress timing accuracy affected | Low | Low | Preserve timing info from spinner phase |
| Interactive mode affected differently | Medium | Medium | Test both batch and interactive modes |
| UnifiedProgress state management issues | Medium | Low | Careful initialization of `models_found` counter |

## Implementation Phases

### Phase 1: Write Failing Tests [NOT STARTED]

**Goal**: Create tests that demonstrate the bug and specify the expected behavior

**Tasks**:
- [ ] Create test file `test_progress_bar_ordering.py` in `builder/tests/unit/`
- [ ] Write test `test_progress_bar_not_printed_before_header_in_batch_mode` - verifies no progress output before header
- [ ] Write test `test_spinner_used_for_model_1_with_iterations` - verifies Spinner is used for initial model
- [ ] Write test `test_progress_bar_appears_after_header_for_subsequent_models` - verifies models 2+ have progress after header
- [ ] Run tests to confirm they fail (RED state)

**Timing**: 1 hour

**Files to modify**:
- `code/src/model_checker/builder/tests/unit/test_progress_bar_ordering.py` - new test file

**Verification**:
- All new tests fail as expected (demonstrating the bug exists)
- Tests clearly document expected behavior in docstrings

---

### Phase 2: Implement Fix in runner.py [NOT STARTED]

**Goal**: Modify `_process_with_iterations` to use Spinner for model 1 and defer UnifiedProgress to models 2+

**Tasks**:
- [ ] Add `Spinner` import to runner.py if not present
- [ ] Modify `_process_with_iterations` to:
  - [ ] Use `Spinner` for initial model solve (like `run_model_check` does)
  - [ ] Call `_capture_and_save_output` after spinner stops (header prints first)
  - [ ] Only create `UnifiedProgress` tracker if `iterate_count > 1`
  - [ ] Initialize `progress.models_found = 1` before starting iteration
  - [ ] Remove the premature `print()` before model 1 progress
- [ ] Ensure timing information is preserved from spinner phase
- [ ] Run tests to verify they pass (GREEN state)

**Timing**: 1 hour

**Files to modify**:
- `code/src/model_checker/builder/runner.py` - lines 388-450, `_process_with_iterations` method

**Verification**:
- All new tests from Phase 1 pass
- Existing runner tests still pass
- Manual test with `iterate > 1` shows header before progress bar

---

### Phase 3: Update UnifiedProgress Initialization [NOT STARTED]

**Goal**: Ensure UnifiedProgress can be initialized starting from model 2

**Tasks**:
- [ ] Review `UnifiedProgress.start_model_search()` for model 2 initialization
- [ ] Verify `models_found` counter can be pre-set before starting
- [ ] Add test for `UnifiedProgress` starting from model 2
- [ ] Ensure progress bar correctly shows "2/N" for second model search

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/output/progress/core.py` - potentially update `UnifiedProgress` if needed
- `code/src/model_checker/builder/tests/unit/test_progress.py` - add test for model 2 start

**Verification**:
- Progress bar shows "Finding non-isomorphic models: [...] 2/N" for second model
- No duplicate progress bars or state issues

---

### Phase 4: Integration Testing and Cleanup [NOT STARTED]

**Goal**: Verify fix works in all modes and clean up code

**Tasks**:
- [ ] Test with various `iterate` values (2, 3, 5, 10)
- [ ] Test interactive mode (prompt_manager enabled)
- [ ] Test batch mode (no prompt_manager)
- [ ] Test case where first model fails (no countermodel found)
- [ ] Refactor: Remove any unnecessary code from the fix
- [ ] Add docstring updates explaining the Spinner/Progress split

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/builder/runner.py` - docstring updates
- `code/src/model_checker/builder/tests/unit/test_progress_bar_ordering.py` - additional edge case tests

**Verification**:
- All test cases pass
- Code coverage maintained
- Manual verification with real examples shows correct output ordering

---

## Testing & Validation

- [ ] All new unit tests pass
- [ ] All existing unit tests pass (`PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/unit/ -v`)
- [ ] All existing progress tests pass (`PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/unit/test_progress.py -v`)
- [ ] Manual test with `iterate=2` shows header before progress bar
- [ ] Interactive mode works correctly
- [ ] Batch mode works correctly
- [ ] No model found case works correctly

## Artifacts & Outputs

- `code/src/model_checker/builder/tests/unit/test_progress_bar_ordering.py` - new test file
- `code/src/model_checker/builder/runner.py` - modified `_process_with_iterations`
- `code/src/model_checker/output/progress/core.py` - possibly modified (if UnifiedProgress changes needed)
- `code/src/model_checker/builder/tests/unit/test_progress.py` - possibly modified (additional tests)

## Rollback/Contingency

If the implementation causes regressions:
1. Revert changes to `runner.py:_process_with_iterations`
2. The current behavior is functional, just visually confusing
3. Alternative approach: Add a `suppress_output` parameter to `TimeBasedProgress.complete()` to skip printing for model 1
