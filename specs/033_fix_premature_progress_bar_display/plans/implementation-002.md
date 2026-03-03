# Implementation Plan: Task #33

- **Task**: 33 - fix_premature_progress_bar_display
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/033_fix_premature_progress_bar_display/reports/research-002.md
- **Artifacts**: plans/implementation-002.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

When running examples with `iterate > 1`, the progress bar appears BEFORE the example header. The user confirmed that progress bar permanence is GOOD - the issue is purely the print ORDER/SEQUENCE. The fix restructures `_process_with_iterations` to: (1) stop the animated progress bar without printing its final state, (2) print the header via `_capture_and_save_output()`, (3) THEN print the progress bar's final state.

### Research Integration

Research report revision 002 (research-002.md) clarified:
- **User correction**: "The problem is not the permanence of the progress bar (that is good) I just need it to print in the correct spot."
- **Recommended approach**: Option B - Defer progress bar completion until after header prints
- **Key insight**: The `TimeBasedProgress.complete()` method prints the permanent bar; we need to defer this call until after the header is printed

## Goals & Non-Goals

**Goals**:
- Fix the progress bar sequence so it appears AFTER the example header
- Keep the progress bar animating during Z3 model search
- Keep the permanent progress bar output (user explicitly wants this)
- Follow TDD methodology per project standards

**Non-Goals**:
- Replacing TimeBasedProgress with Spinner (this was the WRONG approach from plan v001)
- Changing the progress bar format or appearance
- Adding new progress tracking features
- Modifying single-model example behavior (`iterate=1` uses different code path)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Animation thread race condition | Low | Medium | Set `active = False` before clearing display |
| Progress bar timing inaccurate | Low | Low | Time is tracked from start, unaffected by print order |
| Interactive mode regression | Medium | Medium | Test both batch and interactive modes |
| No-model-found case affected | Low | Low | Handle separately with appropriate ordering |

## Implementation Phases

### Phase 1: Write Failing Tests [NOT STARTED]

**Goal**: Create tests that demonstrate the bug and specify the expected behavior

**Tasks**:
- [ ] Create test file `test_progress_bar_ordering.py` in `builder/tests/unit/`
- [ ] Write test `test_header_printed_before_progress_bar_completion` - captures stdout and verifies header appears before progress bar final line
- [ ] Write test `test_progress_bar_animation_during_z3_search` - verifies animation starts before Z3 search
- [ ] Write test `test_no_model_found_ordering` - verifies correct order when no model is found
- [ ] Run tests to confirm they fail (RED state)

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/builder/tests/unit/test_progress_bar_ordering.py` - new test file

**Verification**:
- All new tests fail as expected (demonstrating the bug exists)
- Tests use stdout capturing to verify print order

---

### Phase 2: Implement Fix in runner.py [NOT STARTED]

**Goal**: Restructure `_process_with_iterations` to defer progress bar completion until after header prints

**Tasks**:
- [ ] Modify `_process_with_iterations` method (lines 388-450) to:
  - [ ] After Z3 completes, stop animation thread without printing (`progress.active = False`)
  - [ ] Clear the animated line (`progress.display.clear()`)
  - [ ] Call `_capture_and_save_output()` which prints the header
  - [ ] Add vertical space
  - [ ] THEN call `progress.complete_model_search()` to print permanent progress bar
- [ ] Handle no-model-found case with same ordering principle
- [ ] Run tests to verify they pass (GREEN state)

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/builder/runner.py` - `_process_with_iterations` method

**Code change outline**:
```python
# Current (wrong order):
progress.complete_model_search(found=True)  # Prints progress bar
print()
# ... later ...
self.build_module._capture_and_save_output(...)  # Prints header

# Fixed (correct order):
progress.active = False  # Stop animation thread
progress.display.clear()  # Clear animated line
self.build_module._capture_and_save_output(...)  # Print header FIRST
print()
progress.complete_model_search(found=True)  # Print progress bar AFTER
print()
```

**Verification**:
- All new tests from Phase 1 pass
- Existing runner tests still pass
- Progress bar appears after header in output

---

### Phase 3: Adjust TimeBasedProgress.complete() [NOT STARTED]

**Goal**: Ensure `complete()` handles case where animation thread already stopped

**Tasks**:
- [ ] Review `TimeBasedProgress.complete()` in `animated.py`
- [ ] Verify it handles `active = False` gracefully (already stopped thread)
- [ ] Add defensive check if animation thread already joined
- [ ] Add unit test for `complete()` called after manual thread stop

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/output/progress/animated.py` - `TimeBasedProgress.complete()` method (possibly)
- `code/src/model_checker/output/progress/tests/test_animated_progress.py` - add test for pre-stopped thread

**Verification**:
- No errors when `complete()` called after thread already stopped
- All progress tests pass

---

### Phase 4: Integration Testing and Cleanup [NOT STARTED]

**Goal**: Verify fix works in all modes and clean up code

**Tasks**:
- [ ] Test with various `iterate` values (2, 3, 5)
- [ ] Test interactive mode (prompt_manager enabled)
- [ ] Test batch mode (no prompt_manager)
- [ ] Test case where first model fails (no countermodel found)
- [ ] Verify output matches expected sequence from research report
- [ ] Add docstring updates explaining the deferred completion pattern

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/builder/runner.py` - docstring updates

**Verification**:
- All test cases pass
- Manual verification with real examples shows correct output ordering:
  ```
  ========================================
  EXAMPLE FO_CM_1: there is a countermodel.

  [state space info]
  [premises/conclusions]

  Finding non-isomorphic models: [##########] 1/2 0.1s

  [model 1 output]
  ```

---

## Testing & Validation

- [ ] All new unit tests pass
- [ ] All existing unit tests pass (`PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/unit/ -v`)
- [ ] All existing progress tests pass (`PYTHONPATH=code/src pytest code/src/model_checker/output/progress/ -v`)
- [ ] Manual test with `iterate=2` shows header before progress bar
- [ ] Interactive mode works correctly
- [ ] Batch mode works correctly
- [ ] No model found case shows correct ordering

## Artifacts & Outputs

- `code/src/model_checker/builder/tests/unit/test_progress_bar_ordering.py` - new test file
- `code/src/model_checker/builder/runner.py` - modified `_process_with_iterations`
- `code/src/model_checker/output/progress/animated.py` - possibly modified for thread safety
- `code/src/model_checker/output/progress/tests/test_animated_progress.py` - possibly new tests

## Rollback/Contingency

If the implementation causes regressions:
1. Revert changes to `runner.py:_process_with_iterations`
2. The current behavior is functional, just outputs in wrong sequence
3. Alternative approach: Buffer progress bar output and defer printing (more complex, but decoupled)
