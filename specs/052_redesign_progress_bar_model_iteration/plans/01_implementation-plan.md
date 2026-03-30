# Implementation Plan: Task #52

- **Task**: 52 - Redesign progress bar for non-isomorphic model iteration
- **Status**: [NOT STARTED]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_progress-bar-redesign.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Redesign the progress bar system to achieve sequential "bar -> output -> bar -> output" display with time-proportional fill semantics. The current implementation has two architectural issues: (1) `TimeBasedProgress.complete()` fills bars to 100% regardless of actual elapsed time, and (2) `iterate/core.py` calls `complete_model_search()` before yielding models, causing wrong output ordering in `runner.py`.

### Research Integration

Key findings from `reports/01_progress-bar-redesign.md`:
- `complete()` in `animated.py` (lines 189-227) always fills to 100%
- Iterator calls `complete_model_search()` at line 374 BEFORE `yield` at line 399
- Runner displays output AFTER receiving yield, causing bar-bar-output-output ordering
- Recommended solution: Add `freeze_at_current()` method, move completion calls to runner

## Goals & Non-Goals

**Goals**:
- Progress bar fills proportionally to elapsed time vs timeout
- Bar freezes at actual fill level when model found (not 100%)
- Sequential output: bar completes -> model prints -> next bar starts
- Clean animation thread cleanup without races

**Non-Goals**:
- Changing the core iteration algorithm
- Modifying Z3 constraint generation
- Changing the model output format
- Supporting parallel model display

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Animation thread race conditions | H | M | Add explicit thread join with timeout in freeze method |
| Generator interface change breaking callers | M | L | Keep yielded structure unchanged, only change timing |
| Fill fraction calculation inaccuracy | L | M | Use monotonic clock, handle edge cases (< 100ms) |
| Keyboard interrupt during transition | M | M | Ensure cleanup in finally blocks |

## Implementation Phases

### Phase 1: Add Freeze-at-Current Method [NOT STARTED]

**Goal**: Enable TimeBasedProgress to capture current fill fraction and stop animation without completing.

**Tasks**:
- [ ] Add `fill_fraction` attribute to `TimeBasedProgress.__init__()` (default 1.0)
- [ ] Implement `freeze_at_current() -> float` method in `TimeBasedProgress`
  - Calculate elapsed time fraction: `min(1.0, elapsed / timeout)`
  - Store in `self.fill_fraction`
  - Set `self.active = False` to stop animation loop
  - Join animation thread with timeout (0.5s)
  - Return the frozen fill fraction
- [ ] Add `stop_animation_only()` method to `UnifiedProgress` in `core.py`
  - Delegate to `TimeBasedProgress.freeze_at_current()`
  - Do NOT print final bar state
- [ ] Add unit test for `freeze_at_current()` timing accuracy

**Timing**: 1 hour

**Files to modify**:
- `code/src/model_checker/output/progress/animated.py` - Add freeze method
- `code/src/model_checker/output/progress/core.py` - Add stop_animation_only

**Verification**:
- `freeze_at_current()` returns value 0.25-0.35 when called at 30% of timeout
- Animation thread terminates cleanly after freeze

---

### Phase 2: Modify Complete to Use Frozen Fill [NOT STARTED]

**Goal**: Make `complete()` use the stored fill fraction instead of always filling to 100%.

**Tasks**:
- [ ] Modify `TimeBasedProgress.complete()` to use `self.fill_fraction` for bar display
- [ ] Update `_generate_bar()` to accept fill fraction parameter
- [ ] Ensure `complete(success=False)` (timeout) still shows appropriate state
- [ ] Handle case where `freeze_at_current()` was not called (default to current elapsed)
- [ ] Add unit test verifying bar shows ~30% fill when frozen at 30%

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/output/progress/animated.py` - Modify complete() and _generate_bar()

**Verification**:
- Bar displays correct fill percentage when complete() called after freeze
- Bar still fills correctly for timeout case (100% at timeout)

---

### Phase 3: Refactor Iterator Progress Control [NOT STARTED]

**Goal**: Move progress completion from iterator to runner for correct output ordering.

**Tasks**:
- [ ] In `iterate/core.py`, replace `complete_model_search(found=True)` (line 374) with `stop_animation_only()`
  - This freezes the bar but does not print it
- [ ] Expose progress object through the iterator or model structure
  - Option A: Add `search_progress` attribute to yielded structure
  - Option B: Store in iterator state accessible by runner
- [ ] In `runner.py:_run_generator_iteration()`, after model display:
  - Call `progress.complete_model_search(found=True)` to print final bar
  - Ensure proper spacing between bar and next model header
- [ ] Handle model 1 consistency (runner already controls model 1 progress)

**Timing**: 1.5 hours

**Files to modify**:
- `code/src/model_checker/iterate/core.py` - Replace complete with stop_animation_only
- `code/src/model_checker/builder/runner.py` - Add completion call after display

**Verification**:
- Output order is: bar -> MODEL header -> output -> bar -> MODEL header -> output
- No duplicate bar prints or missing bars

---

### Phase 4: Edge Case Handling and Integration Testing [NOT STARTED]

**Goal**: Ensure robust behavior for all edge cases identified in research.

**Tasks**:
- [ ] Test: Only 1 model found when 4 requested
  - Subsequent bars should complete at actual fill, not 100%
  - No bars for models 3, 4 should appear
- [ ] Test: Iteration timeout
  - Active bar should freeze at timeout fill (100%)
  - No model output for timed-out search
- [ ] Test: Keyboard interrupt during search
  - Active progress bar cleaned up
  - Animation thread terminated
  - Partial results preserved
- [ ] Test: Very fast model discovery (<100ms)
  - Bar should show non-zero fill based on actual elapsed
  - No race between animation thread and completion
- [ ] Test: Sequential bar-output ordering with 3+ models
  - Verify correct interleaving pattern

**Timing**: 1.25 hours

**Files to modify**:
- Test files (may need to create integration test)
- Minor fixes to above files if edge cases reveal issues

**Verification**:
- All edge case tests pass
- Manual verification with example theories

## Testing & Validation

- [ ] Unit test: `freeze_at_current()` returns accurate fill fraction
- [ ] Unit test: `complete()` uses frozen fill, not 100%
- [ ] Integration test: bar -> output -> bar -> output ordering
- [ ] Integration test: timeout handling preserves partial results
- [ ] Manual test: Run `logos counterfactual A` and verify sequential output
- [ ] Manual test: Run with `--iterations 4` and verify fill semantics

## Artifacts & Outputs

- `plans/01_implementation-plan.md` (this file)
- `summaries/01_execution-summary.md` (created after completion)
- Modified files:
  - `code/src/model_checker/output/progress/animated.py`
  - `code/src/model_checker/output/progress/core.py`
  - `code/src/model_checker/iterate/core.py`
  - `code/src/model_checker/builder/runner.py`

## Rollback/Contingency

If implementation causes regressions:
1. Revert changes to all four files via git
2. The original behavior (100% fill, bar-bar-output-output) is functional if suboptimal
3. Progress system changes are isolated from core model checking logic
4. No schema or state changes required
