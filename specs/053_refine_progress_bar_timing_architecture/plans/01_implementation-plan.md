# Implementation Plan: Task #53

- **Task**: 53 - refine_progress_bar_timing_architecture
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_timing-architecture-review.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
- **Type**: python

## Overview

This plan addresses timing inconsistencies in the progress bar system where the visual fill fraction is frozen at model-found time via `freeze_at_current()`, but the displayed elapsed time is calculated at `complete()` time. The fix stores `_frozen_elapsed` alongside `fill_fraction` in `freeze_at_current()` and uses both frozen values in `complete()`. Additional work includes integration tests, type hints, and named constants for maintainability.

### Research Integration

Key findings from research report:
- Root cause identified: `complete()` calculates elapsed at display time but uses fill_fraction from freeze time
- Solution: Store `_frozen_elapsed` in `freeze_at_current()` and use it in `complete()` when `_frozen` is True
- Missing integration tests for bar->output->bar ordering and frozen state consistency
- Quality improvements: explicit type hints, documented class constants

## Goals & Non-Goals

**Goals**:
- Fix elapsed time/fill fraction mismatch by storing and using `_frozen_elapsed`
- Add integration tests for multi-model bar ordering
- Add test for frozen elapsed time consistency
- Add type hints and class constants for maintainability
- Document the progress bar state machine contract

**Non-Goals**:
- Refactoring to FrozenProgressState dataclass (lower priority, future work)
- Thread safety with explicit locks (not needed given current single-writer pattern)
- Changing the fundamental animation loop architecture

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Breaking existing tests | Medium | Low | Run existing test suite after each change |
| Thread timing flakiness in new tests | Medium | Medium | Use appropriate sleep times and tolerances |
| Regression in output formatting | Low | Low | Manual verification of output appearance |

## Implementation Phases

### Phase 1: Core Fix - Store and Use Frozen Elapsed Time [NOT STARTED]

**Goal**: Fix the root cause by storing `_frozen_elapsed` in `freeze_at_current()` and using it in `complete()`

**Tasks**:
- [ ] Add `_frozen_elapsed: float = 0.0` attribute to `TimeBasedProgress.__init__()`
- [ ] Modify `freeze_at_current()` to store elapsed time in `_frozen_elapsed`
- [ ] Modify `complete()` to use `_frozen_elapsed` when `_frozen` is True
- [ ] Run existing tests to verify no regressions

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/output/progress/animated.py` - Add `_frozen_elapsed` attribute, update `freeze_at_current()` and `complete()`

**Verification**:
- All existing tests pass
- Manual inspection shows consistent fill/time in output

---

### Phase 2: Unit Test for Frozen Elapsed Consistency [NOT STARTED]

**Goal**: Add unit test to verify elapsed time matches fill fraction after freeze

**Tasks**:
- [ ] Add `test_freeze_elapsed_time_consistency()` to `test_progress_animated.py`
- [ ] Test should verify: when `freeze_at_current()` captures 30% fill at 0.3s, `complete()` displays "0.3s"
- [ ] Verify test passes with Phase 1 fix

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/output/tests/unit/test_progress_animated.py` - Add elapsed time consistency test

**Verification**:
- New test passes
- Test would fail without Phase 1 fix

---

### Phase 3: Integration Tests for Bar Ordering [NOT STARTED]

**Goal**: Add integration tests for bar->output->bar ordering pattern

**Tasks**:
- [ ] Add `TestBarOutputBarOrdering` class to `test_progress_bar_ordering.py`
- [ ] Implement `test_freeze_complete_time_consistency()` - verifies frozen values used at display
- [ ] Implement `test_deferred_completion_preserves_frozen_state()` - verifies full pattern
- [ ] Run full test suite

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/builder/tests/unit/test_progress_bar_ordering.py` - Add integration tests

**Verification**:
- All new tests pass
- Existing tests still pass

---

### Phase 4: Type Hints and Constants [NOT STARTED]

**Goal**: Add type hints and named constants for maintainability

**Tasks**:
- [ ] Add class constants to `TimeBasedProgress`:
  - `ANIMATION_INTERVAL_SEC = 0.1`
  - `THREAD_JOIN_TIMEOUT_SEC = 0.5`
- [ ] Add explicit return type hints to public methods
- [ ] Replace magic numbers with constants in implementation

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/output/progress/animated.py` - Add constants and type hints

**Verification**:
- All tests pass
- Type checker (mypy) passes on modified file

---

### Phase 5: Documentation and State Machine Contract [NOT STARTED]

**Goal**: Document the progress bar state machine and caller contract

**Tasks**:
- [ ] Add state machine documentation to `TimeBasedProgress` class docstring
- [ ] Document the freeze-then-complete pattern in `core.py` docstring
- [ ] Add inline comments explaining the timing synchronization

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/output/progress/animated.py` - Update class docstring
- `code/src/model_checker/output/progress/core.py` - Document caller contract

**Verification**:
- Documentation is clear and accurate
- Code review confirms clarity improvements

---

### Phase 6: Final Verification [NOT STARTED]

**Goal**: Comprehensive testing and cleanup

**Tasks**:
- [ ] Run full test suite: `pytest code/src/model_checker/`
- [ ] Run progress-specific tests with verbose output
- [ ] Manual test with actual model iteration to verify visual output
- [ ] Review all changes for consistency

**Timing**: 15 minutes

**Files to modify**:
- None (verification only)

**Verification**:
- All tests pass
- Manual verification shows correct bar fill and elapsed time match
- No regressions in existing functionality

## Testing & Validation

- [ ] All existing tests in `test_progress_animated.py` pass
- [ ] All existing tests in `test_progress_bar_ordering.py` pass
- [ ] New `test_freeze_elapsed_time_consistency()` passes
- [ ] New integration tests pass
- [ ] Manual test with `--iterate 3` shows consistent fill/time per model
- [ ] Type checking passes (if mypy configured)

## Artifacts & Outputs

- `plans/01_implementation-plan.md` (this file)
- `summaries/01_execution-summary.md` (upon completion)

## Rollback/Contingency

If implementation causes regressions:
1. Revert changes to `animated.py`
2. Keep new tests (they document expected behavior)
3. Re-analyze the timing flow with additional debug logging
4. Consider alternative approach: recalculate fill at complete time (simpler but different UX)
