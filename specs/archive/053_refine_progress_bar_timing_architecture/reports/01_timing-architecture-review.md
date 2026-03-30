# Progress Bar Timing Architecture Review

## Executive Summary

The progress bar system has a fundamental timing inconsistency: the visual fill fraction is frozen at model-found time via `freeze_at_current()`, but the displayed elapsed time text is calculated at `complete()` time. This creates confusing output where bars show (e.g.) 10% fill but 0.6s elapsed time when the difference calculation takes ~500ms between freeze and display.

## Research Questions and Findings

### 1. Root Cause of Fill Fraction vs Displayed Time Inconsistency

**Root Cause**: The `complete()` method in `TimeBasedProgress` uses two different time references:

```python
# animated.py lines 243-263
def complete(self, success: bool = True) -> None:
    # ...
    if self.start_time is None:
        elapsed = 0.0
    else:
        elapsed = time.time() - self.start_time  # CURRENT time

    if success:
        if self._frozen:
            bar = self._generate_bar(self.fill_fraction)  # FROZEN time
        else:
            bar = self._generate_bar(1.0)

        msg = f"Finding non-isomorphic models: {bar} ... {elapsed:.1f}s"  # Mismatch!
```

**Timeline showing the mismatch**:

```
T=0.0s: Progress bar starts (start_time recorded)
T=0.1s: Model found
T=0.1s: freeze_at_current() called -> fill_fraction = 0.1/60 = 0.17% (nearly empty bar)
T=0.1s-0.6s: Difference calculation runs (iterate/core.py lines 378-383)
T=0.6s: complete() called -> elapsed = 0.6s (but bar shows nearly empty)

Result: "[░░░░░░░░░░░░░░░░░░░░] 2/4 0.6s" - confusing!
```

**Code path**:
1. `iterate/core.py` line 375: `stop_animation_only()` freezes fill at model-found time
2. `iterate/core.py` lines 378-383: `DifferenceCalculator.calculate_differences()` runs
3. `iterate/core.py` line 400: Model yielded
4. `runner.py` line 639: `complete_model_search(found=True)` prints with current elapsed time

### 2. Best Solution: Recalculate Fill vs Use Frozen Timestamp

**Recommended Solution: Use frozen timestamp for display (Option B)**

**Option A: Recalculate fill at complete() time**
- Pros: Fill and time always match
- Cons: Bar jumps from (e.g.) 10% to 100% between freeze and complete, defeating the purpose of showing actual search time

**Option B: Store and use frozen elapsed time for display**
- Pros: Both fill and time reflect actual search duration at model-found time
- Cons: Requires storing frozen_elapsed in addition to fill_fraction

**Implementation for Option B**:

```python
# In TimeBasedProgress.freeze_at_current():
def freeze_at_current(self) -> float:
    self._frozen = True
    if self.start_time is None:
        self.fill_fraction = 0.0
        self._frozen_elapsed = 0.0
    else:
        elapsed = time.time() - self.start_time
        self.fill_fraction = min(1.0, elapsed / self.timeout)
        self._frozen_elapsed = elapsed  # NEW: store frozen elapsed
    # ... rest of method
    return self.fill_fraction

# In TimeBasedProgress.complete():
def complete(self, success: bool = True) -> None:
    # ... existing code ...

    if self._frozen:
        elapsed = self._frozen_elapsed  # Use frozen time, not current
        bar = self._generate_bar(self.fill_fraction)
    else:
        elapsed = time.time() - self.start_time
        bar = self._generate_bar(1.0)

    msg = f"Finding non-isomorphic models: {bar} ... {elapsed:.1f}s"
```

### 3. Timing Architecture Consolidation

**Current Architecture Issues**:

The system has two code paths for stopping progress bars:

| Code Path | Location | Purpose | When Used |
|-----------|----------|---------|-----------|
| `_stop_progress_animation()` | `runner.py:496-506` | Wrapper for first model | First model in `_process_with_iterations` |
| `stop_animation_only()` | `core.py:156-174` | Direct freeze | Subsequent models in `iterate/core.py` |

**Both paths call the same underlying method**, so consolidation is not about reducing code paths but about:

1. **Clarifying ownership**: Who is responsible for calling freeze vs complete?
2. **Documenting the contract**: The freeze-then-complete pattern must be followed

**Proposed Documentation Contract**:

```
Progress Bar State Machine:
  IDLE -> start() -> ANIMATING
  ANIMATING -> freeze_at_current() -> FROZEN (fill captured, animation stopped)
  FROZEN -> complete(True) -> COMPLETED (prints final bar with frozen values)
  ANIMATING -> complete(False) -> CLEARED (no final bar printed)

Caller Contract:
  - Runner owns first model: start_model_search() -> freeze -> output -> complete()
  - Iterator owns subsequent models: [start called by UnifiedProgress] -> freeze -> yield -> [runner calls complete]
```

**Fragility Assessment**:

The timing model is fragile because:
1. The elapsed time semantic differs between animation loop and complete()
2. The _frozen flag affects fill calculation but not time calculation
3. The deferred completion pattern requires careful caller coordination

**Consolidation Recommendations**:

1. Store `_frozen_elapsed` alongside `fill_fraction` in `freeze_at_current()`
2. Use `_frozen_elapsed` in `complete()` when `_frozen` is True
3. Add a `get_frozen_state()` method to expose both values together
4. Consider a ProgressState dataclass to encapsulate frozen values

### 4. Tests for Bar->Output->Bar Ordering

**Current Test Coverage**:

- `test_progress_bar_ordering.py`: Tests the deferred completion pattern
- `test_progress_animated.py`: Tests `freeze_at_current()` and fill fraction

**Missing Integration Tests**:

```python
# Proposed new tests in test_progress_bar_ordering.py

class TestBarOutputBarOrdering(unittest.TestCase):
    """Integration tests for bar -> output -> bar ordering."""

    def test_multi_model_output_ordering(self):
        """Test that output ordering is bar -> header -> bar -> header for multi-model runs.

        Expected output sequence for 3 models:
        1. [animated progress bar clears]
        2. [progress bar 1/3] <- complete() after freeze
        3. MODEL 1 header and content
        4. [animated progress bar clears]
        5. [progress bar 2/3] <- complete() after freeze
        6. MODEL 2 header and content
        7. ... and so on
        """
        pass

    def test_freeze_complete_time_consistency(self):
        """Test that frozen fill fraction and displayed time are consistent.

        When freeze_at_current() captures 30% fill (0.3s of 1.0s timeout),
        complete() should display "0.3s", not current elapsed time.
        """
        pass

    def test_generator_iteration_ordering(self):
        """Test ordering when using iterate_generator() in core.py.

        Verifies that stop_animation_only() in iterate/core.py line 375
        coordinates correctly with complete_model_search() called later.
        """
        pass
```

**Test Implementation Strategy**:

1. Use `io.StringIO` to capture output
2. Track call order with timestamps or sequence numbers
3. Parse output to verify bar appears before header for each model
4. Verify elapsed time in bar text matches fill fraction (within tolerance)

### 5. Quality and Maintainability Improvements

**Issue 1: Implicit State Coupling**

The `_frozen` flag controls fill calculation but not time calculation. This creates an implicit contract that's easy to violate.

**Fix**: Create explicit frozen state:

```python
@dataclass
class FrozenProgressState:
    """Captured progress state at freeze time."""
    fill_fraction: float
    elapsed_seconds: float
    timestamp: float

class TimeBasedProgress:
    def freeze_at_current(self) -> FrozenProgressState:
        elapsed = time.time() - self.start_time if self.start_time else 0.0
        self._frozen_state = FrozenProgressState(
            fill_fraction=min(1.0, elapsed / self.timeout),
            elapsed_seconds=elapsed,
            timestamp=time.time()
        )
        return self._frozen_state
```

**Issue 2: Thread Safety Concerns**

The `fill_fraction` attribute is written by `freeze_at_current()` and read by `complete()`, potentially on different threads (though typically the animation thread is stopped first).

**Fix**: Use threading.Lock or ensure sequential access is documented and enforced.

**Issue 3: Missing Type Hints**

Several methods lack return type hints or parameter types, making the API less discoverable.

**Fix**: Add comprehensive type hints:

```python
def freeze_at_current(self) -> float: ...
def complete(self, success: bool = True) -> None: ...
def stop_animation_only(self) -> float: ...
```

**Issue 4: Magic Numbers**

The code uses several magic numbers (0.5s timeout for thread join, 0.1s animation interval).

**Fix**: Define as class constants with documentation:

```python
class TimeBasedProgress:
    ANIMATION_INTERVAL_SEC = 0.1  # Update frequency
    THREAD_JOIN_TIMEOUT_SEC = 0.5  # Max wait for thread cleanup
```

## Implementation Priority

1. **Critical (P0)**: Fix fill/elapsed time inconsistency - store `_frozen_elapsed`
2. **High (P1)**: Add integration tests for bar->output->bar ordering
3. **Medium (P2)**: Add type hints and constants
4. **Low (P3)**: Refactor to FrozenProgressState dataclass

## Affected Files

| File | Change Type | Description |
|------|-------------|-------------|
| `output/progress/animated.py` | Modify | Add `_frozen_elapsed`, update `complete()` |
| `output/progress/core.py` | Minor | Update docstrings for contract |
| `builder/tests/unit/test_progress_bar_ordering.py` | Add | Integration tests |
| `output/tests/unit/test_progress_animated.py` | Add | Test for elapsed time consistency |

## Appendix: Call Graph

```
_process_with_iterations() [runner.py]
  |
  +-> start_model_search(1) [core.py]
  |     +-> TimeBasedProgress() [animated.py]
  |     +-> start() - animation begins
  |
  +-> BuildExample() - Z3 search runs
  |
  +-> _stop_progress_animation() [runner.py]
  |     +-> stop_animation_only() [core.py]
  |           +-> freeze_at_current() [animated.py] - FREEZE TIME
  |
  +-> _capture_and_save_output() - header printed
  |
  +-> complete_model_search(True) [core.py]
        +-> complete(True) [animated.py] - DISPLAY TIME (should match freeze)

For iterate_generator() [iterate/core.py]:
  |
  +-> stop_animation_only() [line 375] - FREEZE TIME
  |
  +-> DifferenceCalculator.calculate_differences() [lines 378-383]
  |     (takes ~500ms)
  |
  +-> yield new_structure [line 400]
  |
  +-> [runner.py _run_generator_iteration]
        +-> complete_model_search(True) [line 639] - DISPLAY TIME
```
