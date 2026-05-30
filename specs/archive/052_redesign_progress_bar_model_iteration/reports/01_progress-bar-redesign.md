# Research Report: Progress Bar Redesign for Non-Isomorphic Model Iteration

## Executive Summary

The current progress bar implementation has two architectural issues that prevent achieving the desired user experience of sequential "bar -> output -> bar -> output" display:

1. **Bar fill semantics**: `TimeBasedProgress.complete()` fills the bar to 100% regardless of actual elapsed time
2. **Control flow split**: Progress bars for models 2+ are managed by `iterate/core.py` but completed BEFORE yielding, while display is managed by `runner.py` AFTER receiving the yield

## Current Architecture

### Component Responsibilities

| Component | Role | Progress Management |
|-----------|------|---------------------|
| `runner.py` | Display orchestration | Creates progress tracker, manages model 1 |
| `iterate/core.py` | Model iteration | Manages progress for models 2+ |
| `progress/animated.py` | TimeBasedProgress | Animated bar with time-based fill |
| `progress/core.py` | UnifiedProgress | Coordination layer for all progress bars |
| `progress/display.py` | TerminalDisplay | Low-level terminal output |

### Progress Bar Flow: Model 1

```
runner.py:_process_with_iterations()
    |
    +-- progress = _create_progress_tracker()
    +-- print()  # vertical space
    +-- progress.start_model_search(1, start_time)
    +-- example = BuildExample()  # Z3 search happens here
    +-- progress.model_checked()
    +-- _stop_progress_animation(progress)  # Stops thread, clears display
    +-- _capture_and_save_output()  # Prints model header + output
    +-- progress.complete_model_search(found=True)  # Prints final bar
    +-- print()  # vertical space
    +-- process_iterations()  # For models 2+
```

### Progress Bar Flow: Models 2+

```
iterate/core.py:iterate_generator()
    |
    +-- Initialize: current_search_start, current_search_checked, current_search_skipped
    |
    +-- LOOP (while current_iteration < max_iterations):
    |   |
    |   +-- model_number = len(model_structures) + 1
    |   +-- search_progress.start_model_search(model_number, start_time)  # Line 242
    |   |       ^-- Starts animated progress bar
    |   |
    |   +-- [Z3 constraint generation and satisfiability check]
    |   +-- search_progress.model_checked()  # Line 258
    |   +-- [Isomorphism detection loop with model_skipped_isomorphic()]
    |   |
    |   +-- search_progress.complete_model_search(found=True)  # Line 374
    |   |       ^-- PROBLEM: Completes bar BEFORE yield
    |   |       ^-- Also fills bar to 100% regardless of elapsed time
    |   |
    |   +-- yield new_structure  # Line 399
    |       ^-- Model yielded to runner.py
    |
runner.py:_run_generator_iteration()
    |
    +-- for structure in model_generator:
        +-- structure.print_model_differences()
        +-- print(f"MODEL {count}/{total}")
        +-- _capture_and_save_output()  # Display after bar already completed
```

## Issue Analysis

### Issue 1: Bar Fills to 100% on Completion

Location: `output/progress/animated.py`, lines 189-227

```python
def complete(self, success: bool = True) -> None:
    # ...
    if success:
        # Fill bar completely with color if supported
        if self.use_color:
            bar = f"[{PROGRESS_COLOR}{'█' * 20}{COLOR_RESET}]"  # <-- Always 100%
        else:
            bar = "[" + "█" * 20 + "]"  # <-- Always 100%
```

**Problem**: When a model is found at 30% of the timeout, the bar still shows 100% fill.

**Required behavior**: Bar should freeze at the actual elapsed fraction (e.g., 30% fill if found at 30% of timeout).

### Issue 2: Complete Called Before Yield

Location: `iterate/core.py`, lines 372-399

```python
# Line 374: Complete search as found
if self.search_progress:
    self.search_progress.complete_model_search(found=True)

# ... (difference calculation, statistics) ...

# Line 399: YIELD the model instead of just collecting
yield new_structure
```

**Problem**: The iterator calls `complete_model_search()` before yielding the model. This means:
1. Progress bar prints its final state
2. Then model is yielded to runner
3. Runner displays model output AFTER the bar is already printed

**Required behavior**: Bar should complete -> model output should print -> THEN next bar should start.

### Issue 3: No Runner Control Over Model 2+ Progress

Location: `runner.py:_run_generator_iteration()`, lines 607-676

The generator interface gives runner no opportunity to:
1. Stop the animation before the model is yielded
2. Print the model output
3. Then complete the progress bar

The iterator owns the progress lifecycle for models 2+, but runner owns the display.

## Data Flow Diagram

```
                    MODEL 1                                    MODELS 2+
                    ========                                   ==========

runner.py           runner.py                                  iterate/core.py
    |                   |                                           |
    |   start_model_search(1)                          start_model_search(N)
    |          |                                                    |
    |          v                                                    v
    |   [TimeBasedProgress                             [TimeBasedProgress
    |    animates in thread]                            animates in thread]
    |          |                                                    |
    |   BuildExample()                                 [Z3 search loop]
    |          |                                                    |
    |   _stop_progress_animation()                          (no stop!)
    |          |                                                    |
    |   _capture_and_save_output()                    complete_model_search()
    |          |                                           |    ^-- BAR PRINTS
    |   complete_model_search()                            |
    |          |    ^-- BAR PRINTS                         v
    |          |                                       yield structure
    |          v                                                    |
    |   process_iterations() --------------------------> for structure in gen:
    |                                                           |
    |                                                    print differences
    |                                                           |
    |                                                    print MODEL header
    |                                                           |
    |                                                    _capture_and_save_output()
    |                                                           |    ^-- OUTPUT PRINTS
    |                                                           v        (TOO LATE!)
```

## Proposed Solutions

### Solution A: Move Progress Completion to Runner (Recommended)

**Concept**: Iterator yields model WITHOUT completing progress; runner handles completion after displaying output.

**Changes required**:

1. **iterate/core.py**: Remove `complete_model_search()` call before yield
   - Instead, stop the animation thread without printing final bar
   - Add method like `stop_animation_only()` to UnifiedProgress

2. **runner.py**: Add progress completion after model output
   ```python
   for structure in model_generator:
       # Display model output
       structure.print_model_differences()
       print(f"MODEL {count}/{total}")
       _capture_and_save_output()

       # NOW complete the progress bar
       progress.complete_model_search(found=True)

       # Start next search progress bar immediately
       if more_expected:
           progress.start_model_search(next_num)
   ```

3. **animated.py**: Add method to freeze bar at current fill
   ```python
   def freeze_at_current(self) -> float:
       """Stop animation and return current fill fraction."""
       elapsed = time.time() - self.start_time
       self.fill_fraction = min(1.0, elapsed / self.timeout)
       self.active = False
       if self.thread and self.thread.is_alive():
           self.thread.join(timeout=0.5)
       return self.fill_fraction
   ```

4. **animated.py**: Modify `complete()` to use stored fill fraction
   ```python
   def complete(self, success: bool = True) -> None:
       # Use stored fill_fraction instead of 100%
       fill = getattr(self, 'fill_fraction', 1.0)
       bar = self._generate_bar(fill)
       # ... rest of completion
   ```

### Solution B: Yield Progress Control Object

**Concept**: Iterator yields both the model and a progress control object that runner can use.

```python
# iterate/core.py
class ModelWithProgress:
    def __init__(self, structure, complete_fn):
        self.structure = structure
        self.complete_progress = complete_fn

# In iterate_generator:
def make_completer():
    def complete():
        self.search_progress.complete_model_search(found=True)
    return complete

yield ModelWithProgress(new_structure, make_completer())
```

**Pros**: Cleaner interface, explicit progress ownership transfer
**Cons**: More invasive API change, affects all consumers of generator

### Solution C: Event-Based Communication

**Concept**: Use callbacks or events for progress completion.

```python
# Pass callback to iterator
def on_model_display_complete(model_number):
    progress.complete_model_search(found=True)

for structure in theory_iterate_example(example, on_display=on_model_display_complete):
    # display logic
    on_model_display_complete(structure.model_number)
```

**Pros**: Flexible, testable
**Cons**: Adds complexity, callback timing is error-prone

## Recommended Implementation Path

### Phase 1: Fix Fill Semantics (Low Risk)

1. Add `fill_fraction` attribute to TimeBasedProgress
2. Capture elapsed time on completion
3. Modify `complete()` to use actual elapsed fraction

**Files changed**: `output/progress/animated.py`

### Phase 2: Add Animation Freeze Method (Low Risk)

1. Add `freeze_at_current()` method to TimeBasedProgress
2. Add `stop_animation_only()` method to UnifiedProgress
3. Test with existing progress bar tests

**Files changed**: `output/progress/animated.py`, `output/progress/core.py`

### Phase 3: Refactor Iterator Progress Control (Medium Risk)

1. Iterator calls `stop_animation_only()` instead of `complete_model_search()`
2. Iterator exposes progress object via the yielded structure or separate channel
3. Runner calls `complete_model_search()` after output

**Files changed**: `iterate/core.py`, `builder/runner.py`

### Phase 4: Integration Testing (Required)

1. Test sequential output: bar -> model -> bar -> model
2. Test fill levels freeze at actual elapsed time
3. Test timeout behavior (no bar printed on timeout)
4. Test single model case
5. Test keyboard interrupt handling

## Edge Cases to Handle

### Case 1: Only 1 Model Found (When 4 Requested)

- Bar for model 2 should complete without snapping to 100%
- No bar for models 3, 4 should appear
- Iteration report should indicate exhausted search space

### Case 2: Iteration Timeout

- Current bar should freeze at timeout fill (100%)
- No final model output for timed-out search
- Next model search should not start

### Case 3: Keyboard Interrupt

- Active progress bar should be cleaned up
- Partial results should be preserved
- No orphaned animation threads

### Case 4: Very Fast Model Discovery

- If model found in <100ms, bar might not have updated much
- Should still show non-zero fill based on actual elapsed time
- Animation thread cleanup must not race with completion

## Test Strategy

### Unit Tests

```python
def test_progress_bar_freezes_at_actual_fill():
    """Bar should show 30% fill when found at 30% of timeout."""
    bar = TimeBasedProgress(timeout=10.0, ...)
    bar.start()
    time.sleep(3.0)  # 30% of timeout
    fill = bar.freeze_at_current()
    assert 0.25 <= fill <= 0.35  # Allow for timing variance

def test_complete_uses_frozen_fill():
    """Complete should use frozen fill, not 100%."""
    bar = TimeBasedProgress(timeout=10.0, ...)
    bar.start()
    bar.fill_fraction = 0.3  # Simulate freeze
    bar.complete(success=True)
    # Assert output shows ~30% fill
```

### Integration Tests

```python
def test_sequential_bar_output_ordering():
    """Bar -> model output -> bar -> model output."""
    output_tracker = OutputTracker()
    # Run iteration
    # Assert events appear in correct order
```

## Appendix: Key Code Locations

| File | Line | Purpose |
|------|------|---------|
| `output/progress/animated.py` | 189-227 | `TimeBasedProgress.complete()` - fills to 100% |
| `output/progress/animated.py` | 157-174 | `_generate_bar()` - creates bar visualization |
| `output/progress/core.py` | 86-127 | `start_model_search()` - creates TimeBasedProgress |
| `output/progress/core.py` | 148-154 | `complete_model_search()` - delegates to bar.complete() |
| `iterate/core.py` | 372-374 | Calls `complete_model_search()` before yield |
| `iterate/core.py` | 399 | Yields model structure |
| `builder/runner.py` | 607-676 | `_run_generator_iteration()` - display loop |
| `builder/runner.py` | 495-512 | `_stop_progress_animation()` - manual animation stop |

## Conclusion

The redesign requires coordinating changes across three layers:

1. **Progress bar layer**: Fix fill semantics to freeze at actual elapsed time
2. **Iterator layer**: Separate animation stop from completion printing
3. **Runner layer**: Take control of completion timing after model display

Solution A (move completion to runner) is recommended as it:
- Maintains clear separation of concerns (iterator finds models, runner displays them)
- Requires minimal API changes
- Preserves existing test infrastructure
- Allows incremental implementation

The phased approach allows validating each change independently before integration.
