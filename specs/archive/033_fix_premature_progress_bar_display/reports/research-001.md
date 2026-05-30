# Research Report: Task #33

**Task**: 33 - fix_premature_progress_bar_display
**Started**: 2026-03-03
**Completed**: 2026-03-03
**Effort**: Small (2-4 hours implementation)
**Dependencies**: None
**Sources/Inputs**: Codebase analysis
**Artifacts**: This research report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- The progress bar for model 1 appears BEFORE the example header because `_process_with_iterations` starts progress tracking before calling `_capture_and_save_output`
- The issue only affects examples with `iterate > 1` - regular single-model examples use a Spinner that clears itself
- **Recommended fix**: Use Spinner for model 1 instead of TimeBasedProgress, matching the single-model case pattern
- Alternative: Suppress progress bar output for model 1 entirely, since it's nearly instant

## Context & Scope

When running examples with `iterate > 1`, the iteration progress bar (showing "Finding non-isomorphic models: [##...] 1/2 0.1s") appears in the output BEFORE the example's header (the `========` line and "EXAMPLE NAME: there is a countermodel." message).

**Observed in output/test.md (lines 20-26)**:
```
========================================   <-- closing FO_TH_1

Finding non-isomorphic models: [##...] 1/2 0.1s   <-- PROBLEM: progress bar here

========================================   <-- opening FO_CM_1

EXAMPLE FO_CM_1: there is a countermodel.  <-- header after progress bar
```

The progress bar visually belongs to the NEXT example, creating user confusion.

## Findings

### Root Cause Analysis

The issue is in `_process_with_iterations` (runner.py:388-450):

```python
def _process_with_iterations(...):
    # Line 411: Creates progress tracker
    progress = self._create_progress_tracker(example_case, iterate_count)

    # Line 414-416: Starts progress bar BEFORE model is built
    print()  # Add vertical space
    model_1_start = time.time()
    progress.start_model_search(1, start_time=model_1_start)  # STARTS ANIMATED BAR

    # Line 418: Builds the model (Z3 solving happens here)
    example = BuildExample(self.build_module, semantic_theory, example_case, theory_name)

    # Line 431: Completes progress bar - PRINTS FINAL STATE
    progress.complete_model_search(found=True)
    # ^^ This prints the progress bar as a permanent line

    # Line 428 (failure) or later: Calls print_model which prints header
    self.build_module._capture_and_save_output(example, example_name, theory_name)
```

The call sequence is:
1. `progress.start_model_search(1)` - starts animated `TimeBasedProgress` in background thread
2. `BuildExample(...)` - builds the model (Z3 solving)
3. `progress.complete_model_search(found=True)` - stops animation and **prints final progress state**
4. `_capture_and_save_output()` - eventually calls `print_model()` which prints the header

The progress bar's final state is printed at step 3, but the example header isn't printed until step 4.

### TimeBasedProgress.complete() Behavior

In `animated.py:189-220`, `complete()`:
1. Stops the animation thread
2. **Clears the animation line** (line 200)
3. **Prints the final state as a permanent line** (lines 207-220)

```python
def complete(self, success: bool = True) -> None:
    self.found = success
    self.active = False
    # ... stop thread ...
    self.display.clear()  # Clear animation

    if success:
        # Print final state as permanent line
        bar = "[" + "##" * 20 + "]"
        msg = f"Finding non-isomorphic models: {bar} 1/2 0.1s"
        self.display.update(msg)
        self.display.complete()  # Adds newline, making it permanent
```

### Comparison: How Single-Model Examples Work

In `run_model_check` (runner.py:135-172), single-model examples use a `Spinner`:

```python
def run_model_check(...):
    spinner = Spinner()
    spinner.start()
    try:
        example = BuildExample(...)
        return example
    finally:
        spinner.stop()  # CLEARS the spinner line - no permanent output
```

The `Spinner.stop()` method (spinner.py:65-81) clears its line without leaving any output:
```python
def stop(self) -> None:
    self._active = False
    # ...
    self.stream.write("\r" + " " * 50 + "\r")  # Clear line
    self.stream.flush()
```

### Why Model 1 Has Different Behavior

For examples with `iterate > 1`:
- Model 1 is tracked via `UnifiedProgress.start_model_search(1)` which creates a `TimeBasedProgress`
- `TimeBasedProgress.complete(success=True)` prints a permanent progress line
- Models 2+ also use `TimeBasedProgress` but appear AFTER the header (correct position)

The asymmetry is that model 1's progress bar is created before the example is processed, while subsequent models' progress bars appear within the iteration loop which happens AFTER the initial output.

## Recommendations

### Option 1: Use Spinner for Model 1 (Recommended)

Match the single-model pattern by using `Spinner` for model 1's initial solve:

```python
def _process_with_iterations(...):
    # Use spinner for initial model (like _process_single_model does)
    spinner = Spinner()
    spinner.start()
    try:
        example = BuildExample(...)
    finally:
        spinner.stop()  # Clears line

    # Print the example header FIRST
    self.build_module._capture_and_save_output(example, example_name, theory_name)

    # THEN create progress tracker for remaining models (2+)
    if iterate_count > 1:
        progress = self._create_progress_tracker(example_case, iterate_count)
        progress.models_found = 1  # Already found model 1
        self.process_iterations(...)
```

**Pros**:
- Consistent with single-model behavior
- Simple implementation
- No visual progress for model 1 (which is typically fast)

**Cons**:
- Loses progress feedback for model 1 (acceptable since it's usually fast)

### Option 2: Suppress Model 1 Final Display

Modify `TimeBasedProgress.complete()` to optionally skip the final display:

```python
def complete(self, success: bool = True, suppress_output: bool = False) -> None:
    # ... stop animation ...
    self.display.clear()

    if success and not suppress_output:
        # Print final state
        ...
```

Then call `progress.complete_model_search(found=True, suppress_output=True)` for model 1.

**Pros**:
- Keeps progress tracking infrastructure
- Minimal code change

**Cons**:
- Progress bar still animates before header (slightly confusing)
- Adds complexity to the API

### Option 3: Move Header Print Before Progress (Complex)

Restructure to print the header before starting any progress:

```python
def _process_with_iterations(...):
    # Print header first (requires extracting header printing from BuildExample)
    self._print_example_header(example_name, theory_name)

    # Then start progress
    progress = self._create_progress_tracker(...)
    progress.start_model_search(1)
    example = BuildExample(...)
```

**Pros**:
- Keeps full progress feedback
- Correct visual ordering

**Cons**:
- Requires significant refactoring (header printing is currently tied to model building)
- Header content depends on model result ("countermodel" vs "no countermodel")
- Would need to handle header differently for found vs not-found cases

## Implementation Recommendation

**Use Option 1** (Spinner for model 1). It's the simplest fix with the cleanest result:

1. Replace `UnifiedProgress.start_model_search(1)` with `Spinner` for the initial model
2. Print the example output (header) after model 1 is complete
3. Only start `UnifiedProgress` for models 2+ during iteration

Changes required:
- `runner.py:_process_with_iterations()` - Use Spinner for model 1, restructure progress tracking
- Possibly `UnifiedProgress` - May need to support starting from model 2 instead of model 1

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Regression in iteration output format | Low | Medium | Comprehensive testing with iterate=2,3,10 |
| Progress bar timing accuracy affected | Low | Low | Use timing from iterator, not initial solve |
| Interactive mode affected | Medium | Medium | Test both batch and interactive modes |

## Appendix

### Key Files

| File | Location | Role |
|------|----------|------|
| runner.py | code/src/model_checker/builder/runner.py | Contains `_process_with_iterations` |
| core.py | code/src/model_checker/output/progress/core.py | `UnifiedProgress` class |
| animated.py | code/src/model_checker/output/progress/animated.py | `TimeBasedProgress.complete()` |
| spinner.py | code/src/model_checker/output/progress/spinner.py | `Spinner` class |
| structure.py | code/src/model_checker/models/structure.py | `_print_section_header()` |

### Code References

**_process_with_iterations** (runner.py:388-450):
- Line 411: Creates progress tracker
- Line 416: Starts model 1 progress bar
- Line 418: Builds model
- Line 431: Completes model 1 progress (prints final state)
- Line 428: Calls output capture (prints header)

**TimeBasedProgress.complete** (animated.py:189-220):
- Line 200: Clears animation
- Line 207-220: Prints final progress state as permanent line

**Spinner.stop** (spinner.py:65-81):
- Line 80: Clears line without permanent output
