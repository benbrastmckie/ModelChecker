# Research Report: Task #33 (Revision 002)

**Task**: 33 - fix_premature_progress_bar_display
**Started**: 2026-03-03
**Completed**: 2026-03-03
**Effort**: Small (2-4 hours implementation)
**Dependencies**: None
**Sources/Inputs**: Codebase analysis, user clarification
**Artifacts**: This research report (revision 002)
**Standards**: report-format.md, subagent-return.md

## CRITICAL CORRECTION FROM USER

The previous research (research-001.md) recommended **Option 1: Use Spinner for Model 1**. This recommendation was **WRONG**.

**User clarification**: "The problem is not the permanence of the progress bar (that is good) I just need it to print in the correct spot (after the example header, before each model is found and printed)."

**Correct understanding**:
- Progress bar permanence is GOOD - keep it
- The problem is ONLY the print ORDER/SEQUENCE
- Progress bar should appear AFTER the example header ("========" and "EXAMPLE NAME:")
- Progress bar should appear BEFORE each model output
- Option 1 (Spinner) would REMOVE the progress bar - that is NOT what the user wants

## Revised Executive Summary

- The progress bar for model 1 appears BEFORE the example header - this is a SEQUENCE problem, not a display problem
- The fix requires restructuring `_process_with_iterations` to print header BEFORE starting progress bar
- Challenge: Header includes "countermodel" status which requires Z3 result
- **Recommended fix**: Split header printing - print static header before Z3, print result after

## Desired Output Sequence

```
========================================
EXAMPLE FO_CM_1: there is a countermodel.  <-- HEADER FIRST

[state space info]
[premises/conclusions]

Finding non-isomorphic models: [##########] 1/2 0.1s   <-- PROGRESS BAR AFTER HEADER

[model 1 output]

Finding non-isomorphic models: [##########] 2/2 0.3s   <-- PROGRESS BAR FOR MODEL 2

[model 2 output]
========================================
```

## Root Cause Analysis

### Current Sequence (INCORRECT)

In `_process_with_iterations` (runner.py:388-450):

```
Line 414:  print()                              # vertical space
Line 416:  progress.start_model_search(1)       # STARTS progress bar animation
Line 418:  example = BuildExample(...)          # Z3 runs here
Line 431:  progress.complete_model_search()     # PRINTS permanent progress bar
Line 432:  print()                              # vertical space
Line 439:  _handle_iteration_mode()             # --> _capture_and_save_output()
                                                # --> print_model() --> print header
```

**Problem**: Progress bar is printed at line 431, BEFORE the header is printed in `_handle_iteration_mode()`.

### Where Header Printing Happens

`_capture_and_save_output` (module.py:206-208):
```python
if not self.output_manager.should_save():
    example.print_model(example_name, theory_name)  # <-- prints header + model
```

`print_model` (example.py:277-303) calls `model_structure.print_to()` which calls:

`print_info` (structure.py:766-799) which calls:

`_print_section_header` (structure.py:801-804):
```python
def _print_section_header(self, example_name: str, header: str, output: TextIO) -> None:
    print(f"{'='*40}", file=output)
    print(f"\nEXAMPLE {example_name}: {header}\n", file=output)
```

**Key insight**: The header message depends on `model_status` ("there is a countermodel" vs "there is no countermodel"), which is only known AFTER Z3 completes.

## Recommendations (Revised)

### Option A: Split Header Printing (Recommended)

Print the static header portion BEFORE Z3, then print the result portion AFTER.

**Before Z3** (in `_process_with_iterations`):
```python
# Print opening divider and example name
print(f"{'='*40}")
print(f"\nEXAMPLE {example_name}:")  # Note: no result yet
```

**After Z3 but BEFORE progress bar completes**:
```python
# Append the result to the same line or next line
result_msg = "there is a countermodel." if found else "there is no countermodel."
print(f" {result_msg}\n")
# Print state space info, settings, premises, conclusions...
```

**Then progress bar**:
```python
progress.complete_model_search(found=True)  # Progress bar appears here
```

**Pros**:
- Keeps full progress bar functionality
- Header appears in correct position
- Maintains visual feedback during search

**Cons**:
- Requires extracting header printing logic from `print_info`
- Need to handle the split carefully for both save and non-save modes
- May need to refactor `_print_section_header` or duplicate some code

### Option B: Defer Progress Bar Completion

Don't call `progress.complete_model_search()` until AFTER the header is printed.

```python
def _process_with_iterations(...):
    progress = self._create_progress_tracker(...)
    progress.start_model_search(1)

    example = BuildExample(...)  # Z3 runs

    # DON'T complete progress here
    # Instead, pass progress to _handle_iteration_mode

    # Print header FIRST
    self.build_module._capture_and_save_output(example, example_name, theory_name)

    # THEN complete progress (prints permanent bar)
    progress.complete_model_search(found=example.model_structure.z3_model_status)
```

**Pros**:
- Minimal changes to existing code
- Progress bar still animates during Z3
- Final bar prints after header

**Cons**:
- Animation continues during header printing (may look slightly odd)
- Need to coordinate timing carefully

### Option C: Buffer Progress Output

Modify `TimeBasedProgress.complete()` to buffer its output, then print it at a specific point.

```python
class TimeBasedProgress:
    def complete(self, success: bool = True, buffer: bool = False) -> str:
        # Stop animation, compute final state
        # If buffer=True, return the string instead of printing
        # Otherwise print as before
```

Then in runner:
```python
progress.start_model_search(1)
example = BuildExample(...)
buffered_progress = progress.complete_model_search(found=True, buffer=True)

# Print header
self.build_module._capture_and_save_output(example, example_name, theory_name)

# Print buffered progress
print(buffered_progress)
```

**Pros**:
- Clean separation of concerns
- Flexible for future use

**Cons**:
- More complex implementation
- Changes the progress API

## Implementation Recommendation

**Use Option B: Defer Progress Bar Completion**

This is the simplest fix that achieves the desired result:

1. Keep progress bar animating during Z3 search
2. When model found, DON'T immediately call `complete_model_search()`
3. Print the header via `_capture_and_save_output()`
4. THEN call `complete_model_search()` to print the permanent progress bar

### Changes Required

**runner.py:_process_with_iterations()**:
```python
def _process_with_iterations(...):
    from model_checker.builder.example import BuildExample

    progress = self._create_progress_tracker(example_case, iterate_count)

    # Start progress tracking
    print()
    model_1_start = time.time()
    progress.start_model_search(1, start_time=model_1_start)

    # Build model (Z3 runs)
    example = BuildExample(self.build_module, semantic_theory, example_case, theory_name)
    progress.model_checked()

    self._store_timing_info(example, model_1_start)

    # Check if model was found
    found = example.model_structure.z3_model_status

    if not found:
        # No model - clear progress, print header, then show completion
        progress.display.clear()  # Clear animated line
        self.build_module._capture_and_save_output(example, example_name, theory_name)
        progress.complete_model_search(found=False)
        progress.finish()
        return example

    # Model found - print header FIRST, then progress bar
    progress.display.clear()  # Clear animated line (keep animation thread running briefly)
    progress.active = False   # Stop animation thread
    self.build_module._capture_and_save_output(example, example_name, theory_name)
    print()  # vertical space
    progress.complete_model_search(found=True)  # NOW print permanent progress bar
    print()

    # Continue with iterations...
```

**Note**: May need to adjust `TimeBasedProgress.complete()` to handle the case where animation thread has already stopped.

### Alternative: Use _handle_iteration_mode more directly

Looking at the code more carefully, `_handle_iteration_mode` already calls `_capture_and_save_output`. The restructure could be:

1. Start progress bar (animates during search)
2. Run Z3
3. Stop animation (but don't print final bar yet)
4. Call `_handle_iteration_mode()` which prints header
5. Print the final progress bar

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Animation thread race condition | Medium | Low | Use `active = False` before clearing display |
| Progress bar timing inaccurate | Low | Low | Time is tracked from start, not affected by print order |
| Interactive mode regression | Medium | Medium | Test both batch and interactive modes |
| Multiple iterations affected | Low | Medium | Only model 1 needs restructuring; models 2+ work correctly |

## Test Cases

1. **Single iteration (iterate=1)**: Uses different code path, unaffected
2. **Multiple iterations (iterate=2+)**: Verify header prints before progress bar
3. **No model found**: Verify correct ordering for failure case
4. **Interactive mode**: Verify prompt appears in correct sequence
5. **Save output mode**: Verify file output is correct

## Key Files

| File | Location | Role |
|------|----------|------|
| runner.py | code/src/model_checker/builder/runner.py | `_process_with_iterations` - main fix location |
| animated.py | code/src/model_checker/output/progress/animated.py | `TimeBasedProgress.complete()` - may need adjustment |
| module.py | code/src/model_checker/builder/module.py | `_capture_and_save_output` - header printing |
| structure.py | code/src/model_checker/models/structure.py | `_print_section_header` - header format |

## Summary

The fix requires restructuring `_process_with_iterations` to print the example header BEFORE the progress bar completion. This is achieved by:

1. Stop the animated progress bar without printing its final state
2. Print the header via `_capture_and_save_output()`
3. Then print the progress bar's final state

This keeps the progress bar (user wants it), but fixes the order so it appears after the header.
