# Model 1 Timeout Handling Fix

**Spec ID**: SPEC-046
**Created**: 2025-08-15
**Status**: DRAFT
**Priority**: P1
**Effort**: 30 minutes
**Risk**: Low
**Depends on**: SPEC-045 (Progress Timing Alignment)

## Executive Summary

Fix the issue where Model 1 takes longer than the iteration_timeout because it includes setup overhead. Model 1 should either use a separate timeout or not be subject to iteration timeout constraints.

## Problem

- Model 1 includes all initialization overhead (by design from SPEC-045)
- With `iteration_timeout = 5s`, Model 1 takes 8.93s
- This creates confusion as the first model "violates" the timeout
- Progress bar shows completion at 5s but operation continues

## Proposed Solution

### Option 1: Separate Timeout for Model 1 (Recommended)

Model 1 uses a different timeout that accounts for initialization:

```python
# In BaseModelIterator or BuildModule
if model_number == 1:
    # Use max_time (solver timeout) for initial model
    timeout = self.settings.get('max_time', 60.0)
else:
    # Use iteration_timeout for subsequent models
    timeout = self.settings.get('iteration_timeout', 5.0)
```

### Option 2: No Timeout for Model 1

Model 1 is exempt from iteration timeout since it's the initial solve:

```python
# In progress bar creation
if model_number == 1:
    # Use a large timeout for progress bar animation
    progress_bar = TimeBasedProgress(
        timeout=float('inf'),  # Or very large number
        ...
    )
```

### Option 3: Document Current Behavior

Keep current behavior but add clear documentation that Model 1 may exceed iteration_timeout.

## Implementation (Option 1)

### 1. Update BuildModule

```python
# builder/module.py line 754
iteration_timeout = example_case[2].get('iteration_timeout', 60.0)
initial_timeout = example_case[2].get('max_time', 60.0)  # Use solver timeout

progress = UnifiedProgress(
    total_models=iterate_count,
    iteration_timeout=iteration_timeout,
    initial_timeout=initial_timeout  # NEW
)
```

### 2. Update UnifiedProgress

```python
# output/progress/core.py
def __init__(self, 
             total_models: int = 1,
             iteration_timeout: Optional[float] = None,
             initial_timeout: Optional[float] = None,  # NEW
             display: Optional['ProgressDisplay'] = None):
    # ...
    self.initial_timeout = initial_timeout or iteration_timeout or 60.0
    
def start_model_search(self, model_number: int, start_time: Optional[float] = None) -> None:
    # ...
    # Use appropriate timeout
    timeout = self.initial_timeout if model_number == 1 else self.iteration_timeout
    
    progress_bar = TimeBasedProgress(
        timeout=timeout,  # Use model-specific timeout
        # ...
    )
```

## Testing

1. Verify Model 1 uses max_time for timeout
2. Verify Models 2+ use iteration_timeout
3. Progress bars fill at appropriate rates
4. No timeout warnings for Model 1 within max_time

## Success Criteria

- Model 1 can take up to max_time without timeout warnings
- Progress bar for Model 1 fills over max_time duration
- Models 2+ still respect iteration_timeout
- Clear visual distinction between initial and iteration timeouts

## References

- [Progress Timing Research](../research/018_progress_bar_slow_fill_analysis.md)
- [Progress Timing Alignment](045_progress_timing_alignment.md)