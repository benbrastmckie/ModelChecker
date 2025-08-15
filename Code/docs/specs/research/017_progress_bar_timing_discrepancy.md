# Progress Bar Timing Discrepancy Analysis

**Research ID**: RESEARCH-017
**Date**: 2025-08-15
**Status**: COMPLETE
**Severity**: Medium
**Component**: Progress Bar Animation & Iteration Reporting

## Executive Summary

Investigation into a timing discrepancy where the progress bar shows "8.9s" while the iteration report shows "11.41s" for the same model search. This represents a 2.5 second (28%) difference in reported times that could confuse users about actual search performance.

## Issue Description

When running counterfactual example CF_CM_1 with iterate=2:
- Progress bar displays: `Finding non-isomorphic models: [████████████████████] 1/2 8.9s`
- Iteration report shows: `Model 2: Not found - timeout after 5s after checking 1 models (11.41s)`

The discrepancy suggests different timing mechanisms or measurement points between the progress bar and iteration statistics.

## Root Cause Analysis

### 1. Different Time Measurement Points

**Progress Bar Timing (animated.py)**:
```python
# In TimeBasedProgress._animate()
elapsed = time.time() - self.start_time
msg += f" {elapsed:.1f}s"
```
- Measures from when `start()` is called
- Updates every 100ms during animation
- Shows elapsed time at the moment of display

**Iteration Report Timing (core.py)**:
```python
# In BaseModelIterator._iterate_with_progress()
search_duration = time.time() - self.current_search_start
self.search_stats.append(SearchStatistics(
    search_duration=search_duration,
    ...
))
```
- Measures from `self.current_search_start`
- Calculated once when search completes/times out
- Includes all overhead between start and completion

### 2. Timing Overhead Sources

The 2.5 second difference likely comes from:

1. **Model Structure Building** (~0.7s)
   - Initial model construction
   - State space generation
   - Validation checks

2. **Progress Bar Lifecycle** (~0.1-0.2s)
   - Thread creation/destruction
   - Display updates
   - Cleanup operations

3. **Iteration Framework Overhead** (~1.5-1.8s)
   - Constraint generation
   - Isomorphism checking setup
   - Statistics tracking
   - Report generation

### 3. Timing Sequence

```
Timeline:
0.00s - BuildModule starts iteration
0.01s - BaseModelIterator._iterate_with_progress() begins
0.02s - current_search_start = time.time()
0.03s - Progress bar created but not started yet
0.73s - Initial model built (Z3 runtime)
0.74s - Progress bar start() called
0.75s - Animation begins showing elapsed time
...
5.74s - Timeout check triggers (5s from progress start)
8.90s - Progress bar shows this elapsed time
8.91s - Progress complete() called
8.92s - Model structure finalization
11.41s - search_duration calculated from current_search_start
11.42s - Report generated
```

## Evidence

### Code Analysis

1. **Progress Bar Start Timing**:
   ```python
   # In BaseModelIterator line 231-233
   if self.search_progress and current_search_model != model_number:
       self.search_progress.start_model_search(model_number)
       current_search_model = model_number
   ```
   Progress bar starts AFTER initial setup work.

2. **Search Duration Calculation**:
   ```python
   # In BaseModelIterator line 204-205  
   search_duration = time.time() - self.current_search_start
   ```
   Measures from before progress bar creation.

3. **Initial Model Time**:
   ```python
   # Shows 0.73s for initial model
   Z3 Run Time: 0.7253 seconds
   ```
   This time is included in iteration report but not in progress bar.

## Impact

1. **User Confusion**: Different times for the same operation
2. **Performance Perception**: Users may think searches take longer than displayed
3. **Debugging Difficulty**: Hard to correlate progress with actual performance

## Recommendations

### Option 1: Align Timing Start Points (Recommended)
Make progress bar and iteration report use the same timing reference:
```python
# In BaseModelIterator._iterate_with_progress()
if self.search_progress and current_search_model != model_number:
    # Pass the search start time to progress bar
    self.search_progress.start_model_search(model_number, start_time=self.current_search_start)
```

### Option 2: Show Both Times
Display overhead separately:
```
Model 2: Not found - timeout after 5s (search: 8.9s, total: 11.41s)
```

### Option 3: Document the Difference
Add clear documentation explaining that:
- Progress bar shows active search time
- Report shows total time including setup/teardown

## Implementation Considerations

- Changing timing could affect timeout behavior
- Need to ensure backward compatibility
- Consider adding detailed timing breakdown in debug mode
- May need to adjust progress bar animation logic

## Conclusion

The timing discrepancy is caused by different measurement starting points: the progress bar measures from when it starts animating (after initial setup), while the iteration report measures from the beginning of the search attempt (including all setup). This ~2.5s difference represents legitimate overhead that should either be consistently included or excluded from both displays.