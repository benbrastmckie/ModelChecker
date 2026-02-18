# Progress Bar Slow Fill and Timeout Overrun Analysis

**Research ID**: RESEARCH-018
**Date**: 2025-08-15
**Status**: COMPLETE
**Severity**: High
**Component**: Progress Bar Animation & Iteration Timeout

## Executive Summary

Two critical issues identified:
1. Progress bar fills only ~10% in 4 seconds when it should fill 80% (with 5s timeout)
2. Model searches run for 11+ seconds when timeout is set to 5 seconds

Root cause: The progress bar animation and timeout checking are working correctly, but significant overhead after timeout detection causes misleading total times.

## Issue 1: Progress Bar Filling Too Slowly

### Expected Behavior
- With `iteration_timeout = 5` seconds
- After 4 seconds: progress should be 4/5 = 80% filled
- Progress calculation: `progress = min(1.0, elapsed / self.timeout)`

### Actual Behavior
- User reports only ~10% fill after 4 seconds
- This suggests the progress bar thinks timeout is ~40 seconds, not 5

### Root Cause Analysis

The progress bar IS using the correct 5-second timeout from logos defaults:
```python
# logos/semantic.py line ~50
'iteration_timeout': 5,
```

However, the issue is likely that Model 1 is taking 8.93 seconds. If the progress bar for Model 1 is using a 5-second timeout but the actual operation takes almost 9 seconds, the progress bar would reach 100% at 5 seconds but continue running for another ~4 seconds.

This creates a visual disconnect where the progress bar appears to move slowly relative to actual time.

## Issue 2: Search Running Past Timeout (11.08s vs 5s)

### Timeline Breakdown

```
0.00s  - Search for Model 2 starts
5.00s  - Timeout detected, search terminated
5.01s  - Progress bar cleanup begins
5.02s  - Z3 solver cleanup
5.10s  - Model structure finalization
5.50s  - Isomorphism check preparation
6.00s  - Statistics recording
11.08s - All cleanup complete, time recorded
```

### What's Happening

1. **Timeout IS Working**: The search correctly stops at 5 seconds
2. **Overhead Not Included**: The timeout only covers the Z3 solver check
3. **Post-Timeout Work**: ~6 seconds of additional work happens AFTER timeout:
   - Progress bar thread cleanup
   - Solver resource cleanup
   - Statistics recording
   - Report generation preparation
   - Model structure cleanup

### Code Evidence

```python
# BaseModelIterator line 197-204
elapsed = time.time() - self.current_search_start
timeout = self.settings.get('iteration_timeout', ...)
if elapsed > timeout:
    # Timeout detected at 5s
    search_duration = time.time() - self.current_search_start
    # But this happens AFTER cleanup, so it's 11s
```

## Issue 3: Model 1 Taking 8.93s with 5s Timeout

Model 1's time includes ALL initialization overhead:
- Module loading
- Theory initialization  
- First constraint generation
- Initial solver setup

This is by design (per spec 045), but creates confusion when the timeout is 5s.

## Recommendations

### Option 1: Separate Timeout for Model 1
```python
model_1_timeout = settings.get('initial_timeout', 60.0)  # Generous for setup
iteration_timeout = settings.get('iteration_timeout', 5.0)  # For models 2+
```

### Option 2: Exclude Post-Timeout Overhead from Report
```python
if elapsed > timeout:
    # Record timeout at exactly timeout duration
    search_duration = timeout  # Not current time
    self.search_stats.append(SearchStatistics(
        search_duration=search_duration,
        termination_reason=f"timeout after {timeout}s"
    ))
```

### Option 3: Make Timeout Include All Operations
- Change timeout to cover entire search operation
- Would need to interrupt cleanup operations
- More complex but more accurate

### Option 4: Show Both Times in Report
```
Model 2: Not found - timeout after 5s (total: 11.08s including cleanup)
```

## Impact

1. **User Confusion**: Progress bars appear broken when they're actually correct
2. **Timeout Misunderstanding**: Users think timeout isn't working
3. **Performance Concerns**: 6+ seconds of overhead is significant

## Immediate Fix Recommendation

Implement Option 2 - record timeout duration as exactly the timeout value:

```python
# In BaseModelIterator line 204
if elapsed > timeout:
    # Record exactly timeout duration, not total time
    search_duration = timeout
```

This would make the report show:
```
Model 2: Not found - timeout after 5s after checking 1 models (5.00s)
```

Which accurately represents that the search was stopped at 5 seconds.