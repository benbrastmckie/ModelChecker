# Research Report: Fix Flaky Builder Performance Test

**Task**: 68 - Fix flaky `test_multiple_examples_process_efficiently`
**Date**: 2026-03-30
**Session**: sess_1774916194_85648e

## Summary

The `test_multiple_examples_process_efficiently` test in `test_performance.py` uses a per-example threshold of 0.25s (250ms) that is too tight, causing intermittent failures when system timing jitter pushes the average to 0.251s or similar values just over the boundary.

## Current Test Code

The flaky assertion is at line 198:

```python
self.assertLess(avg_time, 0.25,
               f"Average time per example should be <250ms, was {avg_time:.3f}s")
```

The test runs 5 examples (N=2 each), measures total elapsed time, divides by 5 to get per-example average, then asserts `avg_time < 0.25`. A secondary assertion checks `elapsed_time < 2.0` (total).

## Why It Is Flaky

1. **System timing jitter**: `time.time()` measures wall-clock time, which includes OS scheduling delays, GC pauses, and I/O contention. A 1ms variance (0.251s vs 0.249s) is well within normal jitter.
2. **Tight threshold**: 0.25s leaves zero margin. The test intent is "examples process efficiently" -- a 0.3s average still validates that.
3. **CI variability**: CI runners typically have more timing variance than local machines due to shared resources.

## Other Timing Tests in the File

| Test | Threshold | Risk |
|------|-----------|------|
| `test_small_model_generation_completes_quickly` | 0.5s | Low -- generous margin |
| `test_medium_model_generation_completes_within_timeout` | 2.0s | Low |
| `test_large_model_generation_completes_within_timeout` | 5.0s | Low |
| `test_multiple_examples_process_efficiently` (per-example) | **0.25s** | **High -- flaky** |
| `test_multiple_examples_process_efficiently` (total) | 2.0s | Low |
| `test_comparison_mode_performance` | 2.0s | Low |
| `test_module_loading_performance` | 0.1s | Medium |
| `test_serialization_performance` | 0.001s (1ms) | Low -- averaged over 100 runs |
| `test_constraint_generation_scales_linearly` | Relative ratio | Low |

Only the 0.25s per-example threshold is problematic.

## Recommended Fix

Increase the per-example threshold from 0.25s to 0.5s. This matches the `test_small_model_generation_completes_quickly` threshold (which tests the same N=2 complexity for a single example) and provides adequate margin for system variance while still validating that examples process efficiently.

### Specific Change

File: `code/src/model_checker/builder/tests/integration/test_performance.py`, line 198:

```python
# Before:
self.assertLess(avg_time, 0.25,
               f"Average time per example should be <250ms, was {avg_time:.3f}s")

# After:
self.assertLess(avg_time, 0.5,
               f"Average time per example should be <500ms, was {avg_time:.3f}s")
```

Update the error message to match:

```python
f"Average time per example should be <500ms, was {avg_time:.3f}s"
```

### Rationale for 0.5s over 0.3s

- The single-example test (`test_small_model_generation_completes_quickly`) already uses 0.5s for the same N=2 complexity
- Consistency across tests reduces maintenance burden
- 0.3s would still be somewhat tight; 0.5s provides robust margin
- The total-time assertion (2.0s for 5 examples = 0.4s average) already provides a tighter bound

## Effort Estimate

**Trivial** -- single line change plus message update. No functional impact, no new test logic needed.

## File Location

`/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/builder/tests/integration/test_performance.py`
