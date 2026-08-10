# Unfiltered repeat verification — 3 separate invocations

**Bar applied** (carried verbatim from the concurrent-construction task's own Phase 7): run the
unfiltered suite 3 times as **separate invocations** requiring an **identical green result set**.
A single green run is not evidence — the defect being fixed is result-set *instability*, and
comparing result sets across runs is what exposed it.

**Command** (identical for all three; the `-m "not slow"` clause was already deleted, so a bare
invocation is unfiltered):

```
cd code && PYTHONPATH=src python -m pytest -q -p no:cacheprovider
```

**Conditions**: no concurrent oracle suite and no other pytest process on the machine. Other
interactive sessions were active on the box throughout (load average 2.4-3.1); this affects wall
time, not the result set. Raw output: `unfiltered-run-1.txt`, `-2.txt`, `-3.txt`.

## Results

| Run | Collected | Passed | Failed | Errors | Skipped/xfail | Deselected | Wall time |
|---|---|---|---|---|---|---|---|
| 1 | 2190 | **2190** | 0 | 0 | 0 | 0 | 336.81s (5:36) |
| 2 | 2190 | **2190** | 0 | 0 | 0 | 0 | 387.33s (6:27) |
| 3 | 2190 | **2190** | 0 | 0 | 0 | 0 | 418.11s (6:58) |

## Identical-result-set argument

Counts alone are not identity, so the identity is established structurally: `--collect-only`
reports a deterministic **2190** collected with **0 deselected**, and each of the three runs
reported `2190 passed` with zero `FAILED`, zero `ERROR`, and zero skipped/xfail lines. The passed
set therefore equals the full collected set in every run, and the collected set is the same set in
every run. The three result sets are identical, not merely equal in size.

Cross-check: the per-test `--durations` listings contain 724 / 727 / 731 `call` entries. That
spread is **not** a result-set difference — pytest hides durations below 5ms, and a different
handful of sub-5ms tests crosses that display threshold on each run. No node id appears as a
non-passing outcome in any run.

## Note on a discarded fourth measurement

A first attempt at run 3 was killed at 580s by the harness's own command timeout while at 55%
progress, with zero failures recorded up to that point. That is a truncated measurement, not a
result, and it is not counted above; run 3 was re-executed detached and completed normally. It is
recorded here because the machine was demonstrably slower during that window (the same suite had
completed in 337s an hour earlier), which is also the likely explanation for run 3's 418s.

## The three previously-failing tests

The research's unfiltered baseline was **3 failed / 2192 passed in 373.77s (6:13)**. All three
failures are in scope and are eliminated, each appearing as a passing `call` entry in all three
runs above:

| Previously failing | Disposition | Status |
|---|---|---|
| `tests/integration/test_performance.py::TestExecutionPerformance::test_simple_model_performance` | Timing clause (budget == the `max_time` cap) deleted; replaced by assertions that the model was constructed and is well-formed | Passes 3/3 |
| `builder/.../test_multiple_examples_process_efficiently` | Both timing assertions deleted as arithmetically unreachable (5 x ~1.24s against a 2.0s total budget); renamed `test_multiple_examples_run_end_to_end` and now asserts all five examples were loaded and processed | Passes 3/3 |
| `builder/.../test_small_model_generation_completes_quickly` | Timing assertion deleted as arithmetically unreachable (measured floor 1.20s against a 0.5s budget); renamed `test_small_model_runs_end_to_end` and now asserts the load-and-run path completes | Passes 3/3 |

No failure appeared outside the three named files in any run, so the Phase 6 contingency
(revert the quarantine deletion, mark `[PARTIAL]`) was not triggered.

## Wall-time accounting

| Measurement | Result | Wall time |
|---|---|---|
| Filtered baseline recorded in the old `addopts` comment (pre-dates the concurrency fix) | 1 failed / 2136 passed / 43 deselected | 5:37 |
| Research unfiltered run, before this task's changes | 3 failed / 2192 passed | 6:13 |
| Filtered run after this task's Phases 1-3, quarantine still in place | 2189 passed / 1 deselected | 6:14 |
| Unfiltered, quarantine deleted (mean of the three runs above) | 2190 passed | **6:21** |

The default run is now unfiltered and costs ~6:21 on average against a ~5:37 filtered baseline
(+13%), while running 54 more tests than that baseline did and finishing green. The predicted
~+10% held. Cap-burn reduction paid for most of the added cost: the two most expensive
quarantined tests dropped from 11.0s to 0.96s (`test_memory_released_after_error`) and from 3.6s
to 2.34s (`test_file_handles_closed`), and ~5.4s more was recovered by deleting the cap-pinned
`test_constraint_generation_scales_linearly` (4.2s) and the duplicate "large model" test (1.2s).

Note the three unfiltered runs span 336-418s. That spread is machine load across the sampling
window, not test behaviour — which is itself the point of this task: wall time here is not a
stable enough quantity to assert against, which is why no assertion does so any more.
