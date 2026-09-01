# After-State Wall-Clock Baselines

Recorded after all fixture-swap and marking phases (Phases 2-7) landed, on the same invocations
as `before-wall-clocks.md`.

## Machine state

Load was elevated relative to Phase 1's baseline window (roughly 5.1-10.4 across this
measurement window, vs. 4.2-6.1 for the before-state) — this session shares the host with other
concurrently orchestrated agent work. Every figure below still carries its own before/after
`uptime` reading. One transient flake was observed and re-verified (see note under Measurement 1)
rather than accepted uncritically.

## Measurements

### 1. Full gating parallel pass

Invocation: (identical to Phase 1)

- First attempt: load `5.14 -> 7.53`, result `1 failed, 2223 passed, 1 skipped, 2 warnings in
  89.12s`. The one failure,
  `tests/cli/test_flag_matrix.py::test_output_affecting_boolean_flag_changes_output[print_constraints]`,
  passed cleanly in isolation (`1 passed in 0.98s`) and is a pre-existing CLI-subprocess
  wall-clock assertion untouched by this task, run under `-n 4` contention with load already at
  7.53-8.12 — treated as transient contention flakiness, not a regression, and re-verified below
  rather than silently accepted.
- Retry: load `6.28 -> 8.46` (still elevated, but the retry's own result is unambiguous):
  **2224 passed, 1 skipped, 2 warnings in 76.69s**. Zero failures.
- Collected-count note: 2224 (after) vs. 2153 (before) is not a like-for-like diff — this shared
  repository had other, unrelated tasks landing commits (new tests) in the same window this
  measurement spans. The wall-clock comparison is the figure this task's audit targets; the raw
  count delta is not attributable to this task alone.

### 2. Gating serial pass

- Load: `7.91 -> 8.63`.
- Result: **9 passed, 2688 deselected in 2.33s** (before: 9 passed, 2592 deselected in 2.28s).
  Same shape, same near-zero cost, count delta from concurrent unrelated work as above.

### 3. Integration performance/error-handling/timeout-resources trio

- Load: `8.10 -> 10.42`.
- Result: **58 passed in 29.51s** (before: 58 passed in 32.36s), despite load roughly double the
  before-state's. Same collected count (58) -- this selection had no concurrent-task interference.

### 4. `builder/tests/unit/test_example.py`

- Load: `10.42 -> 10.36`.
- Result: **16 passed, 1 deselected in 10.66s** (before: 17 passed in 36.13s, slowest 31.47s).
  The one deselected item is `test_build_example_bimodal_theory_countermodel`, now
  `development`-marked (Phase 6) -- correctly excluded from this `-m "not development"`
  selection. Slowest remaining: `test_iteration_via_iterate_api` at 10.02s (matches Phase 3's own
  figure; see that phase's note about this sitting near logos's own default `max_time=10`).

### 5. CLI/e2e/packaging plumbing trio

- Load: `10.33 -> 9.07`.
- Result: **48 passed in 21.24s** (before: 48 passed in 21.32s) -- essentially flat, as Phase 4's
  own record predicted: this selection was never dominated by bimodal solve cost in the
  aggregate (`test_theory_library_execution`, the one retained bimodal test, contributes a small
  fraction of the total either way).

### 6. Packaging suite under the NEW selector

Invocation:
```
cd code && PYTHONPATH=src pytest tests/packaging/ -v -m "packaging and not unstable and not development" --durations=20
```

- Load: `9.07 -> 8.80`.
- Result: **121 passed, 4 skipped, 2 deselected in 19.82s** (before, old unfixed selector: 119
  passed, 4 skipped in 105.80s). The 2 deselected are exactly
  `test_generate_then_execute[bimodal]` and `test_generate_then_execute_cp1252[bimodal]`
  (`development`-marked, Phase 6). Slowest remaining: `test_generate_then_execute[logos]` at
  4.83s, `test_generate_then_execute_cp1252[logos]` at 4.78s -- no bimodal parametrize case runs
  at all under the gating selector.

## Summary table

| # | Selection | Before | After | Delta |
|---|---|---|---|---|
| 1 | Full gating parallel pass | 81.84s (load 4.45-6.09) | 76.69s (load 6.28-8.46, retry) | -6.3% despite higher load |
| 2 | Gating serial pass | 2.28s | 2.33s | flat (near-zero either way) |
| 3 | Integration trio | 32.36s (load 5.28-5.35) | 29.51s (load 8.10-10.42) | -8.8% despite ~2x load |
| 4 | `test_example.py` | 36.13s, slowest 31.47s | 10.66s, slowest 10.02s | -70.5% |
| 5 | CLI/e2e/packaging trio | 21.32s | 21.24s | flat (never bimodal-dominated) |
| 6 | Packaging suite (new selector) | 105.80s | 19.82s | **-81.3%** |
