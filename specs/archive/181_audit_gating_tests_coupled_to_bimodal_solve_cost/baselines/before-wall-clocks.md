# Before-State Wall-Clock Baselines

Recorded on current HEAD (pre-implementation), before any code change in this task.

## Machine state

- `nproc`: 24
- Load is **not idle**: another orchestrated task (`bimodal-usage-audit`) is running concurrently
  in the same session, and `uptime`'s 1-minute load average fluctuated roughly 4.2-6.1 across the
  measurement window below. Every figure below carries its own before/after `uptime` reading so a
  reader can judge whether a given number is load-contaminated. No figure here is presented as
  "clean idle machine" — it is a paired, load-labeled reading, and Phase 8's after-figures are
  taken under materially the same load band for a defensible comparison.
- `git status --short code/` is clean for the duration of this phase (no source file modified).

## Measurements

### 1. Full gating parallel pass

Invocation:
```
cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial and not development" -n 4 -q --timeout=300 --timeout-method=thread
```

- Load before: `05:31:53  load average: 4.45, 4.85, 5.16`
- Load after: `05:33:18  load average: 6.09, 5.31, 5.29`
- Result: **2153 passed, 1 skipped, 2 warnings in 81.84s (0:01:21)**

### 2. Gating serial pass

Invocation:
```
cd code && PYTHONPATH=src pytest tests/ src/model_checker -m "xdist_serial and not packaging and not unstable and not development" -q --timeout=300 --timeout-method=thread
```

- Load before: `05:33:56  load average: 5.28, 5.22, 5.26`
- Load after: `05:33:48  load average: 5.62, 5.28, 5.28` (reading taken moments after start; see raw
  log — both readings sit in the same 5.2-5.6 band)
- Result: **9 passed, 2592 deselected in 2.28s**

### 3. Integration performance/error-handling/timeout-resources trio

Invocation:
```
cd code && PYTHONPATH=src pytest tests/integration/test_performance.py tests/integration/test_error_handling.py tests/integration/test_timeout_resources.py -m "not development"
```

- Load before: `05:33:56  load average: 5.28, 5.22, 5.26`
- Load after: `05:34:29  load average: 5.35, 5.24, 5.27`
- Result: **58 passed in 32.36s**
- Report's figure (36.25s, different sandbox run) is in the same neighborhood; this run's own
  32.36s is the number this task's Phase 8 comparison uses.

### 4. `builder/tests/unit/test_example.py`

Invocation:
```
cd code && PYTHONPATH=src pytest src/model_checker/builder/tests/unit/test_example.py -m "not development" --durations=20
```

- Load before: `05:34:32  load average: 5.08, 5.19, 5.25`
- Load after: `05:35:09  load average: 4.74, 5.10, 5.22`
- Result: **17 passed in 36.13s**; slowest duration **31.47s**
  (`TestBuildExampleIntegration::test_iteration_via_iterate_api`, against its own explicit
  `max_time=30` budget — confirms the report's near-miss finding directly), followed by 2.19s
  (`test_build_example_bimodal_theory_countermodel`).

### 5. CLI/e2e/packaging plumbing trio

Invocation:
```
cd code && PYTHONPATH=src pytest tests/cli/test_flag_matrix.py tests/e2e/test_batch_output_real.py src/model_checker/builder/tests/e2e/test_full_pipeline.py -m "not development" --durations=20
```

- Load before: `05:35:12  load average: 4.92, 5.14, 5.23`
- Load after: `05:35:34  load average: 4.76, 5.09, 5.22`
- Result: **48 passed in 21.32s**. Slowest: 3.72s (`test_theory_library_execution`, the one
  deliberately-retained bimodal test), 2.61s (`test_print_impossible_flag_includes_impossible_states`),
  2.36s + 2.36s (the two `test_batch_output_real.py` tests).

### 6. Packaging suite as `packaging.yml` currently selects it

Invocation:
```
cd code && PYTHONPATH=src pytest tests/packaging/ -v -m packaging --durations=20
```

- Load before: `05:35:37  load average: 5.02, 5.14, 5.23`
- Load after: `05:37:23  load average: 5.67, 5.30, 5.27`
- Result: **119 passed, 4 skipped in 105.80s (0:01:45)**
- `test_generate_then_execute[bimodal]` **observed outcome: PASSED in 81.06s** — it did NOT hit
  the 180s subprocess timeout in this run. This diverges materially from the research report's
  hypothesis ("already blows its budget... should now be expected to fail via
  `subprocess.TimeoutExpired`"), which was based on a manual `dev_cli.py` reproduction (bypassing
  the `installed_venv` wrapper) that observed in-progress output past 200s wall clock. The actual
  packaging-suite invocation, through the installed console script inside `installed_venv`, is
  evidently faster than that manual reproduction — recorded here as the observed divergence per
  this phase's Scope Hypothesis obligation, not corrected to match the report. It remains the
  single most expensive bimodal-coupled test in the gating surface (81.06s of the packaging
  suite's 105.80s total, vs. the next-slowest `test_generate_then_execute[logos]` at 4.31s), which
  is itself sufficient justification for Phase 6's `development` marking regardless of whether it
  currently times out.
- Other durations of note: 13.66s `test_cli_console_script.py::test_version_matches_python_dash_m_invocation`
  setup (venv/toolchain provisioning, not bimodal-coupled), 4.31s `test_generate_then_execute[logos]`,
  2.10s `test_build_smoke.py` setup, 1.32s/1.19s the two `test_cli_console_script.py` bimodal-fixture
  tests (`test_real_example_run_through_console_script`, `test_console_script_runs_without_pythonpath`).

## Summary table

| # | Selection | Result | Wall clock |
|---|---|---|---|
| 1 | Full gating parallel pass | 2153 passed, 1 skipped | 81.84s |
| 2 | Gating serial pass | 9 passed, 2592 deselected | 2.28s |
| 3 | Integration trio (`test_performance`/`test_error_handling`/`test_timeout_resources`) | 58 passed | 32.36s |
| 4 | `builder/tests/unit/test_example.py` | 17 passed (slowest 31.47s) | 36.13s |
| 5 | CLI/e2e/packaging plumbing trio | 48 passed | 21.32s |
| 6 | Packaging suite (`-m packaging`, current unfixed selector) | 119 passed, 4 skipped (`test_generate_then_execute[bimodal]` 81.06s, PASSED not timed out) | 105.80s |
