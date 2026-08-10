# Phase 6 Handoff — Regression sweep

- **Task**: 135
- **Phase**: 6 (Regression sweep) — COMPLETED
- **Session**: sess_1786211832_501137_135
- **Date**: 2026-08-08

## Environment

The oracle suite (`oracle/run-oracle-suite.sh`, PID 405013) was running concurrently for every
run in this phase. Load average 1.84-2.49 (1-min) on 24 cores. No `oracle/` test was run here —
the sibling task owns that surface this cycle.

## Results

Verification only; no source files modified.

### Theory unit suites (separate targeted invocations)

| Theory | Result | Time |
|--------|--------|------|
| logos | 40 passed | 0.45s |
| exclusion | 77 passed | 0.75s |
| imposition | 98 passed | 10.95s |
| bimodal | 258 passed, 1 failed | 58.01s |

The bimodal failure is `test_example_cases[BM_CM_4-example_case9]` — the pre-existing
load-sensitive flake already documented in Phase 2. It **passed in isolation at 21.39s** against
its `max_time=30` budget, and **passed** in the full-scope sweep below. Not a regression.

### Default filter (`-m "not slow"`)

- Plan's literal scope, `code/tests/`: **257 passed, 0 failed, 30 deselected** (9.15s).
- Documented-baseline scope, `code/tests/ code/src/model_checker/`: **2154 passed, 0 failed,
  41 deselected, exit 0** (5:14).

| Metric | Baseline | This run | Delta |
|--------|----------|----------|-------|
| Passed | 2137 | 2154 | +17 |
| Failed | 0 | 0 | 0 |
| Deselected | 43 | 41 | -2 |

Both deltas fully accounted for: -2 deselected = the two crash tests now unmarked (confirms the
43 -> 41 claim Phase 5 wrote into `KNOWN_TEST_FAILURES.md`); +17 passed = those 2 plus the 15
new guard unit tests in `models/tests/unit/test_concurrency.py` (verified by `--collect-only`).
Failure set is empty — equal to baseline. **No new failures.**

### Still-quarantined timing tests (`-m slow`, two files)

**1 failed, 29 passed, 2 deselected** (42.08s). The failure is
`TestExecutionPerformance::test_simple_model_performance` on `assert elapsed < 1.0` at **1.09s**
— matching the "~1.09 s" figure already in `KNOWN_TEST_FAILURES.md`. One of the three documented
ungrounded wall-clock budgets owned by task 136; out of scope here per this plan's Non-Goals.
The 2 deselected are the rewritten contract tests — re-confirms the Phase 3 marker relocation.

## Phase 7 gate — NOT passed

`jq '.active_projects[] | select(.project_number==136) | .status' specs/state.json` returns
`not_started`. Per the plan's own gate, `code/pyproject.toml` was **not touched** (confirmed
clean in `git status`); the `-m "not slow"` clause remains at line 104. Phase 7 stays
`[NOT STARTED]`.

## Next

Nothing further in this task until task 136 (`ground_wallclock_performance_budgets`) reaches
`completed`. At that point Phase 7 removes the quarantine clause and runs 3 unfiltered repeat
sweeps.
