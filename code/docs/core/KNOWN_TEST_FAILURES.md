# Known Test Failures

Status of the `model_checker` test suite, derived from measured full-suite runs rather than
from accumulated per-file observations.

**Bottom line**: the default test run is green. Every failure previously carried as a "known
failure" has either been fixed or been traced to one of two tracked defects, both of which are
temporarily quarantined behind `-m "not slow"` and both of which are expected to be fixed and
un-quarantined.

## Current State

```bash
PYTHONPATH=src pytest tests/ src/model_checker/
```

| Metric | Value |
|--------|-------|
| Passed | 2137 |
| Failed | **0** |
| Deselected (quarantined) | 43 |
| Wall clock | 6:10 |
| Exit code | 0 |

A green default run is a recent state, not a long-standing one. See "How the previous baseline
was wrong" below before treating any older failure count as authoritative.

## The Quarantine

`code/pyproject.toml` sets `addopts = "... -m \"not slow\""`. This is a **temporary
crash-containment measure, not a policy**. Run the quarantined set with:

```bash
PYTHONPATH=src pytest tests/ src/model_checker/ -m slow
```

The counts below (43 quarantined, 38/3/2 split) describe the measured baseline referenced in
"Current State" above, captured before the concurrent-model segfault fix. That fix removed the
`slow` marker from the two crashing tests entirely (they now assert the guard contract instead
of crashing — see "The 2 crashing tests" below), so the quarantined set has since shrunk from
43 to 41 (38 pass + 3 fail); a fresh full-suite measurement to confirm this, and to fold in any
wall-clock-budget changes, is pending re-verification of this baseline.

At the time of the "Current State" measurement, 43 tests were quarantined. Of those, **38
passed, 3 failed, and 2 could not be run at all**:

| Category | Count | Tracked as |
|----------|-------|------------|
| Pass — quarantined only because the marker is applied at module scope | 38 | see "Over-hiding" |
| Fail — wall-clock assertions with ungrounded budgets | 3 | task: ground wall-clock budgets |
| Crash — abort the interpreter, so they cannot be measured | 2 | **fixed** — see "The 2 crashing tests" below |

Measuring the quarantined set requires deselecting the two crashers first; otherwise the run
aborts partway through and reports nothing.

### The 3 failing tests

All three are wall-clock assertions, not correctness failures:

| Test | Asserts | Measures |
|------|---------|----------|
| `builder/tests/integration/test_performance.py::TestBuilderPerformance::test_small_model_generation_completes_quickly` | < 500 ms | ~1.09 s |
| `builder/tests/integration/test_performance.py::TestBuilderPerformance::test_multiple_examples_process_efficiently` | < 500 ms | ~1.09 s |
| `tests/integration/test_performance.py::TestExecutionPerformance::test_simple_model_performance` | wall clock | load-dependent |

The first two are roughly 2.2x over budget even at low load, which suggests the budgets were
never grounded in measurement rather than that the tests are merely flaky.

A fourth, `tests/integration/test_performance.py::TestExecutionPerformance::test_scaling_with_n[2-1.0]`,
is genuinely intermittent: it failed in one full sweep and passed in the next at the same commit
on the same machine.

### The 2 crashing tests (fixed)

| Test | Threads |
|------|---------|
| `tests/integration/test_performance.py::TestConcurrentPerformance::test_sequential_vs_concurrent` | 3 |
| `tests/integration/test_timeout_resources.py::TestResourceLimits::test_concurrent_model_building` | 5 |

**Status: fixed.** Both used to build models concurrently from `threading.Thread` targets and
abort the interpreter — observed as both SIGSEGV (exit 139) and SIGABRT (exit 134) across runs,
with the faulting extension reported as `cvc5.cvc5_python_base` (a red herring — see
`ARCHITECTURE.md`'s Concurrency Model section and `models/concurrency.py` for why it was loaded
at all). The stack showed two threads simultaneously inside
`theory_lib/bimodal/semantic/core.py:580 build_frame_constraints`, reached from `__init__`, so
the race was in semantics *construction*, not in solving.

Reproduction was intermittent — 1 of 3 identical isolated invocations, and up to 100% at 5
threads in repeat sampling. **A single green run does not validate a fix here**: validation
requires repeated isolated-subprocess runs (a segfault kills the interpreter, so in-process
repetition proves nothing), not a single pytest invocation.

Model construction is now declared single-threaded-only and enforced with a process-global,
thread-reentrant, fail-fast guard (`model_checker.models.concurrency`): a second thread
contending for the guard raises `ConcurrentConstructionError` immediately instead of racing on
the shared Z3 context. Both tests were rewritten to assert exactly that contract — every
thread's outcome must be success or `ConcurrentConstructionError`, never a crash or any other
exception — and neither is marked `slow` any longer, so both run in the default suite. See
"Removing the Quarantine" below for the status of the other tracked defect blocking full
quarantine removal.

### Over-hiding

The `slow` marker is currently applied as a module-level `pytestmark` across three whole files,
so it quarantines 43 tests when only 5 justify it. **38 quarantined tests pass**, and the entire
runnable quarantined set completes in 73 seconds.

Tests hidden for no reason include `test_file_handles_closed`, `test_keyboard_interrupt_cleanup`,
and `test_memory_released_after_error` — none of which assert on wall-clock time or use threads.

The fix is per-test markers on the 5 actual problems instead of module-level ones. This is
tracked with the wall-clock budget work.

One test is legitimately marked and should stay marked:
`models/tests/unit/test_semantic.py::TestSemanticDefaultsNBounds::test_max_n_itself_is_constructible`
really does allocate the 2^MAX_N state space (~3.5 GB, ~11 s). It exists to keep `MAX_N` honest.

## Removing the Quarantine

Delete the `-m "not slow"` clause from `addopts` outright — do not relax it — once both tracked
defects are fixed. Then confirm an unfiltered run is green across **repeat** samples, since the
crash was intermittent.

**Status**: the concurrent-model segfault defect is fixed (see "The 2 crashing tests" above) —
that half of the gate is satisfied. The wall-clock budget defect (the 3 failing tests plus the
over-hiding cleanup) is tracked separately and, as of this writing, not yet done. The quarantine
clause stays in place until both halves are complete; removing it with only one fixed would
re-break the default run for the still-ungrounded wall-clock budgets.

## How the previous baseline was wrong

Earlier triage recorded **27 failures against 2148 passing**. That figure does not survive a
full run and should not be used.

It could not have come from a completed sweep, because no sweep could complete. Two defects
prevented it:

1. `tests/integration/test_error_handling.py::test_memory_limit_handling` passed `N: 64`,
   commented "Maximum allowed". `SemanticDefaults` materialized `all_states` eagerly as 2^N
   `BitVecVal`s with no upper bound, so this allocated until the machine died — measured at
   24 GB RSS in ~60 s on a 30 GB host, still climbing when killed. Because the allocation
   happens inside a Z3 C call, `pytest-timeout`'s thread method reported the timeout but could
   not interrupt it.
2. The two concurrency tests above aborted the interpreter.

The 27 figure was therefore assembled from per-file runs, which mask both. Per-file runs also
mask order-dependent failures, which is how a test that inverts its outcome based on prior
imports was carried as a stable "known failure".

### What actually changed

Four defects were fixed to reach a green default run. None were fixed by filtering:

| Defect | Resolution |
|--------|-----------|
| `N` unbounded — 2^N allocation until OOM | `MAX_N` + `_validate_N`, raising `SemanticError` before allocating |
| `test_semantics_invalid_settings` expected `(ValueError, TypeError)` | Passed only by accident: unvalidated `N=-1` reached `range(1 << -1)`, and Python raised `ValueError` for the negative shift. Now asserts `SemanticError`. |
| `test_find_next_model_basic` called `BuildExample.find_next_model()` | No such method, and per `iterate/__init__.py` there should not be — next-model search belongs to the iterate package. Rewritten against `iterate_example`, renamed `test_iteration_via_iterate_api`. |
| Same test's `model_found` assertion was order-dependent | Example inherited bimodal's 1 s default `max_time` against a slower real solve, so under load the timeout surfaced as `model_found=False`. Given an explicit budget. |

The order-dependent one is worth understanding, because it is the failure mode most likely to
recur. The same test at the same commit failed **two different ways** in consecutive sweeps —
`AssertionError` on `model_found` in one, `AttributeError` on `find_next_model` in the other.
The solve succeeded in one run and not the other. A budget tight enough to straddle real solve
time turns a correctness assertion into a coin flip.

This is the same defect, in the same file, that was previously fixed for the sibling `SIMPLE`
example while leaving `SAT` inheriting the default.

## Conventions

- **Solve budgets**: set `max_time` explicitly and generously in tests. The default is 1 s and
  real solves exceed it. See `TESTING_GUIDE.md` section 8.6 on Z3 solve-time variance.
- **A timeout is reported as a wrong answer, not an error.** A blown budget surfaces as "no
  countermodel found" rather than as a failure, so a tight budget silently inverts verdicts
  instead of failing loudly. Rule out a budget before concluding semantics are wrong.
- **Do not mark a test `slow` to make a failure go away.** The marker means "quarantined pending
  a fix", and everything under it is expected to rejoin the default run.
