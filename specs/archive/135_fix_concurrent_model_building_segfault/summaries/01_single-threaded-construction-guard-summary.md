# Implementation Summary: Fix Concurrent Model-Building Segfault

- **Task**: 135 - Fix concurrent model building segfault
- **Plan**: `plans/01_single-threaded-construction-guard.md`
- **Status**: PARTIAL — Phases 1-6 complete; Phase 7 blocked on task 136
- **Session**: sess_1786211832_501137_135
- **Date**: 2026-08-08

## Outcome

An intermittent C-level segfault (5/8 crashes at 3 threads, 6/6 at 5 threads) is now a
deterministic, documented Python exception. Model construction is declared
**single-threaded-only** and that contract is enforced by a process-global, fail-fast,
thread-reentrant guard raising `ConcurrentConstructionError` at the point of misuse.

**60/60 isolated subprocess runs green.** No SIGSEGV, no SIGABRT, no non-zero exits.

## What was built

| Phase | Outcome |
|-------|---------|
| 1 | `models/concurrency.py` — guard + `ConcurrentConstructionError`, 15 unit tests (TDD, RED then GREEN) |
| 2 | Guard wired into `SemanticDefaults`, `ModelDefaults`, `ModelConstraints`, and (by amendment) `Syntax.__init__` |
| 3 | Both concurrency tests rewritten to assert the contract; `slow` marker relocated from module to class/method scope |
| 4 | Repeat-sample validation: 60 isolated subprocess runs, all exit 0 |
| 5 | Contract documented in `ARCHITECTURE.md` + `KNOWN_TEST_FAILURES.md`; `NOTE:` tag on the cvc5 defect |
| 6 | Regression sweep: 2154 passed, 0 failed, 41 deselected — no new failures vs baseline |
| 7 | **NOT STARTED — hard-gated on task 136** |

### Root cause and the second race

The reported root cause was unlocked `z3.*` allocation into the process-global `z3.main_ctx()`
from `theory_lib/bimodal/semantic/core.py`. A **second, independent race** surfaced during
Phase 3's first verification run and is worth carrying forward: `Syntax.__init__` reaches
`syntactic/atoms.py`'s `get_atom_sort()`, an unsynchronized check-then-set module-global cache.
Two threads racing there each create a distinct `AtomSort`, and sentence letters built from the
losing thread's orphaned sort surface as `Z3Exception('Sort mismatch')` — a clean failure, not a
segfault, but still a contract violation. Extending the guard to `Syntax.__init__` fixed it.
This is why the guard covers four constructors, not the three originally planned.

## Verification

- **Phase 4 evidence**: `evidence/repeat-sample-results.md` (+ raw logs `phase4-batch{1,2,3}.txt`).
  Three batches of 20: 3-thread test, 5-thread test, and both in one invocation (the last rules
  out cross-test guard leakage). Harness: `scripts/repeat_sample.sh`.
- **Phase 6 regression**: full documented scope `code/tests/ code/src/model_checker/` gave
  **2154 passed / 0 failed / 41 deselected / exit 0** against a **2137 / 0 / 43** baseline. The
  -2 deselected is exactly the two crash tests now unmarked; the +17 passed is those 2 plus 15
  new guard unit tests. Failure set empty, equal to baseline.
- Theory unit suites: logos 40, exclusion 77, imposition 98 all green; bimodal 258 passed with
  1 pre-existing load-sensitive flake (`BM_CM_4`) that passes in isolation at 21.39s and passed
  in the full-scope run.

All Phase 4 and 6 runs happened with the oracle suite running concurrently (load 1.8-4.6 on 24
cores). For Phase 4 this is a strength, not a caveat: those runs judge exit codes only and
assert no wall-clock, so contention cannot skew them, and contention is a stronger probe for a
scheduling-dependent race than an idle machine.

## Plan Deviations

1. **Guard extended to a fourth constructor (`Syntax.__init__`)** — Phase 2 amendment, not in the
   original file list. Forced by the second race described above. Recorded in the plan.
2. **Phase 3 marker relocation done at method level for `TestResourceLimits`** — a class-level
   mark would have wrongly re-quarantined the contract test, since that class mixes the contract
   test with two expensive non-timing tests. Recorded in the plan.
3. **Phase 4 runs executed with the oracle suite still active**, rather than deferred until it
   cleared as the plan's task notes said. Justified above and in the evidence file; the deferral
   was written against timing-sensitive concerns that do not apply to exit-code-only sampling.
4. **Phase 6 also ran the wider `tests/ + src/model_checker/` scope** beyond the plan's literal
   `code/tests/`. The plan requires comparing against the documented baseline, and that baseline
   was measured at the wider scope — the literal narrower command alone could not support the
   comparison it was asked to support. Both were run and both are recorded.
5. **Phase 7 not executed** — see Blockers.

## Blockers

**Phase 7 (remove the `-m "not slow"` quarantine) is blocked on task 136**
(`ground_wallclock_performance_budgets`), whose status in `specs/state.json` is `not_started`.

The quarantine clause covers two independent defects. This task fixed one (the crashers);
task 136 owns the other (three ungrounded wall-clock budget assertions, one of which —
`test_simple_model_performance`, failing at 1.09s against a 1.0s budget — was observed again in
Phase 6). Removing the clause now would re-break the default run. Per the plan's own gate,
`code/pyproject.toml` was left untouched and Phase 7 remains `[NOT STARTED]`.

This is the planned, correct outcome for this cycle, not a failure.

## Recommended follow-up

`solver/type_guards.py` unconditionally does `import cvc5.pythonic` on every constraint assert
as a debug type-check, loading a native extension for an unused backend. It is provably **not**
the crash mechanism (no captured fault trace has a cvc5 frame), so it was deliberately kept out
of this crash-fix diff. Phase 5 left `NOTE:` tags at both sites for `/fix-it` to pick up. It
warrants its own task.

## Artifacts

- `code/src/model_checker/models/concurrency.py`, `models/tests/unit/test_concurrency.py`
- Modified: `models/semantic.py`, `models/structure.py`, `models/constraints.py`,
  `syntactic/syntax.py`
- Modified: `code/tests/integration/test_performance.py`, `test_timeout_resources.py`
- Modified: `code/docs/core/ARCHITECTURE.md`, `code/docs/core/KNOWN_TEST_FAILURES.md`
- Modified (comment only): `code/src/model_checker/solver/type_guards.py`
- `specs/135_fix_concurrent_model_building_segfault/scripts/repeat_sample.sh`
- `specs/135_fix_concurrent_model_building_segfault/evidence/repeat-sample-results.md`
- Not modified (gated): `code/pyproject.toml`
