# Implementation Plan: Fix Concurrent Model-Building Segfault

- **Task**: 135 - Fix concurrent model building segfault
- **Status**: [PARTIAL]
- **Effort**: 8.5 hours
- **Dependencies**: Phase 7 only — gated on Task 136 (`ground_wallclock_performance_budgets`) reaching `completed`. Phases 1-6 have no external dependencies.
- **Research Inputs**: `specs/135_fix_concurrent_model_building_segfault/reports/01_concurrent-segfault.md`
- **Artifacts**: plans/01_single-threaded-construction-guard.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Model construction builds Z3 AST nodes against the single process-global `z3.main_ctx()` with
no locking anywhere in the call path; two threads doing this simultaneously corrupt Z3's
context-internal hash-consing/refcount tables and abort the interpreter. This plan declares
model construction **single-threaded-only** and enforces that contract with a process-global,
fail-fast, thread-reentrant guard that raises a clear `ConcurrentConstructionError` on
contention instead of segfaulting, documents the contract where users will find it, rewrites
the two offending tests to assert the contract, and validates the fix with repeat-sample
isolated-subprocess runs (a single green run is not evidence at the measured 62.5%/100% crash
rates). Done when both tests pass 20/20 isolated runs, the contract is documented, and — gated
on Task 136 — the `-m "not slow"` quarantine clause is removed with an unfiltered run verified
green and repeatable.

### Research Integration

Findings taken as settled from `reports/01_concurrent-segfault.md` (each independently
verified; do not re-derive):

- **Root cause**: bare `z3.*` calls in `theory_lib/bimodal/semantic/core.py` (`define_sorts`,
  `define_primitives`, `build_frame_constraints`) allocate into `z3.main_ctx()` unlocked. Zero
  `ctx=` usages in that file.
- **Reproduction**: 5/8 crashes at 3 threads, 6/6 at 5 threads. Crash site migrates across Z3
  C API entry points (`Z3_get_sort_kind`, `Z3_mk_gt`, `Z3_mk_func_decl`, `AstRef.__del__`) —
  the signature of shared-structure memory corruption, not one bad line.
- **Validated fix surface**: one `threading.Lock()` around construction gave 8/8 clean runs at
  5 threads vs 0/6 unguarded.
- **Not the cause**: `cvc5.cvc5_python_base` in fault dumps comes from
  `solver/type_guards.py:96,150` unconditionally doing `import cvc5.pythonic` on every
  constraint assert as a debug type-check. Real defect, wrong task — see Non-Goals.
- **Rejected**: full thread-safety (per-thread `z3.Context()` threaded through every theory's
  Z3 call site, thread-local backend caches, redesigned `isolated_z3_context()`). No
  production path builds models concurrently — `builder/runner.py:727-746` is a sequential
  `for` loop, and the only multi-thread construction call sites in the repository are the two
  tests under investigation.

### Verified during planning (not in the research report)

Two facts change the guard's placement and are load-bearing for Phase 2:

1. **`BimodalSemantics.__init__` does its Z3 work AFTER `super().__init__()` returns.**
   `theory_lib/bimodal/semantic/core.py:67-89` calls `super().__init__(settings)` first, then
   `define_sorts()` / `define_primitives()` / `build_frame_constraints()`. A guard scoped to
   the body of `SemanticDefaults.__init__` (`models/semantic.py:81-105`) would therefore be
   **released before the crashing code runs** and would not prevent the segfault. The guard
   must span the *outermost* `__init__` of the concrete semantics class.
2. **Z3 AST construction continues after semantics construction finishes.**
   `ModelConstraints.__init__` (`models/constraints.py:44-94`) builds `model_constraints`,
   `premise_constraints`, and `conclusion_constraints` — all Z3 AST work — and
   `ModelDefaults.__init__` (`models/structure.py:50-`) solves. Guarding only semantics
   construction leaves a window where thread A is in `ModelConstraints` while thread B is in
   semantics `__init__`, both mutating the same context. All three constructors must share one
   guard.

Also confirmed: `_reset_global_state()` has exactly one call site (`models/semantic.py:83`),
inside `SemanticDefaults.__init__`, so it is automatically inside the guarded window and its
theory overrides (only `theory_lib/bimodal/semantic/core.py:91`, which calls `gc.collect()` —
an independent race trigger per report Section 3.1) need no changes.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in the delegation context; no roadmap consulted.

## Goals & Non-Goals

**Goals**:
- Convert the intermittent C-level segfault into a deterministic, documented Python exception
  (`ConcurrentConstructionError`) raised at the point of misuse.
- Cover the full model-construction window (semantics + constraints + solve), not just
  `SemanticDefaults.__init__`.
- Preserve existing sequential behavior exactly — including same-thread nesting (model
  iteration builds fresh `ModelConstraints`/`ModelDefaults` while an outer structure is alive).
- Rewrite both concurrency tests to assert the contract, not skip it and not leave it behind a
  `slow` marker.
- Prove the fix with repeat-sample isolated-subprocess runs and record the evidence.
- Remove the `-m "not slow"` quarantine — but only when Task 136 is also done.

**Non-Goals**:
- Full thread-safety via per-thread `z3.Context()` (rejected in report Section 5).
- Making `isolated_z3_context()` concurrency-aware.
- Making `solver/registry.py`, `solver/backend.py`, `z3_shim.py` module caches thread-local.
  CPython's import lock already prevents corruption there (report Section 3.4), and they are
  covered incidentally once the guard serializes construction.
- **Fixing the unconditional `import cvc5.pythonic` in `solver/type_guards.py`.** Explicit
  scope decision: **out of scope for this task, belongs in its own task.** It is a real defect
  (loads a native extension for an unused backend on every constraint assert) but it is
  provably not the crash mechanism — no captured fault trace has a cvc5 frame. Folding it in
  would silently expand this task and mix an unrelated performance/hygiene change into a
  crash-fix diff. Phase 5 records it as a durable `NOTE:` tag at the defect site (picked up by
  `/fix-it`) and names it in the summary as a recommended follow-up task; it does not change
  `type_guards.py` behavior.
- Re-tuning any wall-clock budget assertion. Those belong to Task 136.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Guard placed too narrowly (only `SemanticDefaults.__init__`), leaving the actual crash window unguarded | H | H if not designed for | Phase 2 wraps the outermost concrete `__init__` via `__init_subclass__`, plus `ModelConstraints` and `ModelDefaults`; Phase 4's repeat-sample runs are the falsification test |
| Non-reentrant lock breaks legitimate same-thread nesting (iteration, a theory constructing a sub-model) | H | M | Guard is thread-owner + depth counted: same thread re-enters freely, a *different* thread raises. Phase 1 unit-tests reentrancy explicitly; Phase 6 runs the iterate suites |
| Guard leaks (stays held) when a constructor raises | H | M | `try/finally` release; Phase 1 unit-tests "raise inside guarded call leaves guard free" |
| A single green run is mistaken for proof | H | M | Phase 4 mandates 20 isolated subprocess runs per test with recorded exit codes; a single in-process pytest run is explicitly not accepted as evidence |
| Concurrent oracle suite in this repo skews timings / contends for CPU | M | H (known active) | No phase asserts wall-clock. Phases 1-6 use targeted node-id runs, never a full-suite sweep. Phase 7's unfiltered run records observed load conditions alongside the result |
| Phase 3 edits the same two test files Task 136 owns | M | M | Keep the edit mechanical and minimal: rewrite only the two named tests and relocate the module-level `slow` marker to per-class marks. Record the touched files in the handoff so Task 136 can rebase |
| Removing `-m "not slow"` while Task 136 is unfinished re-breaks the default run | H | M | Phase 7 is hard-gated: it reads Task 136's status from `specs/state.json` first and marks itself `[BLOCKED]` if not `completed` |
| Rewritten tests are flaky in the other direction (thread scheduling lets all threads run sequentially, so no contention is observed) | M | H | Contract assertion is written to accept both outcomes — success or `ConcurrentConstructionError` — and to reject only crashes/other exceptions. See Phase 3 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 5 | 2 |
| 4 | 4 | 3 |
| 5 | 6 | 3, 5 |
| 6 | 7 | 4, 6 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Concurrency guard primitive (TDD) [COMPLETED]

**Goal**: A standalone, unit-tested, fail-fast reentrant construction guard with no
dependencies on the model classes.

**Tasks**:
- [x] Write `code/src/model_checker/models/tests/unit/test_concurrency.py` FIRST (RED), covering:
  - Sequential repeated acquire/release succeeds any number of times.
  - Same-thread nested acquire (depth 2, 3) succeeds; guard only frees at depth 0.
  - A second thread attempting acquire while held raises `ConcurrentConstructionError`.
  - An exception raised inside the guarded region still releases the guard (guard is free
    afterwards, and a later acquire from any thread succeeds).
  - The error message names the contract and tells the caller what to do instead
    (build sequentially, or one model per process).
  - `ConcurrentConstructionError` is a subclass of `RuntimeError`.
- [x] Create `code/src/model_checker/models/concurrency.py` (GREEN) with:
  - `class ConcurrentConstructionError(RuntimeError)` with a docstring stating the
    single-threaded-only contract and why it exists (unsynchronized `z3.main_ctx()` mutation).
  - A module-level guard object holding `_owner: Optional[int]` (thread ident) and
    `_depth: int`, protected by a plain `threading.Lock` used only for the short
    check-and-set — never held across the guarded work.
  - `acquire()`: free -> take ownership, depth 1; owned by current thread -> depth += 1;
    owned by another thread -> raise `ConcurrentConstructionError`.
  - `release()`: depth -= 1; at 0, clear owner.
  - `single_threaded_construction()` context manager wrapping acquire/release in `try/finally`.
  - `guard_construction(func)` decorator (used by Phase 2) built on the context manager,
    `functools.wraps`-preserving.
- [x] Confirm RED-then-GREEN was actually observed (tests failed before the module existed).

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/models/concurrency.py` — new module (guard + error type)
- `code/src/model_checker/models/tests/unit/test_concurrency.py` — new unit tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/models/tests/unit/test_concurrency.py -v` — all pass.
- No import of `z3`, `model_checker.models.semantic`, or `structure` in `concurrency.py`
  (keeps it dependency-free and importable from anywhere).

---

### Phase 2: Wire the guard into the construction path [COMPLETED]

**Goal**: Every model-construction entry point is inside the guard, including the subclass
`__init__` bodies where the crash actually occurs.

**Tasks**:
- [x] In `models/semantic.py`: add `__init_subclass__` to `SemanticDefaults` that wraps
  `cls.__init__` with `guard_construction` when the subclass defines its own `__init__` in
  `cls.__dict__`; also wrap `SemanticDefaults.__init__` itself. Double-wrapping through the
  `super()` chain is harmless because the guard is thread-reentrant — state this in a comment
  at the wrap site so a future reader does not "optimize" it away.
- [x] In `models/structure.py`: apply the same `__init_subclass__` treatment to `ModelDefaults`
  (covers `solve()` / `_setup_solver` / `assert_tracked` reached from `__init__`).
- [x] In `models/constraints.py`: decorate `ModelConstraints.__init__` directly (no subclasses
  in the tree today; if `__init_subclass__` is cheaper to keep uniform, that is acceptable).
- [x] Add a class-level docstring paragraph to `SemanticDefaults` and `ModelDefaults` stating
  the single-threaded-only contract and pointing at `models/concurrency.py`. (Fuller
  user-facing docs land in Phase 5.)
- [x] Verify no production path constructs models off the main thread: re-run the report's
  grep for `threading.Thread` / `ThreadPoolExecutor` under `code/src/model_checker`, and
  confirm the only hits are in `output/progress/` (terminal spinner, does not construct).
  Record the grep output in the phase notes. Confirmed: only `output/progress/spinner.py:61`
  and `output/progress/animated.py:158`, both outside the guarded construction path.
- [x] Sanity-check same-thread nesting: run the iterate suites, which build fresh
  `ModelConstraints`/`ModelDefaults` while an outer structure is alive. Deferred while the
  oracle job was running (see git history for the interim `models/tests/unit/` sanity check);
  run once `pgrep -af "run-oracle"` cleared: `PYTHONPATH=code/src pytest
  code/src/model_checker/iterate/tests/ -q` -> **220 passed in 1.34s**. Same-thread nesting is
  unaffected by the guard.

**AMENDMENT (discovered during Phase 3 single-run verification, folded back into Phase 2)**:
the first single-run execution of the rewritten `test_sequential_vs_concurrent` (see Phase 3)
failed with `Z3Exception('Sort mismatch')` — an *unexpected* exception category the test
explicitly does not accept (only `ok` / `ConcurrentConstructionError` are contractual). Root
cause: `tests/utils/helpers.py::create_test_model()` calls `Syntax(premises, conclusions,
operators)` **before** the guarded `semantics_class(full_settings)` call. `Syntax.__init__`
builds sentence-letter atoms via `syntactic/atoms.py`'s `AtomVal()` -> `get_atom_sort()`, which
is an *unsynchronized check-then-set module-global cache* (`_atom_sort`) — a second, independent
race entirely outside the three constructors this phase originally wrapped. Two threads racing
through `get_atom_sort()` can each create a distinct `AtomSort` Z3 sort object; sentence letters
built from the "losing" thread's orphaned sort are not sort-compatible with later expressions
built against the "winning" one, surfacing as a clean (non-crashing) `Z3Exception`, not a
segfault — but still a violation of the single-threaded-only contract and still not something
either rewritten test is allowed to observe. Fix: wrap `Syntax.__init__`
(`code/src/model_checker/syntactic/syntax.py`) in the same `guard_construction` decorator,
consistent with production's sequential `Syntax(...)` -> `semantics_class(...)` call order in
`builder/example.py:173` and `builder/runner.py:79,198` (confirmed via grep — Syntax is always
constructed immediately before semantics, sequentially, in every production call site).
Re-verified: 3 consecutive single runs of `test_sequential_vs_concurrent` all passed (previously
1/1 failed with the Sort mismatch before this fix), plus one run of
`test_concurrent_model_building`, plus the full `syntactic/tests/` suite (71 passed, 0.53s) and
`models/tests/unit/` suite (still green). This is exactly the kind of gap the plan's own risk
table anticipated ("Guard placed too narrowly... Phase 4's repeat-sample runs are the
falsification test") — it surfaced even earlier, on the very first single-run execution, which
is a stronger signal, not a weaker one.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/models/semantic.py` — `__init_subclass__` wrap + contract docstring
- `code/src/model_checker/models/structure.py` — `__init_subclass__` wrap + contract docstring
- `code/src/model_checker/models/constraints.py` — wrap `__init__`
- `code/src/model_checker/syntactic/syntax.py` — wrap `Syntax.__init__` (added by the amendment
  above; not in the original plan's file list)

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/models/tests/ -v` — green (73 passed).
- `PYTHONPATH=code/src pytest code/src/model_checker/iterate/tests/ -v` — green (220 passed,
  proves same-thread nesting is not broken).
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/ -v` — 258
  passed, 1 failed (`test_example_cases[BM_CM_4-example_case9]`), reproduced identically across
  two consecutive full-suite runs but **passes in isolation in 17.67s**. This is a pre-existing,
  documented, load-sensitive flake, not a regression from this phase: `BM_CM_4`'s `max_time=30`
  was explicitly widened by a prior task after its own investigation found solve time varies
  ~15-24s depending on load (see the settings comment in
  `theory_lib/bimodal/examples.py:379-391`), and this class of failure — a tight-relative-to
  -load solve budget flipping outcome under full-suite CPU contention — is exactly what
  `KNOWN_TEST_FAILURES.md`'s "Conventions" section already documents as a known pattern in this
  codebase, unrelated to construction concurrency (the guard adds a cheap lock
  acquire/release around constructor entry, not solve-time overhead, and cannot plausibly turn a
  17.67s solve into a 30s+ one). Not treated as a regression; not fixed by this task per its
  Non-Goals (wall-clock budget tuning belongs to Task 136).
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/unit/ -v` — green
  (40 passed). No sequential regression in the theories that construct most heavily.
- `PYTHONPATH=code/src pytest code/src/model_checker/syntactic/tests/ -v` — green (71 passed),
  added verification for the Phase 2 amendment above (`Syntax.__init__` guard wrap).
- Ad-hoc check: constructing two models back-to-back on one thread succeeds; constructing from
  a second thread while the first is inside `__init__` raises `ConcurrentConstructionError`
  rather than crashing.

---

### Phase 3: Rewrite the two concurrency tests to assert the contract [COMPLETED]

**Goal**: Both tests exercise the documented contract and run in the default (unfiltered-by-
`slow`) suite. Neither is skipped, `xfail`ed, or left behind a `slow` marker.

**Tasks**:
- [x] Rewrite `code/tests/integration/test_performance.py::TestConcurrentPerformance::test_sequential_vs_concurrent`
  (3 threads). Drop the load-sensitive `concurrent_time < sequential_time * 2` assertion
  entirely — it is exactly the class of wall-clock assertion the file's own header comment
  flags as unreliable. The new test:
  - Starts 3 threads each calling `create_test_model({'N': 3})`, recording per-thread outcome
    as one of `ok` / `ConcurrentConstructionError` / `other-exception` (with the exception
    captured, never swallowed — the current `except Exception: return False` swallow must go).
  - Asserts every thread terminated (`not thread.is_alive()` after join).
  - Asserts every outcome is `ok` or `ConcurrentConstructionError`, and that `other-exception`
    is empty — failing with the captured exception in the message.
  - Asserts at least one thread succeeded (the guard must not deadlock or starve everyone).
  - Carries a docstring stating what contract it pins and why it is not a performance test.
  - Note in the docstring that all-`ok` is a legitimate outcome when the scheduler happens to
    serialize the threads; the contract is "no crash, contention reported loudly if it occurs".
- [x] Rewrite `code/tests/integration/test_timeout_resources.py::TestResourceLimits::test_concurrent_model_building`
  (5 threads) the same way. Keep the thread count at 5 — the report measured 100% crash rate
  there, so it is the stronger regression detector.
- [x] Relocate the `slow` marker in both files: replace the module-level
  `pytestmark = pytest.mark.slow` (`test_performance.py:18`, `test_timeout_resources.py:19`)
  with explicit `@pytest.mark.slow` on the classes that carry wall-clock/timing assertions,
  leaving the two rewritten contract tests unmarked. Preserve the existing explanatory comment
  blocks verbatim, adjusted only to say they now apply per-class. This is required by the task
  statement (the tests must not merely be marked) and is deliberately mechanical to minimize
  collision with Task 136, which owns the budgets themselves.
  **Deviation**: `TestResourceLimits` (test_timeout_resources.py) mixes the contract test with
  two other tests (`test_large_state_space`, `test_many_propositions`) that have no wall-clock
  assertions of their own but exercise expensive large-N construction. A class-level mark would
  have wrongly marked the contract test slow too, so those two tests were marked individually
  with `@pytest.mark.slow` at the method level instead of class level, preserving their prior
  filtered-out status under the old module-level marker without touching the contract test.
  `TestConcurrentPerformance` (test_performance.py) has no such mixing — it contains only the
  one rewritten test, so it received no marker at all (class-level or method-level).
- [x] Record in the phase notes exactly which classes received the relocated marker, for Task
  136's benefit. **Classes/methods marked `@pytest.mark.slow`**: test_performance.py —
  `TestExecutionPerformance`, `TestMemoryPerformance`, `TestBatchPerformance`,
  `TestCachingPerformance`, `TestWorstCasePerformance` (all class-level).
  test_timeout_resources.py — `TestTimeoutHandling`, `TestInterruptHandling`,
  `TestPerformanceDegradation`, `TestResourceRecovery` (class-level); `TestResourceLimits`
  is unmarked at the class level with `test_large_state_space` and `test_many_propositions`
  marked individually (method-level) — see deviation note above. Unmarked (default suite):
  `TestConcurrentPerformance` (whole class) and
  `TestResourceLimits::test_concurrent_model_building` (one method within an otherwise-slow
  -leaning class).

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `code/tests/integration/test_performance.py` — rewrite `test_sequential_vs_concurrent`; relocate module marker
- `code/tests/integration/test_timeout_resources.py` — rewrite `test_concurrent_model_building`; relocate module marker

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/integration/test_performance.py::TestConcurrentPerformance -v` — passes.
- `PYTHONPATH=code/src pytest code/tests/integration/test_timeout_resources.py::TestResourceLimits::test_concurrent_model_building -v` — passes.
- `PYTHONPATH=code/src pytest code/tests/integration/test_performance.py code/tests/integration/test_timeout_resources.py --collect-only -q -m "not slow"` — collects exactly the two rewritten tests (and any other now-unmarked tests), confirming the marker relocation did what was intended. **Run and confirmed**: collects exactly
  `TestConcurrentPerformance::test_sequential_vs_concurrent` and
  `TestResourceLimits::test_concurrent_model_building` (2/32 selected, 0.43s — collection only,
  no test execution).
- These are single runs; they are NOT the evidence. Phase 4 supplies the evidence.
- **Run once `pgrep -af "run-oracle"` cleared**: the first single-run execution of
  `test_sequential_vs_concurrent` **failed** with `Z3Exception('Sort mismatch')` — this is what
  triggered the Phase 2 amendment above (extending the guard to `Syntax.__init__`). After that
  fix: 3/3 consecutive runs of `test_sequential_vs_concurrent` passed, and 1/1 run of
  `test_concurrent_model_building` passed. `--collect-only -m "not slow"` still selects exactly
  the two contract tests (2/32).

---

### Phase 4: Repeat-sample validation [COMPLETED]

**Goal**: Statistically meaningful evidence that the crash is gone, using the report's
isolated-subprocess methodology.

**Sample count and rationale**: **20 isolated runs per test**, plus 20 runs of the two
together. A segfault kills the interpreter, so in-process repetition is impossible — each
sample must be its own pytest subprocess, checked by exit code. At the measured pre-fix rates
(3 threads: 0.625, 5 threads: 1.0), 20 clean runs of the 3-thread test drives the probability
of a surviving 62.5%-rate defect below 1e-8; even against a hypothetical residual 10% rate, 20
runs still gives ~88% detection power. 20 is the floor, not a target to negotiate down; a
single green run is explicitly not accepted.

**Tasks**:
- [x] Write `specs/135_fix_concurrent_model_building_segfault/scripts/repeat_sample.sh` (or an
  inline documented loop recorded in the evidence file) that, for a given node ID and count N,
  runs `PYTHONFAULTHANDLER=1 PYTHONPATH=code/src python -m pytest <node-id>` N times as
  separate processes and tabulates exit codes. Written and syntax-checked (`bash -n`); not yet
  exercised while the oracle exhaustive scan runs.
- [x] Run 20 isolated samples of `test_sequential_vs_concurrent`. Require 20/20 exit code 0.
  **20/20 exit 0** (`evidence/phase4-batch1.txt`).
- [x] Run 20 isolated samples of `test_concurrent_model_building`. Require 20/20 exit code 0.
  **20/20 exit 0** (`evidence/phase4-batch2.txt`).
- [x] Run 20 isolated samples of both node IDs in one pytest invocation (catches cross-test
  interaction where one test leaves the guard held). Require 20/20 exit code 0. **20/20 exit 0**
  (`evidence/phase4-batch3.txt`).
- [x] Any exit code 139 / 134 / non-zero is a hard failure: stop, capture the faulthandler
  output, and treat it as evidence the guard coverage is incomplete (return to Phase 2). **Not
  triggered**: no run in any batch produced 139, 134, or any other non-zero code; no faulthandler
  output was emitted.
- [x] Write `specs/135_fix_concurrent_model_building_segfault/evidence/repeat-sample-results.md`
  with the per-run exit-code table, the exact commands, the date, and the pre-fix baseline
  (5/8 and 6/6 crashes) for contrast. Written.

**Deviation from the plan's deferral note**: the earlier `[ ]` entries deferred these runs until
`pgrep -af "run-oracle"` cleared. The runs were instead executed **with the oracle suite still
running** (PID 405013, load average 4.0-4.6 on 24 cores). This is a deliberate, defensible
departure: Phase 4 judges samples solely by process exit code and asserts no wall-clock budget
anywhere, so external CPU contention cannot skew the outcome — and running a scheduling-dependent
race test under contention is a *stronger* probe than running it on an idle machine, not a weaker
one. The load conditions are recorded in the evidence file. The deferral was written when the
concern was timing-sensitive results; it does not apply to exit-code-only sampling.

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `specs/135_fix_concurrent_model_building_segfault/scripts/repeat_sample.sh` — new harness
- `specs/135_fix_concurrent_model_building_segfault/evidence/repeat-sample-results.md` — new evidence record

**Verification**:
- 60 total subprocess runs, all exit code 0, table recorded in the evidence file.
- Evidence file states the harness command verbatim so the run is reproducible.

---

### Phase 5: Document the single-threaded contract [COMPLETED]

**Goal**: The contract is discoverable by a user who never reads `specs/`.

**Tasks**:
- [x] Add a **Concurrency Model** subsection to `code/docs/core/ARCHITECTURE.md` (under
  *Core Architectural Principles*, cross-referenced from *Performance Architecture*) stating:
  model construction and solving are single-threaded-only; the reason (all theories build Z3
  AST against the single process-global context); what happens on violation
  (`ConcurrentConstructionError`, not a crash); and the supported way to parallelize (one
  model per *process*, not per thread). Do not cite task numbers — reference
  `models/concurrency.py` and the exception name as the durable anchors.
- [x] Update `code/docs/core/KNOWN_TEST_FAILURES.md`: the "2 crashing tests" section
  (`:65-73`) and the crash row (`:43`) now describe fixed, contract-asserting tests; update
  the "Removing the Quarantine" section (`:101`) to record that this half of the gate is
  satisfied and only the wall-clock half remains. Also updated the quarantine-count intro
  paragraph to note the set shrank from 43 to 41 now that the two fixed tests are unmarked
  entirely, without altering the historical "Current State" measured table (framed explicitly
  as pre-fix baseline pending re-verification, since the full-suite re-measurement is itself
  deferred to Phase 6/7 while the oracle job runs).
- [x] Ensure `ConcurrentConstructionError`'s docstring (Phase 1) is the single authoritative
  statement of the contract and that the `SemanticDefaults` / `ModelDefaults` docstrings
  (Phase 2) point at it rather than restating it. Confirmed: both class docstrings say "see
  `model_checker.models.concurrency` for the full contract" rather than restating it.
- [x] Add a `NOTE:` tag at `code/src/model_checker/solver/type_guards.py` (near lines 96 and
  150) recording the unconditional `import cvc5.pythonic` defect — that it loads a native
  extension for an unused backend on every constraint assert, that it is not a crash cause,
  and that it warrants its own task. Change no behavior there. Two `NOTE:` tags added, one at
  each site named in the plan; no behavior changed (only comments added).

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `code/docs/core/ARCHITECTURE.md` — new Concurrency Model subsection
- `code/docs/core/KNOWN_TEST_FAILURES.md` — update crash-test rows and quarantine-removal section
- `code/src/model_checker/solver/type_guards.py` — `NOTE:` tag only, no behavior change

**Verification**:
- `grep -rn "ConcurrentConstructionError" code/docs/` returns the ARCHITECTURE.md reference.
- `bash .claude/scripts/`-driven `/fix-it` style scan (or a plain `grep -rn "NOTE:" code/src/model_checker/solver/type_guards.py`) finds the new tag.
- No task-number strings introduced anywhere under `code/` (per
  `.claude/rules/no-task-references-in-deliverables.md`).

---

### Phase 6: Regression sweep [COMPLETED]

**Goal**: Confirm the guard did not break any sequential path, without depending on exclusive
access to test infrastructure.

**Tasks**:
- [x] Run the package unit suites per theory (`bimodal`, `logos`, `exclusion`, `imposition`)
  as separate targeted invocations rather than one full-suite sweep, so a contended machine
  does not turn one long run into an unreadable result. Results:
  - `logos` — **40 passed** (0.45s)
  - `exclusion` — **77 passed** (0.75s)
  - `imposition` — **98 passed** (10.95s)
  - `bimodal` — **258 passed, 1 failed** (58.01s):
    `test_example_cases[BM_CM_4-example_case9]`. This is the same pre-existing, load-sensitive
    flake Phase 2 documented, not a regression: re-run in isolation it **passed in 21.39s**
    against its `max_time=30` budget, and it also **passed** in the full-scope sweep below. The
    guard adds a lock acquire/release at constructor entry, not solve-time overhead, so it
    cannot turn a 21s solve into a 30s+ one.
- [x] Run `PYTHONPATH=code/src pytest code/tests/ -m "not slow"` (the current default filter)
  and compare the failure set against the documented baseline in
  `code/docs/core/KNOWN_TEST_FAILURES.md`. No new failures permitted. **257 passed, 0 failed,
  30 deselected** (9.15s).
  Because the documented baseline was measured at the wider `tests/ src/model_checker/` scope,
  that scope was also run for an apples-to-apples comparison:
  `PYTHONPATH=code/src pytest code/tests/ code/src/model_checker/` -> **2154 passed, 0 failed,
  41 deselected, exit 0** (5:14).

  | Metric | Documented baseline | This run | Delta |
  |--------|--------------------|----------|-------|
  | Passed | 2137 | 2154 | +17 |
  | Failed | 0 | **0** | 0 |
  | Deselected | 43 | 41 | -2 |

  Both deltas are fully accounted for, with no unexplained movement: the **-2 deselected** is
  exactly the two crash tests, now unmarked and running (confirming the 43 -> 41 claim Phase 5
  wrote into `KNOWN_TEST_FAILURES.md`); the **+17 passed** is those same 2 tests plus the 15
  new guard unit tests in `models/tests/unit/test_concurrency.py` (count verified by
  `--collect-only`: 15 tests). The failure set is empty, i.e. equal to the baseline. No new
  failures.
- [x] Run `PYTHONPATH=code/src pytest code/tests/integration/test_performance.py code/tests/integration/test_timeout_resources.py -m slow` to confirm the still-quarantined timing tests behave as before (their pass/fail state is load-sensitive by design — record observed load, do not treat a timing failure here as a regression from this task).
  **1 failed, 29 passed, 2 deselected** (42.08s). The single failure is
  `TestExecutionPerformance::test_simple_model_performance`, failing on
  `assert elapsed < 1.0` at **1.09s** — matching the "~1.09 s" figure already recorded in
  `KNOWN_TEST_FAILURES.md`'s "The 3 failing tests" table verbatim. This is one of the three
  documented ungrounded wall-clock budgets owned by Task 136, is not a correctness failure, and
  is explicitly out of scope here per this plan's Non-Goals. The 2 deselected under `-m slow`
  are the two rewritten contract tests — independent re-confirmation that the Phase 3 marker
  relocation holds.
- [x] Note in the phase record whether the oracle suite was running concurrently, since it
  affects timing-sensitive results. **The oracle suite (`oracle/run-oracle-suite.sh`, PID
  405013) was running concurrently for every run in this phase.** Observed load average ranged
  1.84-2.49 (1-min) on 24 cores. This is the most likely explanation for the `BM_CM_4`
  full-suite flake and is consistent with `test_simple_model_performance` landing just 9% over
  a 1.0s budget. No `oracle/` test was run by this phase; the sibling task owns that surface.

**Timing**: 1 hour

**Depends on**: 3, 5

**Files to modify**:
- None (verification only; findings recorded in the phase notes and the eventual summary)

**Verification**:
- Theory unit suites green.
- `-m "not slow"` failure set equal to or smaller than the documented baseline.
- Any timing-test movement explained by load, not by the guard.

---

### Phase 7: Gated removal of the `-m "not slow"` quarantine [NOT STARTED]

**Goal**: Delete the quarantine clause — but only when both defects it covers are fixed.

**GATE (evaluate first, before any edit)**: read Task 136
(`ground_wallclock_performance_budgets`) status from `specs/state.json`:

```bash
jq -r '.active_projects[] | select(.project_number==136) | .status' specs/state.json
```

- If `completed`: proceed with the tasks below.
- If anything else (currently `not_started`): **do not touch `code/pyproject.toml`.** Mark this
  phase `[BLOCKED]`, record the blocker in the summary and in
  `.orchestrator-handoff.json`'s `blockers` array as "quarantine removal gated on Task 136",
  and close the task as `[PARTIAL]`. Phases 1-6 stand on their own; the quarantine clause
  covers two independent defects and removing it with only one fixed would re-break the
  default run.

**Tasks (only if the gate passes)**:
- [ ] Delete the `-m \"not slow\"` clause from `addopts` in `code/pyproject.toml:104`, leaving
  `--durations=0 -v --import-mode=importlib`. Delete the clause — do not relax it — per the
  comment block's own instruction.
- [ ] Delete the now-obsolete TEMPORARY quarantine comment block above `addopts`
  (`code/pyproject.toml:85-103`) and update the `slow` marker description in `markers` so it
  no longer describes a quarantine.
- [ ] Remove any remaining `slow` markers that existed only for quarantine purposes (keep any
  that genuinely denote long-running tests, if Task 136 established such a convention).
- [ ] Run the unfiltered suite `PYTHONPATH=code/src pytest code/tests/ -v` **3 times** as
  separate invocations, recording pass/fail counts and durations for each. All three must be
  green with an identical failure set (ideally empty). A single green run does not close this
  phase.
- [ ] Record in the summary, explicitly: that an unfiltered run was verified green, the number
  of repeat runs, their results, and the observed machine load conditions.

**Timing**: 1 hour

**Depends on**: 4, 6

**Files to modify**:
- `code/pyproject.toml` — remove `-m "not slow"` from `addopts`, remove the quarantine comment block, update the `slow` marker description

**Verification**:
- `grep -n 'not slow' code/pyproject.toml` returns nothing.
- 3 unfiltered runs, all green, same result set each time — recorded in the summary.
- If the gate did not pass: `code/pyproject.toml` is unmodified and the blocker is recorded.

---

## Testing & Validation

- [x] Guard unit tests pass, covering reentrancy, cross-thread rejection, and release-on-exception. (15 tests)
- [x] `test_sequential_vs_concurrent` passes 20/20 isolated subprocess runs (exit code 0).
- [x] `test_concurrent_model_building` passes 20/20 isolated subprocess runs (exit code 0).
- [x] Both tests together pass 20/20 isolated subprocess runs.
- [x] Neither test is skipped, `xfail`ed, or marked `slow`. (Both deselected under `-m slow`,
  both selected in the default run.)
- [x] Theory unit suites (bimodal, logos, exclusion, imposition) green — no sequential regression.
  (One pre-existing load-sensitive bimodal flake, passes in isolation and in the full-scope run.)
- [x] Iterate suites green — same-thread nesting still works. (220 passed, verified in Phase 2;
  re-covered by the full-scope 2154-passed sweep in Phase 6.)
- [x] `-m "not slow"` failure set no worse than the documented baseline. (0 failures vs 0.)
- [x] Contract documented in `ARCHITECTURE.md` and reachable from class docstrings.
- [ ] (Gated) unfiltered `pytest code/tests/` green across 3 repeat runs. **BLOCKED on Task 136**
  — Phase 7 not started; `code/pyproject.toml` deliberately untouched.

## Artifacts & Outputs

- `code/src/model_checker/models/concurrency.py` — guard + `ConcurrentConstructionError`
- `code/src/model_checker/models/tests/unit/test_concurrency.py` — guard unit tests
- Modified: `models/semantic.py`, `models/structure.py`, `models/constraints.py`
- Modified: `code/tests/integration/test_performance.py`, `code/tests/integration/test_timeout_resources.py`
- Modified: `code/docs/core/ARCHITECTURE.md`, `code/docs/core/KNOWN_TEST_FAILURES.md`
- Modified (comment only): `code/src/model_checker/solver/type_guards.py`
- Modified (gated): `code/pyproject.toml`
- `specs/135_fix_concurrent_model_building_segfault/scripts/repeat_sample.sh`
- `specs/135_fix_concurrent_model_building_segfault/evidence/repeat-sample-results.md`
- `specs/135_fix_concurrent_model_building_segfault/summaries/01_single-threaded-construction-guard-summary.md`

## Rollback/Contingency

- Each phase commits separately (`task 135 phase {P}: {name}`), so any phase can be reverted
  in isolation. The riskiest single commit is Phase 2 (guard wiring); reverting it restores
  the pre-fix behavior exactly, since Phase 1's module is inert until wired.
- If Phase 4 finds a surviving crash, the guard's coverage is incomplete: capture the
  faulthandler trace, identify which constructor the faulting frames sit under, and extend the
  wrap in Phase 2 to that entry point. Do not widen scope toward per-thread contexts — that
  path was evaluated and rejected.
- If the guard turns out to break a legitimate sequential nesting pattern not caught in Phase 2,
  the fix is to confirm the reentrancy depth accounting, not to weaken the cross-thread
  rejection.
- Phase 7 is independently revertible: restoring the `-m "not slow"` clause and its comment
  block re-establishes the quarantine without touching the fix.
