# Research Report: Concurrent Model-Building Segfault

## Summary

The intermittent crash in `test_sequential_vs_concurrent` (3 threads) and
`test_concurrent_model_building` (5 threads) is caused by multiple threads
concurrently constructing Z3 AST nodes (sorts, functions, comparisons,
quantified formulas) inside `BimodalSemantics.__init__` / `build_frame_constraints`
against a single shared, unsynchronized Z3 context object
(`z3.z3._main_ctx`, exposed to user code as `z3.main_ctx()`). Every bare
`z3.Function(...)`, `z3.BitVecSort(...)`, `z3.ForAll(...)`, comparison
operator (`__gt__`, etc.) used throughout `theory_lib/bimodal/semantic/core.py`
allocates into that one process-global context with no locking anywhere in
the call path. Z3's Python bindings are documented upstream as not
thread-safe for concurrent use of a single `Context`; this codebase has
never had a concurrency-safe construction path, and nothing in production
(`builder/runner.py`) ever calls model construction from more than one
thread — the two crashing tests are the only call sites in the repository
that do.

`cvc5.cvc5_python_base` appearing as "the faulting extension module" in the
crash dumps is a red herring caused by an unrelated, always-on import: it is
not evidence of cvc5 participating in the crash. Every crash stack trace
collected below is entirely inside `z3core.py`/`z3.py`/`bimodal/semantic/core.py`;
no thread ever touches cvc5 code.

Repeat-sample reproduction (see Section 2): the 3-thread test crashed
**5/8 runs (62.5%)**; the 5-thread test crashed **6/6 runs (100%)**. Wrapping
`create_test_model()` calls in a single `threading.Lock()` (no other change)
eliminated the crash across **8/8 runs (0%)** at 5 threads — confirming the
mechanism is unsynchronized concurrent construction, not something specific
to `N=3` or a one-off environmental fluke.

**Recommendation**: declare model construction single-threaded-only,
enforce it with a fail-fast guard (a non-reentrant lock that raises a clear
`RuntimeError` instead of segfaulting if concurrent construction is
attempted), and rewrite the two tests to assert that documented contract.
Full thread-safety (per-thread `z3.Context()` objects threaded through every
constructor call in every theory) is rejected as disproportionate: it would
require auditing and modifying every direct Z3 call site across
`theory_lib/*/semantic/*.py`, `models/semantic.py`, and the solver
abstraction layer, plus making several existing module-level caches
(`solver/registry.py`, `solver/backend.py`, `z3_shim.py`) and
`isolated_z3_context()`'s global `_main_ctx` swap thread-aware, in service
of a capability nothing in the actual product uses or needs. See Section 5
for the full comparison and Section 6 for concrete code changes.

---

## 1. Why `cvc5.cvc5_python_base` is loaded on the default z3 path

Empirically traced with an `__import__` hook (see Appendix A for the full
trace). The import is triggered from inside the **z3-only** solve path,
not from cvc5 code, pytest collection, or theory registration:

```
Z3SolverAdapter.assert_tracked()          (solver/z3_adapter.py:84)
  -> assert_backend_types(constraint, "z3")   (solver/type_guards.py:47)
    -> _check_not_cvc5_type(constraint)       (solver/type_guards.py:96)
      -> import cvc5.pythonic as cvc5         # <-- loads cvc5.cvc5_python_base
```

`type_guards._check_not_cvc5_type()` is a debugging aid: on **every single
constraint assertion**, even when the active backend is z3, it imports
`cvc5.pythonic` so it can `isinstance()`-check the constraint against
cvc5's expression types and catch accidental cross-backend type leakage.
Because cvc5 is installed in this environment, the import succeeds (no
`ImportError` short-circuit), so `cvc5.cvc5_python_base` — cvc5's native
extension module — gets mapped into the process on the very first
`solver.assert_tracked()` call of the very first model built, regardless of
`settings['solver']`. This was confirmed directly:

```python
>>> from tests.utils.helpers import create_test_model
>>> import sys; before = {m for m in sys.modules if 'cvc5' in m}
>>> create_test_model({'N': 3})
>>> after = {m for m in sys.modules if 'cvc5' in m}
# before: set()
# after:  {'cvc5', 'cvc5.pythonic', 'cvc5.cvc5_python_base',
#          'cvc5.pythonic.cvc5_pythonic', 'cvc5.pythonic.cvc5_pythonic_printer'}
```

(A secondary, narrower contributor exists for full-suite runs: any pytest
collection that includes `solver/tests/unit/test_equivalence.py` or
`theory_lib/logos/tests/integration/test_solver_comparison.py` also imports
cvc5 at **collection time**, via module-level
`pytestmark = pytest.mark.skipif(not detect_cvc5(), ...)`. This was verified
the same way but is not what explains the isolated single-test crash dumps
below, since neither module is collected when running the two crashing
tests by node ID.)

**Consequence for the crash investigation**: `cvc5.cvc5_python_base` being
resident in the process is unconditional and incidental to backend choice —
it says nothing about which backend's C code is actually executing when the
segfault occurs. All stack traces gathered below (Section 2) show every
live thread inside Z3 code at the moment of the crash; none are inside
cvc5 code. This is out of scope to fix here (it is a debugging aid, not a
bug), but is worth flagging separately: it means every model build in this
process, cvc5-only or not, pays one cvc5 native-extension load, and it
means "cvc5 loaded" can never again be treated as a signal of "cvc5 code is
running" when reading a fault dump from this codebase.

---

## 2. Repeat-sample reproduction data

Each test was run as its own pytest subprocess (a segfault kills the
interpreter, so in-process repetition inside a single pytest session is not
possible for this class of crash). `PYTHONFAULTHANDLER=1` was set to
capture native stack traces.

### `test_sequential_vs_concurrent` (3 threads), 8 isolated runs

| Run | Exit code | Result |
|-----|-----------|--------|
| 1 | 139 (SIGSEGV) | crash |
| 2 | 0 | pass |
| 3 | 0 | pass |
| 4 | 139 (SIGSEGV) | crash |
| 5 | 139 (SIGSEGV) | crash |
| 6 | 139 (SIGSEGV) | crash |
| 7 | 0 | pass |
| 8 | 0 | pass |

**5/8 crashed (62.5%)** — consistent with the task description's earlier
"1 in 3" observation; small-sample rates will vary run to run, but the
mechanism reproduces reliably within a handful of attempts and is not a
one-off.

### `test_concurrent_model_building` (5 threads), 6 isolated runs

| Run | Exit code | Result |
|-----|-----------|--------|
| 1 | 139 (SIGSEGV) | crash |
| 2 | 139 (SIGSEGV) | crash |
| 3 | 139 (SIGSEGV) | crash |
| 4 | 139 (SIGSEGV) | crash |
| 5 | 139 (SIGSEGV) | crash |
| 6 | 139 (SIGSEGV) | crash |

**6/6 crashed (100%)**. Crash probability scales with thread count (3
threads: 62.5%; 5 threads: 100%), which is exactly what an unsynchronized
data race predicts (more concurrent writers to the same shared structure
-> higher collision probability) and is hard to explain any other way.

### Crash-site diversity (evidence of memory corruption, not one bad line)

Across the 11 observed crashes, the faulting frame was **not** the same
line every time — it moved around inside Z3's native call surface,
depending on exactly which two AST-construction operations happened to
interleave that run:

```
# Run A: two threads inside __init__/build_frame_constraints simultaneously
Thread 1: z3/z3.py:380 __del__                          (AST finalizer, GC-triggered)
Thread 2: z3core.py:2911 Z3_get_sort_kind
          -> z3.py:587 _sort_kind -> z3.py:698 _to_sort_ref -> z3.py:823 domain
          -> z3.py:901 __call__
          -> bimodal/semantic/core.py:844 is_valid_time_for_world
          -> bimodal/semantic/core.py:1041 valid_array_domain
          -> bimodal/semantic/core.py:943 world_interval_constraint
          -> bimodal/semantic/core.py:601 build_frame_constraints
          -> bimodal/semantic/core.py:88 __init__

# Run B: different site entirely
Current thread: z3core.py:2027 Z3_mk_gt -> z3.py:2792 __gt__
                 -> bimodal/semantic/core.py:831 is_valid_time
                 -> bimodal/semantic/core.py:559 build_frame_constraints
                 -> bimodal/semantic/core.py:88 __init__
Other thread:   z3core.py:1884 Z3_mk_func_decl -> z3.py:940 Function
                 -> bimodal/semantic/core.py:190 define_primitives
                 -> bimodal/semantic/core.py:87 __init__
```

Sort-kind lookups, `Function()` declarations, comparison-operator AST
construction, and reference-counted object finalization (`__del__`) all
appeared as crash sites across different runs, all inside the same handful
of `BimodalSemantics` construction methods
(`define_sorts`/`define_primitives`/`build_frame_constraints`, called from
`__init__` at `core.py:86-88`). A single buggy line produces the same crash
signature every time; a moving crash site across different Z3 C API entry
points, always at the moment two threads are simultaneously creating or
destroying AST nodes in the same context, is the signature of a shared
data-structure race (Z3's context-internal hash-consing / reference-count
tables) rather than a logic bug in ModelChecker's own Python code.

### Validation: a single lock eliminates the crash

To confirm the diagnosis (not just correlate with it), `create_test_model()`
calls in a copy of the 5-thread test were serialized with one
process-global `threading.Lock()` — no other change:

```python
_lock = threading.Lock()

def build_model():
    with _lock:
        create_test_model({'N': 3})
```

**8/8 runs completed with no crash** (vs. 0/6 unguarded at the same thread
count). This is direct evidence that the fix surface is "serialize access
to Z3 AST construction," not something specific to `N=3`, to `bimodal`, or
to environment flakiness.

---

## 3. Shared mutable state touched during `BimodalSemantics.__init__`

In call order from `BimodalSemantics.__init__` (`bimodal/semantic/core.py:67`):

1. **`super().__init__(settings)`** (`models/semantic.py:81`) calls
   `self._reset_global_state()` (`models/semantic.py:83`) **before** any
   instance state exists. `SemanticDefaults._reset_global_state()`
   (`models/semantic.py:151`) resets `self._cached_values`; the bimodal
   override (`bimodal/semantic/core.py:91-131`) additionally calls
   `gc.collect()` unconditionally on every construction
   (`core.py:130-131`). `gc.collect()` walks and potentially frees every
   Python object in the process, including Z3 `AstRef` wrapper objects
   whose `__del__` (`z3.py:380`, seen live in the crash traces above) calls
   back into the Z3 C API (`Z3_dec_ref`) against the same shared context
   other threads are actively mutating. Running full-process GC from N
   threads simultaneously while N other threads are mid-construction of
   AST nodes in the same context is an independent way to trigger the same
   race, on top of the AST-construction race itself.

2. **Z3's implicit global context.** `define_sorts()`, `define_primitives()`,
   and `build_frame_constraints()` (`core.py:134-`, `147-`, `483-`) call
   bare `z3.BitVecSort`, `z3.IntSort`, `z3.Function`, `z3.ForAll`,
   `z3.Exists`, `z3.Int`, comparison operators, etc. — none of these pass an
   explicit `ctx=` argument, so all of them resolve through
   `z3.main_ctx()`, a single lazily-created `Context()` stored in the
   module-level `z3.z3._main_ctx` global (see `z3/z3.py`'s `main_ctx()`).
   This is the actual shared mutable state at the root of the crash: every
   thread's AST construction mutates the same context's internal
   hash-consing/refcount tables with no lock anywhere in the call path.

3. **`isolated_z3_context()`** (`utils/context.py`) is the codebase's
   existing tool for context isolation, but it is a **sequential-isolation**
   mechanism, not a concurrency primitive: it swaps the single process-global
   `z3.z3._main_ctx` pointer to a fresh `Context()` on entry and restores
   the saved pointer on exit (`context.py:48-65`). It is used exactly this
   way in production, one example at a time, inside a plain sequential
   `for` loop over examples and theories (`builder/runner.py:727-746`) —
   never from more than one thread. If two threads called
   `isolated_z3_context()` concurrently, they would race on the same
   `saved_ctx`/`_main_ctx` swap and each would restore the *other's*
   context on exit, which is strictly worse than the status quo (a
   silently-wrong context, not just an unsynchronized shared one). Neither
   crashing test uses `isolated_z3_context()` at all — `create_test_model()`
   builds `BimodalSemantics` directly against whatever context is currently
   installed as `z3.main_ctx()`.

4. **Module-level backend-resolution caches**, all check-then-set globals
   with no lock, in the call path (`Semantics.__init__` doesn't call these
   directly, but `_setup_solver`/`create_solver` and every `z3_shim`-mediated
   call from the theory code does, on the same threads, during the same
   window):
   - `solver/registry.py:17-22` — `_active_backend`, `_cli_override`,
     `_available_backends`, `_backend_factories`.
   - `solver/backend.py:23-24` — `_cached_module`, `_cached_backend`
     (`get_backend_module()`, `backend.py:40-60`: classic
     check-then-import-then-set race).
   - `z3_shim.py:20` — `_backend_module` (`__getattr__`, `z3_shim.py:38-49`:
     same pattern).
   These are lower-severity than the Z3 context race: CPython's import
   system serializes concurrent `importlib.import_module()` calls for the
   same module name via its own internal per-module lock, so two threads
   racing through `get_backend_module()`'s `if _cached_module is None: ...`
   check will not double-import or corrupt `sys.modules`, only
   redundantly re-run the `import_module` call and re-assign the same
   cached-module reference. They are still unsynchronized data races by
   Python's own memory model (not guaranteed atomic beyond single
   attribute assignment) and worth closing as part of a "declare
   single-threaded, fail fast" fix (Section 6), but they are not
   independently sufficient to explain the segfaults — the crash traces
   never show two threads inside `backend.py`/`z3_shim.py`/`registry.py`
   at the moment of the fault; they always show two threads inside raw Z3
   AST construction.

---

## 4. Confirming cvc5 is not involved in the crash

Every captured fault-handler stack trace (11 crashes total across both
tests) has all live threads inside one of: `z3/z3.py`, `z3/z3core.py`, or
`bimodal/semantic/core.py`. None show a frame in `cvc5/pythonic/*.py` or
`cvc5/cvc5_python_base`. Combined with Section 1's explanation for why the
module is loaded at all, this rules out "cvc5's native library is
interacting badly with Z3's native library in the same address space" as
the mechanism — the two libraries happen to share a process due to an
unrelated debug-assertion import, but only Z3's context is ever touched
concurrently by the crashing tests.

---

## 5. Recommendation: single-threaded-only contract, not full thread-safety

### Why not "make it genuinely thread-safe"

Doing this properly would mean every Z3 object created anywhere during
model construction is tied to a context that is private to the constructing
thread. Concretely that requires:

- A `z3.Context()` per thread (or per call), and threading an explicit
  `ctx=` argument through **every** direct Z3 call in every theory's
  `semantic/*.py` (`bimodal`, and by the same contract every other theory
  in `theory_lib/`), through `models/semantic.py`'s shared helpers
  (`BitVecVal`, `IntVal`, `simplify`, etc. re-exported from
  `solver/expressions.py`), and through `syntactic/atoms.py`'s `AtomSort`
  cache (already known to need per-context resets — see
  `isolated_z3_context()`'s explicit `reset_atom_sort()` calls).
- Making `solver/registry.py`, `solver/backend.py`, and `z3_shim.py`'s
  module-level caches thread-local instead of process-global (Section 3.4),
  since a per-thread context also implies backend/solver selection can no
  longer be cached as one process-wide value if two threads could ever
  legitimately use different backends concurrently.
- Deciding what `isolated_z3_context()` even means under concurrency — its
  current single-slot swap-and-restore design (Section 3.3) cannot be used
  from two threads at once without becoming thread-local itself, which
  changes its contract for every existing sequential caller
  (`builder/runner.py`, and every test listed in the earlier grep of
  `isolated_z3_context` call sites).
- Auditing `gc.collect()` inside `_reset_global_state()` for safety under
  concurrent Z3 object finalization, or removing/gating it.

This is a wide, cross-cutting change to the semantic layer of every theory
for a capability **nothing in the product uses**: `builder/runner.py` is a
plain sequential loop (Section 3.3), and a repo-wide grep for
`threading.Thread`/`ThreadPoolExecutor` in `src/model_checker` outside
`output/progress/` (a terminal spinner, unrelated to solving) returns
nothing. The only call sites in the entire repository that build models
from more than one thread are the two tests under investigation. Given the
project's "No Backwards Compatibility" / "Fail-Fast Philosophy" principles,
paying this cost to support a pattern the product does not exercise is not
justified.

### Why "declare single-threaded-only" is not just skipping the problem

The task description explicitly warns against silently marking these tests
skip/slow without recording the decision, since "the crash risk stays in
the product either way." A bare contract statement in a docstring would
have exactly that problem: nothing would stop a future caller from building
models from multiple threads and hitting the same segfault. The
recommendation is therefore **single-threaded-only, enforced by a fail-fast
guard**, not merely documented:

- Add a process-wide, non-reentrant `threading.Lock` (module-level, e.g. in
  `models/semantic.py` alongside `SemanticDefaults`, or in
  `solver/registry.py` next to the other process-wide solver state) that is
  acquired non-blocking (`acquire(blocking=False)`) at the start of
  `SemanticDefaults.__init__` (or, more precisely, around the
  `_reset_global_state()` + Z3-construction + `_setup_solver` window) and
  released when the constructing example is fully built. If acquisition
  fails, raise a clear `RuntimeError` explaining that concurrent model
  construction is not supported and pointing at this report/contract,
  instead of segfaulting. This converts an intermittent, catastrophic,
  hard-to-debug C-level crash into a deterministic, documented Python
  exception — consistent with the project's fail-fast philosophy, and it
  is exactly the mechanism validated in Section 2 (a lock around
  construction reliably prevents the race; the only difference for the
  "single-threaded-only" contract is failing loudly instead of silently
  serializing, so misuse is visible rather than silently slow).
- Rewrite both tests to assert this contract rather than exercising the
  unsupported pattern: build models from multiple threads and assert that
  every non-first thread either (a) raises the documented `RuntimeError`,
  or (b) if the guard is implemented as a blocking lock instead of
  fail-fast, that all threads complete successfully and deterministically
  (choose (a) for consistency with fail-fast; see Section 6 for both
  options). Either rewrite must be run repeatedly (per Section 2's
  methodology — isolated subprocess runs, not a single in-process pytest
  invocation) to confirm the crash is gone, not just that one run was
  green.
- Once fixed, drop `pytest.mark.slow` from both tests and coordinate with
  the wall-clock budget work (tracked separately) so the shared
  `-m "not slow"` quarantine clause in `code/pyproject.toml`'s `addopts`
  (`pyproject.toml:104`) is deleted only when both are done, and verify an
  unfiltered full run is green across repeat samples before removing it —
  per this task's stated scope.

---

## 6. Concrete code changes for the recommended fix

1. **`code/src/model_checker/models/semantic.py`** (or a new small module,
   e.g. `code/src/model_checker/models/concurrency_guard.py`, imported from
   here): add a module-level lock and acquire/release it around the
   critical section of `SemanticDefaults.__init__`:

   ```python
   import threading

   _construction_lock = threading.Lock()

   class ConcurrentConstructionError(RuntimeError):
       """Raised when model construction is attempted from a second thread
       while another construction is already in progress.

       Model construction is not thread-safe: BimodalSemantics.__init__ and
       every other theory's semantics constructor build Z3 AST nodes
       against the single process-global Z3 context (z3.main_ctx()) with
       no per-thread isolation. See specs/135_fix_concurrent_model_building_segfault
       for the investigation and rationale. Build models from one thread
       at a time (e.g. serially, or via a process pool with one model per
       process) rather than from multiple threads in the same process.
       """

   def __init__(self, combined_settings):
       if not _construction_lock.acquire(blocking=False):
           raise ConcurrentConstructionError(...)
       try:
           self._reset_global_state()
           ...  # existing body
       finally:
           _construction_lock.release()
   ```

   The lock must wrap the whole constructor body (not just
   `_reset_global_state()`), since the crash traces show the race hitting
   `define_primitives()` and `build_frame_constraints()` too, both called
   later in `__init__`. `ModelDefaults.__init__` (`models/structure.py:101`)
   also calls `self.solve(...)` -> `_setup_solver` -> `assert_tracked`,
   which builds no new AST but does mutate the solver/registry caches from
   Section 3.4; guard through the full model-build call, not just semantics
   construction, or extend the lock's scope to cover `ModelDefaults.__init__`
   as well if solving must also be serialized (recommended, since
   `create_solver()` touches the same process-global registry caches).

2. **`code/tests/integration/test_performance.py`** — replace
   `TestConcurrentPerformance.test_sequential_vs_concurrent` (currently
   asserts a performance ratio, which is exactly the load-sensitive
   assertion flagged as unreliable in the comment at the top of this file)
   with a test that asserts the documented contract: spin up 3 threads
   calling `create_test_model`, assert exactly one succeeds and the rest
   raise `ConcurrentConstructionError` (or, if threads happen to run
   sequentially due to scheduling, allow all to succeed — the contract is
   "no crash, and any concurrent contention is reported, never silent
   corruption"). Drop `pytest.mark.slow` once verified stable across
   repeat isolated runs.

3. **`code/tests/integration/test_timeout_resources.py`** — same rewrite
   for `TestResourceLimits.test_concurrent_model_building` (5 threads).
   Drop `pytest.mark.slow` once verified stable across repeat isolated
   runs.

4. **`code/pyproject.toml:104`** — remove the `-m "not slow"` clause from
   `addopts` only once both this task and the wall-clock budget work are
   complete, and only after confirming an unfiltered `pytest code/tests/`
   (or `PYTHONPATH=code/src pytest code/tests/ -v`) run is green across
   multiple repeat isolated invocations, not a single run.

5. Verification methodology for whichever fix lands: reuse the
   isolated-subprocess repeat-sample harness from Section 2 (loop of N
   separate `python -m pytest -m slow ...` invocations, checking exit code,
   not a single in-process pytest run) — a single green run proves nothing
   given the 62.5%/100% crash rates measured here.

---

## Appendix A: Environment

- Python 3.13.13, z3-solver 4.16.0, pytest 9.0.3, 24 cores / 30GB RAM.
- All commands run with `PYTHONPATH=code/src` from the `code/` directory
  and `PYTHONFAULTHANDLER=1` to capture native stack traces on fatal
  signals.
- Raw fault-handler logs and the lock-validation script from Section 2 are
  not checked into the repo (scratch artifacts); the stack-trace excerpts
  and pass/fail data above are transcribed directly from those runs.
