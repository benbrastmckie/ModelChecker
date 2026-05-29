# Research Report: Z3 Solver State Leakage - Deep Dive on Fix Options

- **Task**: 94 - fix_z3_solver_state_leakage
- **Status**: [COMPLETED]
- **Type**: z3
- **Date**: 2026-05-29
- **Mode**: Team Research (4 teammates)
- **Session**: sess_1780089555_3b3c0e

## Summary

Four parallel research agents investigated process-level isolation (Option A), explicit Z3 context management (Option B), critical analysis of assumptions, and strategic architecture. The team converged on a clear recommendation: **Option B2 (global `_main_ctx` swap via context manager)** is the correct fix -- a ~25-line change across 3 files that provides full C-level Z3 isolation per example. Option A (multiprocessing) has a hard blocker (Z3 objects cannot be pickled). Full `ctx=` threading (Option B1) is unnecessary at 23+ files of changes. The simpler B2 variant achieves identical isolation by temporarily replacing `z3.z3._main_ctx` with a fresh `z3.Context()` for each example run.

## Key Findings

### Finding 1: Root Cause Confirmed and Refined (Teammates A, B, C)

The diagnosis from report 01 is correct but the failure mechanism is more precise than originally described:

- `reset_z3_context()` hits the `elif hasattr(z3, 'main_ctx')` branch and sets `z3.main_ctx = None`, which **corrupts the function** (not the context object)
- `importlib.reload(z3)` then restores the function but does NOT reset `z3.z3._main_ctx`, which holds the actual Context
- The actual C-level context lives at `z3.z3._main_ctx` (the `z3.z3` submodule), NOT at `z3._main_ctx` (top-level module)
- `_initialize_z3_context()` in `example.py` always fails silently (`z3.Context` has no `.solver` attribute)
- The codebase has 5 scattered reset attempts, all ineffective

**Confidence**: HIGH (empirically confirmed by teammates B and C independently)

### Finding 2: Option A Has a Hard Serialization Blocker (Teammates A, C)

Z3 `ModelRef`, `ExprRef`, `BitVecRef`, and all Z3 expression objects **cannot be pickled** (`ValueError: ctypes objects containing pointers cannot be pickled`). The codebase has extensive post-solve `z3_model.eval()` calls across 5+ modules for result extraction and display. For Option A to work, ALL result extraction and display formatting must happen inside the subprocess before returning plain dicts.

Teammate A proposed a concrete design where `process_example()` becomes the process boundary and the subprocess captures stdout, returning `{output_text, model_found, runtime, timeout, check_result}`. This is technically feasible (~135 lines) but has significant complexity:

- The iteration pattern (`_process_with_iterations`, generator-based) must be entirely replicated inside the subprocess (~250 lines of logic)
- Interactive mode (`prompt_for_iterations`) cannot work inside a subprocess
- Progress bar UX requires IPC coordination
- Fork overhead is ~0.12-0.15s per example (acceptable but non-zero)

**Verdict**: Option A provides categorical isolation guarantees but is not recommended as the primary fix due to architectural complexity. It could serve as a secondary CI/testing mode.

**Confidence**: HIGH (pickling failure confirmed empirically)

### Finding 3: Option B Splits Into Two Distinct Variants (Teammate B)

**B1 - Explicit ctx threading**: Add `ctx=ctx` to every Z3 constructor call. Requires changes to 23+ production files. Risky due to partial-threading bugs (one missed `ctx=` causes silent `Z3Exception: Context mismatch`). Effectively re-implements what B2 provides for free.

**B2 - Global `_main_ctx` swap** (RECOMMENDED): Install a fresh `z3.Context()` as the global context for each example via a context manager. Requires changes to exactly **3 files, ~25 lines**:

| File | Change | Lines |
|------|--------|-------|
| `utils/context.py` | Add `isolated_z3_context()` context manager, deprecate `reset_z3_context()` | ~20 |
| `builder/runner.py` | Wrap `process_example()` call with `with isolated_z3_context():` | ~2 |
| `builder/example.py` | Replace `_initialize_z3_context()` body with pass | ~1 |

The mechanism: `z3.z3._main_ctx` is a module-level attribute that all Z3 Python API calls use via `z3.z3.get_ctx(None)`. Swapping it to a fresh `z3.Context()` before each example ensures all Z3 objects (sorts, functions, expressions, solvers) are created in an isolated C-level context. Each `z3.Context()` wraps a freshly allocated `Z3_context` C pointer with no shared learned lemmas, caches, or heuristic state.

Key properties verified empirically:
- Each `z3.Context()` creates a distinct C-level pointer (different `ref()` values)
- The swap is transparent to `z3_shim.py` (shim delegates to `z3` module which reads `_main_ctx`)
- The swap is transparent to `z3_adapter.py` (uses `import z3` directly, but object creation happens inside the wrapped call)
- Nested contexts restore correctly via `try/finally`
- Context creation costs ~2.3ms (negligible)

**Confidence**: HIGH (all claims backed by executed experiments)

### Finding 4: AtomSort Cache Requires Reset (Teammates B, C)

`syntactic/atoms.py` caches `DeclareSort('AtomSort')` in a module-level `_atom_sort` variable. This sort is context-bound. The `reset_atom_sort()` function already exists and is called by the lifecycle hook system. The `isolated_z3_context()` wrapper must call `reset_atom_sort()` before yielding (to clear the old-context sort) and after restoring (to clear the new-context sort).

**Confidence**: HIGH

### Finding 5: Timeout Sensitivity Is an Alternative/Contributing Factor (Teammate C)

The critic identified that BM_CM_3's `max_time: 2` may be insufficient for cold solving of a UFBV+quantifier problem. Z3's MBQI solver has known nondeterministic behavior (Z3 issue #7525). The observed "state leakage" could be partially explained by timeout sensitivity -- 2 seconds is too short cold, but sufficient when MBQI has warm heuristic state.

This does not invalidate the fix (fresh contexts are architecturally correct regardless), but it means some examples may still need timeout increases even after the fix. Specifically, BM_CM_3 and BM_CM_1 should be tested with longer timeouts after the context isolation fix is applied.

**Confidence**: MEDIUM (hypothesis, not yet tested empirically)

### Finding 6: Theory Landscape Is Contained (Teammate D)

Only two top-level theories exist: `LogosSemantics` (21 Z3 calls) and `BimodalSemantics` (20 Z3 calls), both inheriting from `SemanticDefaults`. Logos has 7 subtheories but these share `LogosSemantics` and contribute only operators, not independent Z3 primitives. The `iterate/` package has ~48 Z3 calls but these operate on existing expressions (context inherited from creation), not constructing new named declarations.

With B2, none of these files need changes -- the context swap happens at the runner level and propagates transparently.

**Confidence**: HIGH

### Finding 7: Z3 Maintainer Guidance Aligns With B2 (Teammates B, D)

Z3 GitHub discussion #4992 explicitly states:
- `Z3_reset_memory()` from Python causes segfaults and should not be used
- Creating fresh `Solver()` instances per problem is correct
- Fresh `z3.Context()` objects provide complete isolation

The `_main_ctx` swap approach is consistent with this guidance: each example gets a fresh context without requiring explicit `ctx=` threading.

**Confidence**: HIGH

## Synthesis

### Conflicts Resolved

**Conflict 1: Option B scope estimates**
- Teammate B estimated 3 files for B2, 23 files for B1
- Teammate C estimated 50+ files for "Option B"
- Teammate D estimated 41 critical calls

**Resolution**: The apparent conflict arises from conflating B1 and B2. Teammate C's 50+ file estimate applies to B1 (full ctx threading). B2 requires only 3 files. The 41 critical Z3 construction calls (teammates D) are in semantic files that do NOT need changes under B2 -- they transparently use the swapped global context.

**Conflict 2: Whether timeout sensitivity matters**
- Teammate C argues timeout sensitivity may be the primary issue
- Other teammates assume state leakage is the primary cause

**Resolution**: Both contribute. The context swap fix is architecturally correct regardless, and should be the primary fix. After applying it, BM_CM_3 and BM_CM_1 should be tested with longer timeouts to determine if they need `max_time` increases. The fix addresses the real isolation bug; timeout tuning addresses the residual performance question.

### Gaps Identified

1. **Not yet tested end-to-end**: The B2 `_main_ctx` swap has been verified in isolation experiments but has not been tested by running the full bimodal test suite. The implementation phase should include this validation.

2. **Test infrastructure needs isolation fixtures**: `conftest.py` files lack `autouse` fixtures for Z3 context isolation between test functions. This should be added as part of the fix.

3. **Dead code cleanup scope**: After the fix, `reset_z3_context()`, `reset_solver_context()`, `Z3ContextManager`, scattered `gc.collect()` calls, and `importlib.reload(z3)` can all be removed or simplified. The implementation plan should include this cleanup.

4. **`z3.reset_params()` interaction**: `runner.py:327` calls `z3.reset_params()` which resets global solver parameters. Its interaction with context isolation is not fully analyzed and may reset the timeout parameter set earlier.

### Recommendations

**Primary fix: Option B2 (global `_main_ctx` swap)**

1. Implement `isolated_z3_context()` in `utils/context.py` as a `contextlib.contextmanager`
2. Wrap `process_example()` in `runner.py` with `with isolated_z3_context():`
3. Deprecate `_initialize_z3_context()` in `example.py`
4. Call `reset_atom_sort()` inside the context manager
5. Run full test suite to validate
6. Test BM_CM_3 and BM_CM_1 in isolation with longer timeouts
7. Clean up dead reset infrastructure
8. Add `conftest.py` isolation fixtures for tests

**Future enhancement: Option A as CI mode**

Process-level isolation can be added later as an optional `--subprocess` flag for CI/testing environments where maximum isolation guarantees are desired. This is not needed for the primary fix.

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|------------------|
| A | Option A deep dive | completed | high | Mapped iterator pattern, confirmed pickling blocker, proposed subprocess design |
| B | Option B variants | completed | high | Discovered B2 variant, verified `_main_ctx` swap mechanism, provided complete implementation design |
| C | Critic | completed | high | Refined root cause mechanism, identified timeout sensitivity gap, confirmed Z3_reset_memory segfault |
| D | Strategic horizons | completed | high | Surveyed theory landscape (41 critical calls in 2 files), confirmed Z3 maintainer guidance, recommended cleanup scope |

## References

- Z3 GitHub discussion #4992: reset() vs new Solver - https://github.com/Z3Prover/z3/discussions/4992
- Z3 GitHub issue #7525: nondeterministic behavior - https://github.com/Z3Prover/z3/issues/7525
- Z3 GitHub issue #1629: changing contexts - https://github.com/Z3Prover/z3/issues/1629
- Z3py Context Class Reference - https://z3prover.github.io/api/html/classz3py_1_1_context.html
- Programming Z3 (Stanford) - https://theory.stanford.edu/~nikolaj/programmingz3.html
- `code/src/model_checker/utils/context.py` - current reset infrastructure
- `code/src/model_checker/builder/runner.py` - example processing loop
- `code/src/model_checker/builder/example.py` - per-example entry point
- `code/src/model_checker/theory_lib/logos/semantic.py` - LogosSemantics (21 Z3 calls)
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - BimodalSemantics (20 Z3 calls)
- `code/src/model_checker/z3_shim.py` - Z3 module proxy
- `code/src/model_checker/syntactic/atoms.py` - AtomSort cache
