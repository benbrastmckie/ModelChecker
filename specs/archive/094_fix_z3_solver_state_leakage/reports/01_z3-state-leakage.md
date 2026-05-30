# Research Report: Z3 Solver State Leakage Between Examples

- **Task**: 94 - fix_z3_solver_state_leakage
- **Status**: [COMPLETED]
- **Type**: z3

## Problem

Running bimodal examples produces nondeterministic results depending on which examples precede others. Specifically:

- **BM_CM_3** (`\Diamond A |= \future A`): Finds no countermodel when run alone (UNSAT after timeout), but finds one in ~0.09s when run after other examples like EX_CM_1.
- **BM_CM_1** (`\Future A |= \Box A`): Same pattern — UNSAT alone at 5s timeout, SAT in ~0.46s after other examples.

This means the Z3 solver retains internal state (learned lemmas, heuristic seeds, internal caches) across example runs, causing later examples to benefit from earlier solving work.

## Root Cause

The `reset_z3_context()` function in `code/src/model_checker/utils/context.py:50-62` does not effectively reset Z3's global state:

### Problem 1: `_main_ctx` attribute does not exist (line 81)

```python
if hasattr(z3, '_main_ctx'):
    z3._main_ctx = None
```

The attribute `_main_ctx` does not exist in the installed Z3 version. The Z3 Python bindings access the context through `z3.main_ctx()` (a function), not a module-level attribute. This line silently does nothing because `hasattr` returns False.

### Problem 2: `importlib.reload(z3)` does not reset C library state (line 92)

```python
importlib.reload(z3)
```

Reloading the Python module re-executes the module's Python code but does NOT reset the underlying Z3 C library's internal state. The C library retains:
- Learned lemmas from previous solver runs
- Internal caches and hash tables
- Heuristic state (variable ordering, phase saving)
- Sort and function declaration caches

### Call chain

1. `code/src/model_checker/models/structure.py:100-103` calls `reset_z3_context()` before each solve
2. `code/src/model_checker/builder/example.py:113-120` `_initialize_z3_context()` also attempts reset
3. Neither achieves true isolation

## Evidence

| Example | Alone | After EX_CM_1 | After full suite |
|---------|-------|---------------|------------------|
| BM_CM_3 | UNSAT (2s timeout) | SAT (0.09s) | SAT (varies) |
| BM_CM_1 | UNSAT (5s timeout) | -- | SAT (0.46s) |
| BM_CM_2 | SAT (correct) | SAT (correct) | SAT (correct) |
| BM_CM_4 | SAT (correct) | SAT (correct) | SAT (correct) |

BM_CM_2 and BM_CM_4 work in isolation because their search spaces are small enough for Z3 to find solutions within the timeout. BM_CM_1 and BM_CM_3 require more complex models that Z3 only finds quickly when it has cached internal state from previous runs.

## Affected Files

| File | Lines | Role |
|------|-------|------|
| `code/src/model_checker/utils/context.py` | 50-97 | `reset_z3_context()` / `reset_solver_context()` |
| `code/src/model_checker/builder/example.py` | 113-120 | `_initialize_z3_context()` |
| `code/src/model_checker/models/structure.py` | 100-103 | Calls reset before each solve |

## Fix Directions

### Option A: Process-level isolation (most reliable)
Run each example in a separate subprocess via `multiprocessing`. This guarantees complete Z3 state isolation since each process gets its own C library instance. Downside: higher overhead per example.

### Option B: Explicit Z3 context objects (recommended)
Create a fresh `z3.Context()` for each example and pass it explicitly to all Z3 API calls (`z3.Solver(ctx=ctx)`, `z3.BitVecSort(N, ctx=ctx)`, etc.). This is Z3's intended isolation mechanism. Downside: requires threading the context through all solver construction code.

### Option C: `z3.Z3_reset_memory()` (quick fix, fragile)
Call `z3.Z3_reset_memory()` between examples. This is an undocumented internal API that may reset global state. Downside: not guaranteed to work across Z3 versions, may cause segfaults if any Z3 objects are still referenced.

### Option D: Increase timeouts (workaround, not a fix)
Increase `max_time` for affected examples so they find solutions even without cached state. This masks the bug rather than fixing it.

## Recommendation

Option B (explicit contexts) is the correct long-term fix. Option D (increased timeouts) can serve as an immediate workaround while Option B is implemented.

## References

- `code/src/model_checker/utils/context.py`
- `code/src/model_checker/builder/example.py`
- `code/src/model_checker/models/structure.py`
- Z3 documentation on `z3.Context()` for solver isolation
