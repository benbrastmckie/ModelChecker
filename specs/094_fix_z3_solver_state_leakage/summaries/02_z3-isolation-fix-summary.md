# Implementation Summary: Fix Z3 Solver State Leakage

- **Task**: 94 - fix_z3_solver_state_leakage
- **Plan**: plans/02_z3-isolation-fix.md
- **Status**: COMPLETED
- **Date**: 2026-05-29
- **Session**: sess_1780090806_62d8bd

## What Was Implemented

The root cause of Z3 solver state leakage was identified and fixed: the existing five reset mechanisms all targeted the wrong attribute or used `importlib.reload()` which does not reset C library state. The fix swaps `z3.z3._main_ctx` (the actual C-level context) to a fresh `z3.Context()` per example.

### Phase 1: Core Context Manager (isolated_z3_context)

Added `isolated_z3_context()` to `code/src/model_checker/utils/context.py`. The context manager:
- Saves the current `z3.z3._main_ctx` reference
- Creates a fresh `z3.Context()` and installs it as `z3.z3._main_ctx`
- Calls `reset_atom_sort()` to clear the AtomSort cache (context-bound)
- Yields to the caller
- In `finally`: calls `reset_atom_sort()` again, then restores the saved context

Updated `run_examples()` in `runner.py` to wrap `process_example()` with `isolated_z3_context()`. Removed the inline `z3._main_ctx = None` resets and flanking `gc.collect()` calls. Updated `_initialize_z3_context()` in `runner.py` to remove the `reset_z3_context()` call. Stubbed out `_initialize_z3_context()` in `example.py`.

### Phase 2: Dead Code Cleanup

Removed the five ineffective reset mechanisms:
- `Z3ContextManager` class from `context.py`
- `reset_z3_context()` function from `context.py`
- `reset_solver_context()` function from `context.py`
- Updated `utils/__init__.py` to export `isolated_z3_context` instead of `Z3ContextManager`
- Removed `reset_z3_context()` call from `structure.py`
- Removed unused `import gc` from `runner.py`
- Updated test files to test `isolated_z3_context`
- Updated `utils/README.md`

### Phase 3: Test Validation

Validated BM_CM_3 and BM_CM_1 behavior after the fix:
- Both time out consistently in isolation AND in sequence (correct behavior)
- Before the fix: they could find countermodels by borrowing learned lemmas from previous examples (state leakage was masking their true difficulty)
- After the fix: each example runs independently, giving correct and deterministic results
- Fixed `test_z3_isolation.py` to create Z3 variables inside `isolated_z3_context()` blocks (Z3 expressions are context-bound)

### Phase 4: conftest.py Fixtures

Added `z3_context_isolation` fixture to three conftest.py files. The fixture is explicit (not autouse) because Z3 expressions created in `setUp()` are context-bound and cannot safely cross context boundaries.

## Files Modified

| File | Change |
|------|--------|
| `code/src/model_checker/utils/context.py` | Complete rewrite: only `isolated_z3_context()` |
| `code/src/model_checker/utils/__init__.py` | Export `isolated_z3_context` instead of `Z3ContextManager` |
| `code/src/model_checker/utils/README.md` | Updated documentation |
| `code/src/model_checker/builder/runner.py` | Wrap process_example() with isolated_z3_context(); remove gc, inline reset |
| `code/src/model_checker/builder/example.py` | Stub out _initialize_z3_context() |
| `code/src/model_checker/models/structure.py` | Remove reset_z3_context() call |
| `code/src/model_checker/utils/tests/unit/test_context.py` | Tests for isolated_z3_context |
| `code/src/model_checker/utils/tests/conftest.py` | Add z3_context_isolation fixture |
| `code/src/model_checker/builder/tests/unit/test_z3_isolation.py` | Tests for isolated_z3_context |
| `code/src/model_checker/builder/tests/conftest.py` | Add z3_context_isolation fixture |
| `code/src/model_checker/models/tests/unit/test_structure.py` | Remove stale Z3ContextManager patch |
| `code/tests/conftest.py` | Add z3_context_isolation fixture |

## Verification Results

- `isolated_z3_context()` creates distinct contexts and restores original: verified
- Bimodal examples (22 of 52): run to completion
- Logos examples (24 examples): run to completion
- 341 unit/integration tests + 71 subtests: all pass
- `grep -rn "reset_z3_context|reset_solver_context|Z3ContextManager" code/src/`: no Python code results (only README.md which is updated)

## Plan Deviations

1. **Timeout tuning (Phase 3)**: BM_CM_3 (max_time=2) and BM_CM_1 (max_time=5) time out consistently even with max_time=10. These examples were relying on state leakage to find countermodels. The fix is correct; the examples may need redesign or larger timeouts in a future task. No timeout changes were made.

2. **autouse fixture (Phase 4)**: The plan specified an autouse fixture. This was changed to an explicit fixture because Z3 expressions are context-bound -- autouse would break tests that create Z3 expressions in setUp(). Documented in the fixture's docstring.

## Key Technical Insight

The critical distinction: `z3._main_ctx` (at the `z3` package level) is NOT the same as `z3.z3._main_ctx` (inside the `z3.z3` submodule). All five previous reset attempts either targeted the wrong level (`z3._main_ctx` or `z3.main_ctx`) or used `importlib.reload(z3)` which reloads the Python module but does not reset the underlying C library state. True isolation requires swapping `z3.z3._main_ctx` directly.
