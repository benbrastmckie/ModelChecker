# Backend Leak Analysis: Per-Example Solver Override Persistence

## Executive Summary

The `_cli_override` variable in `solver/registry.py` persists across examples, causing examples that specify `solver: cvc5` to "leak" that setting to subsequent examples that don't explicitly set a solver. The fix requires clearing the override after each example completes.

## Problem Description

### Symptoms

When running `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py`:

1. First example (`CF_CM_1`) specifies `'solver': 'cvc5'` in settings
2. Example runs with CVC5, completes (with an error during iteration due to missing `.assertions()` method)
3. Second example (`CF_CM_2`) does NOT specify a solver
4. Second example inherits CVC5 from the sticky `_cli_override`
5. Code fails because `z3.reset_params()` doesn't exist in cvc5.pythonic

**Error output**:
```
Error during iteration: 'CVC5SolverAdapter' object has no attribute 'assertions'
...
AttributeError: module 'cvc5.pythonic' has no attribute 'reset_params'
```

### Root Cause

The call chain that creates the leak:

```
BuildExample.__init__()
    -> _configure_solver_backend()
        -> set_backend_with_invalidation()
            -> set_cli_backend()  # Sets _cli_override = "cvc5"
```

The problem is `_cli_override` is never cleared. Once set, it has highest priority in `get_active_backend()`:

```python
def get_active_backend(settings: Optional[Dict[str, Any]] = None) -> str:
    # 1. CLI flag has highest priority
    if _cli_override:
        return _cli_override  # <-- This returns "cvc5" even for examples without solver setting

    # 2. Environment variable
    # 3. Settings configuration
    # 4. Default to z3
```

## Code Flow Analysis

### Files Involved

| File | Role |
|------|------|
| `solver/registry.py` | Contains `_cli_override`, `set_cli_backend()`, `clear_cli_backend()`, `get_active_backend()` |
| `solver/lifecycle.py` | Contains `set_backend_with_invalidation()` which calls `set_cli_backend()` |
| `builder/example.py` | `_configure_solver_backend()` calls `set_backend_with_invalidation()` |
| `builder/runner.py` | `process_example()` creates `BuildExample`, `_initialize_z3_context()` calls `z3.reset_params()` |

### Example Processing Sequence

```
run_examples() loop:
    for example_name, example_case in examples.items():
        for theory_name, semantic_theory in theories.items():
            process_example(example_name, example_copy, ...)
                |
                +-> BuildExample.__init__()
                |       |
                |       +-> _configure_solver_backend()
                |       |       |
                |       |       +-> set_backend_with_invalidation("cvc5")
                |       |               |
                |       |               +-> set_cli_backend("cvc5")  # LEAK: _cli_override = "cvc5"
                |       |
                |       +-> _initialize_z3_context()  # calls z3.reset_params() via z3_shim
                |
                +-> (next example inherits _cli_override="cvc5")
```

### The Missing Reset

`clear_cli_backend()` exists but is never called:

```python
def clear_cli_backend() -> None:
    """Clear CLI backend override (useful for testing)."""
    global _cli_override
    _cli_override = None
```

## Proposed Fix: Option Analysis

### Option A: Clear CLI Override After Each Example (Recommended)

**Location**: `builder/runner.py` in `process_example()` or example loop

**Change**: Add cleanup in `finally` block after example processing

```python
# In runner.py, after process_example() call
finally:
    from model_checker.solver.registry import clear_cli_backend
    clear_cli_backend()
    gc.collect()
```

**Pros**:
- Minimal code change
- Uses existing API (`clear_cli_backend()` already exists)
- Restores default behavior (z3) for examples without explicit solver

**Cons**:
- Must ensure cleanup happens even on exceptions

### Option B: Save/Restore Pattern in _configure_solver_backend

**Location**: `builder/example.py`

**Change**: Save previous backend before setting, restore in cleanup

```python
def _configure_solver_backend(self, example_case: List[Any]) -> None:
    from model_checker.solver.registry import get_active_backend, clear_cli_backend

    # Save current state
    self._previous_backend = get_active_backend()

    # ... existing logic to set backend ...

def cleanup(self):
    clear_cli_backend()  # Or restore _previous_backend
```

**Pros**:
- Keeps backend management localized to BuildExample

**Cons**:
- Requires adding cleanup method and ensuring it's called
- More complex than Option A

### Option C: Separate _settings_backend Variable

**Location**: `solver/registry.py`

**Change**: Create `_settings_backend` with lower priority than `_cli_override`

```python
_cli_override: Optional[str] = None  # CLI flags only
_settings_backend: Optional[str] = None  # Per-example settings

def set_settings_backend(backend: str) -> None:
    """Set backend from example settings (lower priority than CLI)."""
    global _settings_backend
    _settings_backend = backend

def get_active_backend(settings: Optional[Dict[str, Any]] = None) -> str:
    if _cli_override:
        return _cli_override
    if _settings_backend:
        return _settings_backend
    # ... rest of priority chain
```

**Pros**:
- Cleaner separation of concerns
- CLI flags truly override settings

**Cons**:
- Still requires clearing `_settings_backend` after each example
- More invasive change to registry.py

### Option D: Context Manager Approach

**Location**: New context manager, used in runner.py

**Change**: Create a context manager for backend scoping

```python
@contextmanager
def scoped_backend(backend: str):
    from model_checker.solver.lifecycle import set_backend_with_invalidation
    from model_checker.solver.registry import clear_cli_backend

    set_backend_with_invalidation(backend)
    try:
        yield
    finally:
        clear_cli_backend()
```

**Pros**:
- Clean, Pythonic pattern
- Automatic cleanup on exceptions

**Cons**:
- Requires changes to multiple call sites
- More complex than Option A

## Recommendation

**Option A is recommended** for these reasons:

1. **Minimal change**: Single-line addition in `runner.py`
2. **Uses existing API**: `clear_cli_backend()` already exists and is tested
3. **Clear semantics**: Each example starts with clean backend state
4. **Consistent behavior**: Examples without solver setting get the default (z3)

### Recommended Implementation

In `builder/runner.py`, modify the example processing loop (around line 764):

```python
# In run_examples() method, around line 764
try:
    self.process_example(example_name, example_copy, theory_name, semantic_theory)
finally:
    # Clear per-example solver override to prevent backend leak
    from model_checker.solver.registry import clear_cli_backend
    clear_cli_backend()
    # Force cleanup after each example to prevent state leaks
    gc.collect()
```

This ensures:
- Backend is reset after each example (success or failure)
- Next example uses its own solver setting or default
- No import needed at module level (already inside function)

## Secondary Issue: CVC5SolverAdapter Missing `.assertions()`

The error trace also shows:

```
'CVC5SolverAdapter' object has no attribute 'assertions'
```

This is a separate issue in `iterate/constraints.py` line 57 where the code assumes Z3-specific API. The adapter pattern should expose this method or the constraint generator should use adapter-agnostic APIs.

**Note**: This is out of scope for the current task but should be tracked separately.

## Test Verification

After implementing the fix, verify with:

```bash
python code/dev_cli.py code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
```

Expected behavior:
- CF_CM_1 runs with CVC5 (has `solver: cvc5`)
- CF_CM_2 runs with Z3 (no solver setting, should default to z3)
- No `reset_params` AttributeError

## Files to Modify

| File | Change |
|------|--------|
| `builder/runner.py` | Add `clear_cli_backend()` in finally block after `process_example()` |

## Summary

The backend leak occurs because `set_backend_with_invalidation()` sets `_cli_override` which persists across examples. The fix is to call `clear_cli_backend()` after each example completes, which restores default behavior for subsequent examples.
