# Research Report: Unified Z3/CVC5 Architecture

**Task**: 72 - Fix CVC5 constraint compatibility with Z3 expression types
**Date**: 2026-03-31
**Type**: Architecture Review

## Summary

This report analyzes the existing implementation plan (02_cache-invalidation-fix.md) and the current codebase to identify opportunities for a more elegant, unified architecture supporting both Z3 and CVC5 solvers. The analysis confirms that the cache invalidation approach is correct but identifies architectural improvements that create a clearer, more maintainable system.

## Architecture Analysis

### Current State: Three-Layer Abstraction

The ModelChecker currently has three layers of solver abstraction:

```
Layer 1: Solver Adapters (TrackedSolverProtocol)
         z3_adapter.py, cvc5_adapter.py
         |
Layer 2: Expression Construction (z3_shim, expressions.py)
         Delegates to active backend module
         |
Layer 3: Type System (types.py, types_runtime.py, compat.py)
         Backend-agnostic type aliases and compatibility helpers
```

**Architectural Insight**: The three layers are correctly designed. The issue is not in the architecture but in the lifecycle management of cached state across layers.

### Cached State Locations (Confirmed)

The team research correctly identified three cache locations:

| Location | Type | Purpose | Reset Function |
|----------|------|---------|----------------|
| `z3_shim._backend_module` | Module | Cached backend module (z3/cvc5.pythonic) | `_reset_backend()` |
| `syntactic/atoms._atom_sort` | Sort | Cached uninterpreted sort declaration | `reset_atom_sort()` |
| `solver/registry._available_backends` | Dict | Backend availability cache | `reset_registry()` |

**Analysis**: The caches are reasonable performance optimizations. The issue is that no single function coordinates their invalidation when the backend changes.

### Entry Points for Backend Selection

Current entry points where backend selection occurs:

1. **CLI** (`__main__.py:290-302`): Sets backend via `set_cli_backend()` before any model construction
2. **Example settings**: Per-example `solver` key in settings dict (not currently handled early)
3. **Environment variable**: `MODEL_CHECKER_SOLVER` (checked at runtime)
4. **Test fixtures**: Manual cache invalidation via `switch_solver()` in test code

**Gap Identified**: The CLI properly sets the backend early, but per-example settings are not processed until after z3_shim has already been accessed (importing z3_shim triggers lazy caching).

## Improvement Opportunities

### 1. Unified Cache Invalidation (Plan Phase 1 - Confirmed)

The plan's approach is correct. However, consider a more elegant implementation pattern:

**Current Plan**:
```python
def _invalidate_expression_caches() -> None:
    from model_checker.z3_shim import _reset_backend
    from model_checker.syntactic.atoms import reset_atom_sort
    _reset_backend()
    reset_atom_sort()
```

**Suggested Enhancement**: Create a formal "backend lifecycle" module:

```python
# solver/lifecycle.py
"""Backend lifecycle management for clean solver switching."""

_switch_hooks: List[Callable[[], None]] = []

def register_cache_invalidation(hook: Callable[[], None]) -> None:
    """Register a function to call when backend changes."""
    _switch_hooks.append(hook)

def invalidate_all_caches() -> None:
    """Invalidate all registered expression caches."""
    for hook in _switch_hooks:
        hook()

def set_backend_with_invalidation(backend: str) -> None:
    """Set backend and invalidate all caches atomically."""
    from .registry import set_cli_backend
    invalidate_all_caches()
    set_cli_backend(backend)
```

**Benefit**: Each module registers its own cleanup hook, avoiding tight coupling. New caches can be added without modifying central code.

### 2. Lazy Backend Detection Pattern

The current pattern in `z3_shim.py` and `expressions.py` both lazily load the backend module. Consider a unified lazy loading pattern:

**Current** (z3_shim.py):
```python
_backend_module: Any = None

def __getattr__(name: str) -> Any:
    global _backend_module
    if _backend_module is None:
        backend = get_active_backend()
        if backend == "z3":
            _backend_module = importlib.import_module("z3")
        elif backend == "cvc5":
            _backend_module = importlib.import_module("cvc5.pythonic")
```

**Current** (expressions.py):
```python
def _get_backend_module():
    backend = get_active_backend()
    if backend == "z3":
        import z3
        return z3
    elif backend == "cvc5":
        import cvc5.pythonic as cvc5_pythonic
        return cvc5_pythonic
```

**Issue**: Two separate lazy loading implementations create maintenance burden.

**Suggested Pattern**: Centralize backend module access:

```python
# solver/backend.py
"""Centralized backend module access."""

from functools import lru_cache
from typing import Any
import importlib

_cached_module: Any = None
_cached_backend: str = None

def get_backend_module() -> Any:
    """Get the backend module, caching for performance."""
    global _cached_module, _cached_backend
    from .registry import get_active_backend

    backend = get_active_backend()
    if _cached_module is None or _cached_backend != backend:
        if backend == "z3":
            _cached_module = importlib.import_module("z3")
        else:
            _cached_module = importlib.import_module("cvc5.pythonic")
        _cached_backend = backend
    return _cached_module

def reset_backend_cache() -> None:
    """Reset the cached backend module."""
    global _cached_module, _cached_backend
    _cached_module = None
    _cached_backend = None
```

**Benefit**: Single point of caching, automatic invalidation on backend change detection.

### 3. Early Backend Configuration in BuildExample (Plan Phase 2 - Enhanced)

The plan correctly identifies the need for early backend configuration in `BuildExample.__init__`. An improvement would be to use a context manager pattern:

**Current Plan**:
```python
def __init__(self, ...):
    self._configure_solver_backend(example_case)
    self._initialize_z3_context()
```

**Enhanced Pattern**:
```python
def __init__(self, ...):
    # Extract settings before any z3_shim access
    settings = self._extract_settings(example_case)

    # Configure backend in atomic block
    with backend_context(settings.get("solver")):
        self._initialize_z3_context()
        self._build_model_structure()
```

Where `backend_context` is:
```python
@contextmanager
def backend_context(requested_backend: Optional[str] = None):
    """Context manager for temporary backend override."""
    from .registry import get_active_backend, set_cli_backend, clear_cli_backend
    from .lifecycle import invalidate_all_caches

    if requested_backend is None:
        yield
        return

    original = get_active_backend()
    try:
        invalidate_all_caches()
        set_cli_backend(requested_backend)
        yield
    finally:
        # Restore original if needed (for nested examples)
        if original != requested_backend:
            invalidate_all_caches()
            set_cli_backend(original)
```

**Note**: This pattern may be overkill for the current use case. Only implement if multiple examples with different backends run in the same session.

### 4. Defensive Type Checking (Plan Phase 4 - Simplified)

The plan's optional SMT-LIB fallback is a good defensive measure. A simpler alternative is runtime type assertion:

```python
# solver/type_guards.py
"""Runtime type checking for solver expressions."""

def assert_backend_types(constraint: Any, expected_backend: str) -> None:
    """Assert that constraint was built with expected backend types."""
    import z3
    try:
        import cvc5.pythonic as cvc5
        cvc5_available = True
    except ImportError:
        cvc5_available = False

    if expected_backend == "cvc5":
        if isinstance(constraint, z3.ExprRef):
            raise TypeError(
                f"CVC5 backend received Z3 expression: {type(constraint)}. "
                "This indicates a cache invalidation bug. "
                "Call invalidate_all_caches() before switching backends."
            )
    elif expected_backend == "z3" and cvc5_available:
        if hasattr(cvc5, 'ExprRef') and isinstance(constraint, cvc5.ExprRef):
            raise TypeError(
                f"Z3 backend received CVC5 expression: {type(constraint)}. "
                "This indicates a cache invalidation bug."
            )
```

**Usage in adapters**:
```python
class CVC5SolverAdapter:
    def add(self, constraint: Any) -> None:
        assert_backend_types(constraint, "cvc5")  # Fail fast
        self._solver.add(constraint)
```

**Benefit**: Fails fast with clear error message instead of cryptic CVC5 errors. Lower implementation cost than SMT-LIB interchange.

### 5. Architecture Diagram

The unified architecture with improvements:

```
                    ┌─────────────────────────────────────────────────────────────┐
                    │                    CLI / Settings                           │
                    │                  (solver selection)                         │
                    └────────────────────────┬────────────────────────────────────┘
                                             │
                    ┌────────────────────────┴────────────────────────────────────┐
                    │                 solver/lifecycle.py                         │
                    │           set_backend_with_invalidation()                   │
                    │                                                             │
                    │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │
                    │  │ z3_shim     │  │ atoms       │  │ registry            │  │
                    │  │ reset hook  │  │ reset hook  │  │ reset hook          │  │
                    │  └─────────────┘  └─────────────┘  └─────────────────────┘  │
                    └────────────────────────┬────────────────────────────────────┘
                                             │
                    ┌────────────────────────┴────────────────────────────────────┐
                    │                 solver/backend.py                           │
                    │              get_backend_module()                           │
                    │         (single source of backend module)                   │
                    └────────────────────────┬────────────────────────────────────┘
                                             │
              ┌──────────────────────────────┼──────────────────────────────┐
              │                              │                              │
    ┌─────────┴─────────┐      ┌─────────────┴─────────────┐       ┌────────┴────────┐
    │   expressions.py  │      │        z3_shim.py         │       │    atoms.py     │
    │  And, Or, BitVec  │      │    (migration shim)       │       │   AtomSort      │
    └─────────┬─────────┘      └─────────────┬─────────────┘       └────────┬────────┘
              │                              │                              │
              └──────────────────────────────┼──────────────────────────────┘
                                             │
                    ┌────────────────────────┴────────────────────────────────────┐
                    │               TrackedSolverProtocol                         │
                    │         (solver.add, solver.check, etc.)                    │
                    │                                                             │
                    │  ┌─────────────────────┐  ┌──────────────────────────────┐  │
                    │  │   Z3SolverAdapter   │  │     CVC5SolverAdapter        │  │
                    │  │   (z3.Solver())     │  │   (cvc5.pythonic.Solver())   │  │
                    │  └─────────────────────┘  └──────────────────────────────┘  │
                    └─────────────────────────────────────────────────────────────┘
```

## Recommendations

### Minimal Implementation (Matches Plan)

If the goal is minimal code change with quick fix:

1. **Phase 1**: Add `_invalidate_expression_caches()` to registry.py as planned
2. **Phase 2**: Configure backend early in BuildExample as planned
3. **Phase 3**: Verify with counterfactual examples
4. **Phase 4 (optional)**: Add type assertions for debugging

Estimated effort: 3-4 hours (as planned)

### Enhanced Implementation (Future-Proof)

If the goal is cleaner long-term architecture:

1. **Create solver/lifecycle.py**: Hook-based cache invalidation
2. **Create solver/backend.py**: Single source for backend module
3. **Update z3_shim.py**: Delegate to solver/backend.py
4. **Update expressions.py**: Delegate to solver/backend.py
5. **Add type guards**: Runtime type assertions in adapters
6. **Deprecate z3_shim**: Move fully to solver.expressions

Estimated effort: 6-8 hours

### Recommended Approach

Implement the **minimal approach** (matching the plan) to fix the immediate issue. Then create a follow-up task for the enhanced architecture if:
- Multiple solvers become production requirements
- Additional caches are discovered
- Performance profiling shows module lookup overhead

## Files Affected

### Minimal Implementation
- `code/src/model_checker/solver/registry.py` (~15 lines)
- `code/src/model_checker/builder/example.py` (~10 lines)

### Enhanced Implementation (Future)
- Create: `code/src/model_checker/solver/lifecycle.py` (~30 lines)
- Create: `code/src/model_checker/solver/backend.py` (~40 lines)
- Create: `code/src/model_checker/solver/type_guards.py` (~30 lines)
- Modify: `code/src/model_checker/z3_shim.py` (~5 lines)
- Modify: `code/src/model_checker/solver/expressions.py` (~10 lines)
- Modify: `code/src/model_checker/solver/z3_adapter.py` (~3 lines)
- Modify: `code/src/model_checker/solver/cvc5_adapter.py` (~3 lines)

## Gaps in Current Plan

1. **atoms.py integration**: The plan calls `reset_atom_sort()` but doesn't update atoms.py to register with a lifecycle hook. This is fine for minimal implementation but creates coupling.

2. **Nested backend switching**: The plan doesn't address scenarios where one example runs with z3 and then switches to cvc5 for comparison. The current pattern works but could leak state in edge cases.

3. **Thread safety**: Both z3_shim and atoms use module-level globals. If ModelChecker ever supports parallel execution, these would need locking or thread-local storage.

## Conclusion

The existing plan (02_cache-invalidation-fix.md) correctly identifies the root cause and proposes an appropriate minimal fix. This report confirms the approach and identifies architectural patterns that could improve maintainability in a future refactoring. The recommended path is to implement the minimal fix now and consider the enhanced architecture as a separate task if multi-solver support becomes a first-class requirement.
