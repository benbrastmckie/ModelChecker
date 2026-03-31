# Implementation Plan: Task #72 (v3)

- **Task**: 72 - Fix CVC5 constraint compatibility with Z3 expression types
- **Status**: [COMPLETED]
- **Effort**: 4-5 hours
- **Dependencies**: None
- **Research Inputs**: reports/02_team-research.md, reports/03_unified-architecture.md
- **Artifacts**: plans/03_unified-architecture.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: true

## Overview

This plan implements a unified z3/cvc5 architecture based on the findings from reports 02 and 03. Instead of a minimal patch (plan v2), this version creates a clean, maintainable architecture with:

1. **Hook-based lifecycle module**: Decoupled cache invalidation
2. **Centralized backend access**: Single source of truth for backend module
3. **Runtime type guards**: Fail-fast assertions in adapters

### Why This Approach

The research (03_unified-architecture.md) confirmed that cache invalidation is the correct fix but identified architectural debt:
- Two separate lazy loading implementations (z3_shim.py and expressions.py)
- Tight coupling in cache invalidation (registry must know all caches)
- No fail-fast mechanism when Z3 types leak to CVC5

This plan adds ~80 lines to create a foundation for future solver backends (e.g., SMT-LIB file output).

## Goals & Non-Goals

**Goals**:
- Create solver/lifecycle.py for hook-based cache invalidation
- Create solver/backend.py as single source for backend module access
- Add runtime type guards to adapters for debugging
- Invalidate caches when solver backend changes
- Verify CVC5 works with counterfactual examples

**Non-Goals**:
- Full deprecation of z3_shim (future task)
- Thread-safe backend switching (not currently needed)
- SMT-LIB interchange fallback (not needed with proper cache invalidation)

## Architecture

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
                │  │ z3_shim     │  │ atoms       │  │ backend.py          │  │
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
          ┌──────────────────────────────┼──────────────────────────────────┐
          │                              │                                  │
┌─────────┴─────────┐      ┌─────────────┴─────────────┐      ┌────────────┴────────────┐
│   expressions.py  │      │        z3_shim.py         │      │       atoms.py          │
│  And, Or, BitVec  │      │    (migration shim)       │      │      AtomSort           │
└─────────┬─────────┘      └─────────────┬─────────────┘      └────────────┬────────────┘
          │                              │                                  │
          └──────────────────────────────┼──────────────────────────────────┘
                                         │
                ┌────────────────────────┴────────────────────────────────────┐
                │               TrackedSolverProtocol                         │
                │                                                             │
                │  ┌─────────────────────┐  ┌──────────────────────────────┐  │
                │  │   Z3SolverAdapter   │  │     CVC5SolverAdapter        │  │
                │  │  + type guards      │  │     + type guards            │  │
                │  └─────────────────────┘  └──────────────────────────────┘  │
                └─────────────────────────────────────────────────────────────┘
```

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Circular imports with new modules | High | Medium | Careful import ordering, lazy imports |
| Undiscovered caches | Medium | Low | Type guards catch leaked types |
| Import order in existing code | Medium | Low | Test with fresh interpreter |

## Implementation Phases

### Phase 1: Create solver/lifecycle.py [COMPLETED]

**Goal**: Create hook-based cache invalidation system.

**Tasks**:
- [ ] Create `code/src/model_checker/solver/lifecycle.py`
- [ ] Implement `register_cache_hook()` to register cleanup functions
- [ ] Implement `invalidate_all_caches()` to call all hooks
- [ ] Implement `set_backend_with_invalidation()` as single entry point

**Timing**: 30 minutes

**Code**:
```python
"""Backend lifecycle management for clean solver switching."""

from typing import Callable, List

_cache_hooks: List[Callable[[], None]] = []

def register_cache_hook(hook: Callable[[], None]) -> None:
    """Register a function to call when backend changes.

    Modules with cached backend-specific state should register
    their reset function during import.
    """
    if hook not in _cache_hooks:
        _cache_hooks.append(hook)

def invalidate_all_caches() -> None:
    """Invalidate all registered expression caches."""
    for hook in _cache_hooks:
        hook()

def set_backend_with_invalidation(backend: str) -> None:
    """Set backend and invalidate all caches atomically.

    This is the primary entry point for backend switching.
    """
    invalidate_all_caches()
    from .registry import set_cli_backend
    set_cli_backend(backend)
```

**Verification**:
- Unit test: register hook, call invalidate, verify hook executed
- Test: set_backend_with_invalidation clears caches

---

### Phase 2: Create solver/backend.py [COMPLETED]

**Goal**: Single source of truth for backend module access.

**Tasks**:
- [ ] Create `code/src/model_checker/solver/backend.py`
- [ ] Implement `get_backend_module()` with caching
- [ ] Implement `reset_backend_cache()` and register with lifecycle
- [ ] Add type hints and docstrings

**Timing**: 30 minutes

**Code**:
```python
"""Centralized backend module access."""

from typing import Any
import importlib

_cached_module: Any = None
_cached_backend: str = None

def get_backend_module() -> Any:
    """Get the backend module (z3 or cvc5.pythonic), caching for performance."""
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

# Register with lifecycle
from .lifecycle import register_cache_hook
register_cache_hook(reset_backend_cache)
```

**Verification**:
- get_backend_module() returns z3 by default
- After set_backend_with_invalidation("cvc5"), returns cvc5.pythonic

---

### Phase 3: Add Runtime Type Guards [COMPLETED]

**Goal**: Fail-fast assertions in adapters to catch leaked types early.

**Tasks**:
- [ ] Create `code/src/model_checker/solver/type_guards.py`
- [ ] Implement `assert_backend_types()` helper
- [ ] Add type guard calls to CVC5SolverAdapter.add() and similar methods
- [ ] Add type guard calls to Z3SolverAdapter for symmetry

**Timing**: 45 minutes

**Code**:
```python
"""Runtime type checking for solver expressions."""

from typing import Any

def assert_backend_types(constraint: Any, expected_backend: str) -> None:
    """Assert that constraint was built with expected backend types.

    Raises TypeError with clear debugging message if wrong types detected.
    """
    import z3

    if expected_backend == "cvc5":
        if isinstance(constraint, (z3.ExprRef, z3.BoolRef, z3.ArithRef, z3.BitVecRef)):
            raise TypeError(
                f"CVC5 backend received Z3 expression: {type(constraint).__name__}. "
                "This indicates stale cached types. "
                "Call lifecycle.invalidate_all_caches() before switching backends."
            )
    elif expected_backend == "z3":
        # Check for cvc5 types if available
        try:
            import cvc5.pythonic as cvc5
            if hasattr(cvc5, 'ExprRef') and isinstance(constraint, cvc5.ExprRef):
                raise TypeError(
                    f"Z3 backend received CVC5 expression: {type(constraint).__name__}. "
                    "This indicates stale cached types."
                )
        except ImportError:
            pass  # cvc5 not installed
```

**Add to adapters**:
```python
# In cvc5_adapter.py CVC5SolverAdapter.add():
def add(self, constraint: Any) -> None:
    from .type_guards import assert_backend_types
    assert_backend_types(constraint, "cvc5")
    self._solver.add(constraint)
```

**Verification**:
- Type guard raises TypeError when Z3 expression passed to CVC5 adapter
- Type guard passes when correct types used

---

### Phase 4: Wire Up Cache Registrations [COMPLETED]

**Goal**: Register existing caches with lifecycle system.

**Tasks**:
- [ ] Update z3_shim.py to register `_reset_backend` with lifecycle
- [ ] Update syntactic/atoms.py to register `reset_atom_sort` with lifecycle
- [ ] Update registry.py to use lifecycle.set_backend_with_invalidation
- [ ] Remove old manual cache invalidation code

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/z3_shim.py` (~3 lines)
- `code/src/model_checker/syntactic/atoms.py` (~3 lines)
- `code/src/model_checker/solver/registry.py` (~5 lines)

**Code changes**:

z3_shim.py (add at end of file):
```python
# Register cache invalidation with lifecycle
from model_checker.solver.lifecycle import register_cache_hook
register_cache_hook(_reset_backend)
```

atoms.py (add at end of file):
```python
# Register cache invalidation with lifecycle
from model_checker.solver.lifecycle import register_cache_hook
register_cache_hook(reset_atom_sort)
```

registry.py (update set_cli_backend):
```python
def set_cli_backend(backend: str) -> None:
    """Set the solver backend from CLI flag.

    Note: Use lifecycle.set_backend_with_invalidation() for automatic
    cache clearing. This function only sets the backend variable.
    """
    global _cli_override
    if backend not in ("z3", "cvc5"):
        raise ValueError(f"Unknown solver backend: {backend}")
    _cli_override = backend
```

**Verification**:
- Importing z3_shim registers reset hook
- Importing atoms registers reset hook
- Lifecycle.invalidate_all_caches() clears both

---

### Phase 5: Configure Backend Early in Example [COMPLETED]

**Goal**: Ensure backend is set from settings before any expression construction.

**Tasks**:
- [ ] In `BuildExample.__init__`, extract solver setting early
- [ ] Call `lifecycle.set_backend_with_invalidation()` if solver differs
- [ ] This must happen BEFORE `_initialize_z3_context()`

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/builder/example.py` (~15 lines)

**Code**:
```python
def __init__(
    self,
    build_module: 'BuildModule',
    semantic_theory: Dict[str, Any],
    example_case: List[Any],
    theory_name: Optional[str] = None
) -> None:
    # Set backend from settings BEFORE any expression construction
    self._configure_solver_backend(example_case)

    # Initialize Z3 context and store module reference
    self._initialize_z3_context()
    # ... rest unchanged

def _configure_solver_backend(self, example_case: List[Any]) -> None:
    """Configure solver backend from example settings."""
    from model_checker.solver.lifecycle import set_backend_with_invalidation
    from model_checker.solver.registry import get_active_backend

    # example_case is [premises, conclusions, settings]
    if len(example_case) >= 3 and isinstance(example_case[2], dict):
        settings = example_case[2]
        requested_solver = settings.get("solver")
        if requested_solver and requested_solver in ("z3", "cvc5"):
            current = get_active_backend()
            if current != requested_solver:
                set_backend_with_invalidation(requested_solver)
```

**Verification**:
- Example with `settings={"solver": "cvc5"}` uses cvc5.pythonic types
- Example without solver setting uses default (z3)

---

### Phase 6: Verify Core Functionality [COMPLETED]

**Goal**: Run counterfactual examples with CVC5 and verify results.

**Tasks**:
- [ ] Run existing counterfactual examples with `--cvc5` flag
- [ ] Verify results match Z3 (sat/unsat, model values)
- [ ] Test push/pop behavior with CVC5
- [ ] Test that switching solvers mid-session works
- [ ] Run full test suite to verify no regressions

**Timing**: 1 hour

**Verification**:
- All counterfactual examples pass with CVC5
- No TypeError about wrong expression types
- Model values consistent between solvers
- Test suite passes

---

## Testing & Validation

- [ ] Unit tests for lifecycle.py (hook registration, invalidation)
- [ ] Unit tests for backend.py (module caching, reset)
- [ ] Unit tests for type_guards.py (type detection, error messages)
- [ ] Integration test: backend switching clears all caches
- [ ] Integration test: counterfactual examples with CVC5
- [ ] Run `test_solver_comparison.py` with CVC5 enabled
- [ ] Full test suite passes

## Artifacts & Outputs

New files:
- `code/src/model_checker/solver/lifecycle.py` (~30 lines)
- `code/src/model_checker/solver/backend.py` (~35 lines)
- `code/src/model_checker/solver/type_guards.py` (~30 lines)

Modified files:
- `code/src/model_checker/solver/registry.py` (~5 lines)
- `code/src/model_checker/z3_shim.py` (~3 lines)
- `code/src/model_checker/syntactic/atoms.py` (~3 lines)
- `code/src/model_checker/builder/example.py` (~15 lines)

Summary:
- `specs/072_fix_cvc5_constraint_compatibility/summaries/03_unified-architecture-summary.md`

## Rollback/Contingency

If the hook-based architecture causes issues:
1. Remove lifecycle.py and backend.py
2. Revert to plan v2's direct `_invalidate_expression_caches()` approach
3. Type guards can be kept as debugging tool regardless

## Comparison to Previous Plans

| Aspect | Plan v1 | Plan v2 | Plan v3 (This) |
|--------|---------|---------|----------------|
| Root cause | Type incompatibility | Cache invalidation | Cache invalidation |
| Approach | Expression reconstruction | Direct cache clear | Hook-based lifecycle |
| Code changes | ~200+ lines | ~25 lines | ~100 lines |
| Phases | 4 (all required) | 3 + 1 optional | 6 |
| Effort | 6 hours | 3-4 hours | 4-5 hours |
| Maintainability | Low (tight coupling) | Medium | High (decoupled) |
| Debugging | Poor (cryptic errors) | Medium | Good (type guards) |
| Extensibility | None | None | Easy (add hooks) |
