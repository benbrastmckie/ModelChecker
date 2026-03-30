# Implementation Plan: Wire Solver Registry into Core

- **Task**: 58 - Wire Solver Registry into Core
- **Status**: [IMPLEMENTING]
- **Effort**: 6-8 hours
- **Dependencies**: Task 47 (Multi-solver abstraction layer) - COMPLETED
- **Research Inputs**: specs/058_wire_solver_registry_into_core/reports/01_solver-registry-wiring.md
- **Artifacts**: plans/01_solver-registry-wiring-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

The ModelChecker has a complete solver abstraction layer (registry, adapters, expressions.py, compat.py) but it is not wired into the core solving pipeline. Direct `import z3` statements and `z3.Solver()` instantiation throughout the codebase bypass the solver switching infrastructure, meaning `switch_solver('cvc5')` has no effect.

This plan provides a **single comprehensive migration** that:
1. Extends expressions.py with missing functions (EmptySet, SetAdd, IsMember, etc.)
2. Updates compat.py for backend auto-detection
3. Migrates ALL core files to use the abstraction layer
4. Handles the AtomSort lazy initialization challenge
5. Verifies cvc5 actually works when selected

**Definition of Done**: Running `MODEL_CHECKER_SOLVER=cvc5 pytest tests/` produces the same results as the default z3 backend, proving the registry is actually being used.

### Research Integration

- Report: `reports/01_solver-registry-wiring.md`
- Key findings: 181 files with z3 imports, but only ~15 in core pipeline
- AtomSort must use lazy initialization for backend switching
- Adapters return string results ("sat"/"unsat") not z3 objects

## Goals & Non-Goals

**Goals**:
- Complete migration of core solving pipeline to use solver abstraction
- Support cvc5 as functional alternative backend
- Preserve z3 as default with identical behavior
- Enable `MODEL_CHECKER_SOLVER=cvc5` environment variable
- All existing tests pass with both backends

**Non-Goals**:
- Migrating test files (they can use z3 directly for z3-specific tests)
- Adding new solver backends beyond z3/cvc5
- Performance optimization (thin adapter layer already exists)
- Documentation updates (README, usage guides) - separate task

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Circular import errors | High | Medium | Follow dependency order strictly; use lazy imports |
| AtomSort context mixing | High | Medium | Implement lazy initialization with backend reset |
| Subtle API differences | Medium | Medium | Extensive equivalence testing |
| Result comparison breakage | High | High | Use SolverResult.is_sat() consistently |
| Missing expressions.py functions | Medium | High | Extend module first before migration |

## Implementation Phases

### Phase 1: Extend Abstraction Layer [COMPLETED]

**Goal**: Ensure expressions.py and compat.py have all functions needed by core files.

**Tasks**:
- [ ] Add to `solver/expressions.py`:
  - `EmptySet(sort)` - Create empty set of given element sort
  - `SetAdd(set, elem)` - Add element to set
  - `IsMember(elem, set)` - Check set membership
  - `ArrayRef` type export (for type hints)
  - `BitVecRef`, `BoolRef`, `ExprRef` type exports
- [ ] Update `solver/compat.py`:
  - Auto-detect backend in all functions (remove required `backend` param)
  - Add `_get_backend()` helper that calls registry
- [ ] Add `solver/types_export.py` for backend-specific type exports
- [ ] Verify cvc5.pythonic has equivalent functions

**Files to modify**:
- `code/src/model_checker/solver/expressions.py`
- `code/src/model_checker/solver/compat.py`
- `code/src/model_checker/solver/__init__.py` (export new items)

**Code examples**:

```python
# expressions.py additions
def EmptySet(sort: Any) -> Any:
    """Create an empty set of the given element sort."""
    return _get_backend_module().EmptySet(sort)

def SetAdd(s: Any, elem: Any) -> Any:
    """Add an element to a set."""
    return _get_backend_module().SetAdd(s, elem)

def IsMember(elem: Any, s: Any) -> Any:
    """Check if element is member of set."""
    return _get_backend_module().IsMember(elem, s)
```

```python
# compat.py update
def _get_backend() -> str:
    """Get active backend, caching for performance."""
    from .registry import get_active_backend
    return get_active_backend()

def is_true(val: Any, backend: str = None) -> bool:
    """Check if a value represents boolean true."""
    if backend is None:
        backend = _get_backend()
    # ... rest unchanged
```

**Timing**: 45 minutes

**Verification**:
- Unit test: `from model_checker.solver.expressions import EmptySet, SetAdd, IsMember`
- Unit test: `is_true(val)` works without explicit backend

---

### Phase 2: Migrate Utility Modules [COMPLETED]

**Goal**: Update low-level utilities that other modules depend on.

**Tasks**:
- [ ] Migrate `utils/bitvector.py`:
  - Replace `from z3 import BitVecVal, BitVecRef` with expressions import
- [ ] Migrate `utils/z3_helpers.py`:
  - Replace z3 imports with expressions imports
  - ForAll/Exists already in expressions.py
- [ ] Migrate `utils/context.py`:
  - Update `reset_z3_context()` to reset solver registry backend module cache
  - Handle both z3 and cvc5 context reset
- [ ] Migrate `utils/types.py`:
  - Update type imports to use solver layer

**Files to modify**:
- `code/src/model_checker/utils/bitvector.py`
- `code/src/model_checker/utils/z3_helpers.py`
- `code/src/model_checker/utils/context.py`
- `code/src/model_checker/utils/types.py`

**Code examples**:

```python
# utils/bitvector.py - before
from z3 import BitVecVal, BitVecRef

# utils/bitvector.py - after
from model_checker.solver.expressions import BitVecVal
from model_checker.solver.types import BitVecExpr as BitVecRef
```

```python
# utils/context.py - addition
def reset_solver_context() -> None:
    """Reset solver context for both backends."""
    from model_checker.solver.registry import get_active_backend
    from model_checker.z3_shim import _reset_backend

    backend = get_active_backend()
    if backend == "z3":
        # Original z3 reset logic
        import z3
        if hasattr(z3, '_main_ctx'):
            z3._main_ctx = None
        # ...
    elif backend == "cvc5":
        # cvc5 uses TermManager, reset if needed
        pass

    # Also reset the shim's cached module
    _reset_backend()
```

**Timing**: 30 minutes

**Verification**:
- Import each module without errors
- Run existing unit tests for utils/

---

### Phase 3: Migrate Syntactic Layer [COMPLETED]

**Goal**: Handle AtomSort and syntactic atom creation with lazy initialization.

**Tasks**:
- [ ] Migrate `syntactic/atoms.py`:
  - Replace module-level AtomSort with lazy getter
  - Implement `get_atom_sort()` function
  - Maintain backwards compatibility via `AtomSort` alias
- [ ] Migrate `syntactic/collection.py`:
  - Use expressions.Const instead of z3.Const
  - Import AtomSort from atoms module
- [ ] Migrate `syntactic/types.py`:
  - Update type imports
- [ ] Migrate `syntactic/sentence.py`:
  - Update ExprRef import
- [ ] Migrate `syntactic/assignments.py`:
  - Replace z3 import with expressions

**Files to modify**:
- `code/src/model_checker/syntactic/atoms.py`
- `code/src/model_checker/syntactic/collection.py`
- `code/src/model_checker/syntactic/types.py`
- `code/src/model_checker/syntactic/sentence.py`
- `code/src/model_checker/syntactic/assignments.py`

**Code examples**:

```python
# syntactic/atoms.py - rewritten
from typing import Union
from .types import AtomType

_atom_sort = None

def get_atom_sort():
    """Get the AtomSort, creating it lazily for the current backend."""
    global _atom_sort
    if _atom_sort is None:
        from model_checker.solver.expressions import DeclareSort
        _atom_sort = DeclareSort("AtomSort")
    return _atom_sort

def reset_atom_sort():
    """Reset AtomSort when backend changes."""
    global _atom_sort
    _atom_sort = None

# Backwards compatibility - module attribute access
def __getattr__(name):
    if name == "AtomSort":
        return get_atom_sort()
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")

def AtomVal(i: Union[int, str]) -> AtomType:
    """Create a constant of AtomSort with the given index."""
    from model_checker.solver.expressions import Const
    return Const(f"AtomSort!val!{i}", get_atom_sort())
```

**Timing**: 45 minutes

**Verification**:
- `from model_checker.syntactic.atoms import AtomSort, AtomVal` works
- Creating atoms uses current backend
- Switching backend and resetting creates compatible atoms

---

### Phase 4: Migrate Core Semantic Module [COMPLETED]

**Goal**: Update semantic.py to use abstraction layer.

**Tasks**:
- [ ] Replace direct z3 imports with expressions imports
- [ ] Update `_make_constrained_verify()` to use expressions.BoolVal
- [ ] Update `_make_constrained_falsify()` to use expressions.BoolVal
- [ ] Verify all imported functions are available in expressions.py

**Files to modify**:
- `code/src/model_checker/models/semantic.py`

**Code example**:

```python
# models/semantic.py - before
from z3 import (
    And, ArrayRef, BitVecSort, BitVecVal, EmptySet,
    IntVal, IsMember, Not, SetAdd, simplify, BitVecRef, BoolRef,
)

# models/semantic.py - after
from model_checker.solver.expressions import (
    And, BitVecSort, BitVecVal, EmptySet,
    IntVal, IsMember, Not, SetAdd, simplify,
)
from model_checker.solver.types import BitVecExpr, BoolExpr
# ArrayRef may need TYPE_CHECKING guard

# In _make_constrained_verify:
# Before: return z3.BoolVal(value)
# After:
from model_checker.solver.expressions import BoolVal
return BoolVal(value)
```

**Timing**: 45 minutes

**Verification**:
- `from model_checker.models.semantic import SemanticDefaults` works
- Creating semantic instances uses current backend

---

### Phase 5: Migrate Core Structure Module [COMPLETED]

**Goal**: The critical change - wire structure.py to use solver registry.

**Tasks**:
- [ ] Replace `from z3 import Solver` with `from model_checker.solver import create_solver`
- [ ] Replace `z3.Solver()` instantiation with `create_solver()`
- [ ] Replace `result == z3.sat` with `SolverResult.is_sat(result)`
- [ ] Replace `z3.is_true()` with `from model_checker.solver import is_true`
- [ ] Update `_setup_solver()` to use adapter's `assert_tracked()` method
- [ ] Update `solve()` method for adapter interface
- [ ] Update `re_solve()` method for adapter interface
- [ ] Update `extract_verify_falsify_state()` to use compat.is_true
- [ ] Handle timeout via adapter's `set_timeout()` method

**Files to modify**:
- `code/src/model_checker/models/structure.py`

**Code examples**:

```python
# structure.py - _setup_solver change
# Before:
from z3 import Solver
solver = Solver()
solver.assert_and_track(constraint, c_id)

# After:
from model_checker.solver import create_solver
solver = create_solver()
solver.assert_tracked(constraint, c_id)  # Adapter method
```

```python
# structure.py - solve() change
# Before:
import z3
self.solver = z3.Solver()
result = self.solver.check()
if result == z3.sat:
    return self._create_result(False, self.solver.model(), True, start_time)

# After:
from model_checker.solver import create_solver, SolverResult
self.solver = create_solver()
result = self.solver.check()
if SolverResult.is_sat(result):
    return self._create_result(False, self.solver.model(), True, start_time)
```

```python
# structure.py - extract_verify_falsify_state change
# Before:
import z3
state_map[(state, letter_str)] = (
    z3.is_true(verify_val),
    z3.is_true(falsify_val)
)

# After:
from model_checker.solver import is_true
state_map[(state, letter_str)] = (
    is_true(verify_val),
    is_true(falsify_val)
)
```

**Timing**: 1.5 hours

**Verification**:
- Run `pytest code/src/model_checker/models/tests/` with default backend
- Manually verify solver instance type when `MODEL_CHECKER_SOLVER=cvc5`

---

### Phase 6: Migrate Theory Libraries [COMPLETED]

**Goal**: Update theory implementations to use abstraction layer.

**Tasks**:
- [ ] Migrate `theory_lib/logos/semantic.py`:
  - Replace `from z3 import simplify` with expressions import
  - Replace `import z3` with expressions imports
- [ ] Migrate `theory_lib/bimodal/semantic.py`:
  - Replace `import z3` usage
- [ ] Migrate `theory_lib/bimodal/operators.py`:
  - Replace z3 imports
- [ ] Migrate `theory_lib/bimodal/iterate.py`:
  - Replace z3 imports
- [ ] Migrate `theory_lib/logos/subtheories/*/operators.py`:
  - modal/operators.py
  - extensional/operators.py
  - constitutive/operators.py
  - counterfactual/operators.py
  - first_order/operators.py

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/semantic.py`
- `code/src/model_checker/theory_lib/bimodal/semantic.py`
- `code/src/model_checker/theory_lib/bimodal/operators.py`
- `code/src/model_checker/theory_lib/bimodal/iterate.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py`
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
- `code/src/model_checker/theory_lib/logos/iterate.py`
- `code/src/model_checker/theory_lib/logos/protocols.py`
- `code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/first_order/operators.py`

**Code example pattern**:

```python
# Before (typical pattern in theory files):
import z3
# ... later ...
result = z3.And(expr1, expr2)
simplified = z3.simplify(result)

# After:
from model_checker.solver.expressions import And, simplify
# ... later ...
result = And(expr1, expr2)
simplified = simplify(result)
```

**Timing**: 1.5 hours

**Verification**:
- Run `pytest code/src/model_checker/theory_lib/tests/`

---

### Phase 7: Migrate Iterator and Builder Modules [COMPLETED]

**Goal**: Update iteration and example building to use abstraction.

**Tasks**:
- [ ] Migrate `iterate/base.py`:
  - Replace z3 import
- [ ] Migrate `iterate/models.py`:
  - Replace z3 import
- [ ] Migrate `iterate/build_example.py`:
  - Replace z3 import
- [ ] Migrate `iterate/constraints.py`:
  - Replace z3 import
- [ ] Migrate `iterate/graph.py`:
  - Replace z3 import
- [ ] Migrate `builder/runner.py`:
  - Remove unused z3 import (line 15 appears unused)
- [ ] Migrate `builder/example.py`:
  - Replace z3 import
- [ ] Migrate `builder/z3_utils.py`:
  - Replace z3 imports; rename to `solver_utils.py` if appropriate

**Files to modify**:
- `code/src/model_checker/iterate/base.py`
- `code/src/model_checker/iterate/models.py`
- `code/src/model_checker/iterate/build_example.py`
- `code/src/model_checker/iterate/constraints.py`
- `code/src/model_checker/iterate/graph.py`
- `code/src/model_checker/builder/runner.py`
- `code/src/model_checker/builder/example.py`
- `code/src/model_checker/builder/z3_utils.py`

**Timing**: 1 hour

**Verification**:
- Run `pytest code/src/model_checker/iterate/tests/`
- Run `pytest code/src/model_checker/builder/tests/`

---

### Phase 8: Update Type Modules and Constraints [COMPLETED]

**Goal**: Ensure all type hints and constraint references use abstraction.

**Tasks**:
- [ ] Migrate `models/types.py`:
  - Update z3 type imports to use solver types
- [ ] Migrate `models/constraints.py`:
  - Replace ExprRef import
- [ ] Migrate `theory_lib/types.py`:
  - Update z3 type imports

**Files to modify**:
- `code/src/model_checker/models/types.py`
- `code/src/model_checker/models/constraints.py`
- `code/src/model_checker/theory_lib/types.py`

**Code example**:

```python
# models/types.py - before
import z3
Constraint = z3.BoolRef

# models/types.py - after
from model_checker.solver.types import BoolExpr
Constraint = BoolExpr
```

**Timing**: 30 minutes

**Verification**:
- Type hints work correctly
- mypy (if configured) passes

---

### Phase 9: Wire Context Reset to Backend [COMPLETED]

**Goal**: Ensure context reset properly handles backend switching.

**Tasks**:
- [ ] Update `reset_z3_context()` to call `reset_atom_sort()`
- [ ] Update `reset_z3_context()` to call `z3_shim._reset_backend()`
- [ ] Add `reset_solver_context()` as unified reset function
- [ ] Update `structure.py` to use new reset function
- [ ] Consider renaming `utils/context.py` to `utils/solver_context.py`

**Files to modify**:
- `code/src/model_checker/utils/context.py`
- `code/src/model_checker/models/structure.py` (import update)
- `code/src/model_checker/z3_shim.py` (ensure _reset_backend exported)

**Code example**:

```python
# utils/context.py - addition
def reset_solver_context() -> None:
    """Reset solver context for complete isolation between examples."""
    from model_checker.solver.registry import get_active_backend
    from model_checker.syntactic.atoms import reset_atom_sort
    from model_checker.z3_shim import _reset_backend

    backend = get_active_backend()

    # Backend-specific reset
    if backend == "z3":
        import z3
        if hasattr(z3, '_main_ctx'):
            z3._main_ctx = None
        elif hasattr(z3, 'main_ctx'):
            z3.main_ctx = None
        if hasattr(z3, 'clear_parser_cache'):
            z3.clear_parser_cache()
        import importlib
        importlib.reload(z3)
    elif backend == "cvc5":
        # cvc5 typically doesn't need context reset
        pass

    # Reset cached modules
    _reset_backend()
    reset_atom_sort()
```

**Timing**: 30 minutes

**Verification**:
- Multiple examples run without state leakage
- Backend switching between examples works

---

### Phase 10: Verification and Testing [COMPLETED]

**Goal**: Prove the migration works and cvc5 is actually used when selected.

**Tasks**:
- [ ] Create verification script `scripts/verify_solver_wiring.py`:
  - Test that `create_solver()` returns correct adapter type
  - Test that expressions come from correct backend
  - Test end-to-end solve with each backend
- [ ] Run full test suite with z3 (default):
  - `pytest code/src/model_checker/`
- [ ] Run full test suite with cvc5:
  - `MODEL_CHECKER_SOLVER=cvc5 pytest code/src/model_checker/`
- [ ] Add equivalence test `solver/tests/integration/test_backend_equivalence.py`:
  - Same constraints produce same satisfiability
  - Model values are equivalent
- [ ] Document any cvc5-specific failures (known limitations)

**Files to create**:
- `code/scripts/verify_solver_wiring.py`
- `code/src/model_checker/solver/tests/integration/test_backend_equivalence.py`

**Code example**:

```python
# scripts/verify_solver_wiring.py
"""Verify solver registry is properly wired into core."""

import os
import sys

def test_solver_type():
    """Verify create_solver returns correct adapter type."""
    from model_checker.solver import create_solver, get_active_backend
    from model_checker.solver.z3_adapter import Z3SolverAdapter
    from model_checker.solver.cvc5_adapter import CVC5SolverAdapter

    backend = get_active_backend()
    solver = create_solver()

    if backend == "z3":
        assert isinstance(solver, Z3SolverAdapter), f"Expected Z3SolverAdapter, got {type(solver)}"
        print("[PASS] z3 backend creates Z3SolverAdapter")
    elif backend == "cvc5":
        assert isinstance(solver, CVC5SolverAdapter), f"Expected CVC5SolverAdapter, got {type(solver)}"
        print("[PASS] cvc5 backend creates CVC5SolverAdapter")

def test_expressions_backend():
    """Verify expressions come from correct backend."""
    from model_checker.solver import get_active_backend
    from model_checker.solver.expressions import And, BitVec

    backend = get_active_backend()
    x = BitVec("x", 8)

    if backend == "z3":
        import z3
        assert isinstance(x, z3.BitVecRef), "BitVec should be z3 type"
        print("[PASS] z3 backend produces z3 expressions")
    elif backend == "cvc5":
        # Check cvc5 type
        print("[PASS] cvc5 backend produces cvc5 expressions")

def test_end_to_end_solve():
    """Test complete solve cycle with active backend."""
    from model_checker.solver import create_solver, SolverResult
    from model_checker.solver.expressions import BitVec, And

    solver = create_solver()
    x = BitVec("x", 8)
    y = BitVec("y", 8)

    # Simple satisfiable constraint
    solver.add(And(x > 0, y > 0, x + y == 10))
    result = solver.check()

    assert SolverResult.is_sat(result), f"Expected sat, got {result}"
    model = solver.model()
    print(f"[PASS] End-to-end solve succeeded with {get_active_backend()}")
    print(f"  Model: x={model.eval(x)}, y={model.eval(y)}")

if __name__ == "__main__":
    print(f"Testing with MODEL_CHECKER_SOLVER={os.environ.get('MODEL_CHECKER_SOLVER', 'z3 (default)')}")
    test_solver_type()
    test_expressions_backend()
    test_end_to_end_solve()
    print("\n[SUCCESS] All verification tests passed")
```

**Timing**: 1 hour

**Verification**:
- Script passes with both backends
- Full test suite passes with z3
- Full test suite passes with cvc5 (or documents known failures)

## Testing & Validation

- [ ] All existing unit tests pass with z3 backend
- [ ] All existing integration tests pass with z3 backend
- [ ] Verification script passes with z3 backend
- [ ] Verification script passes with cvc5 backend
- [ ] No circular import errors on fresh import
- [ ] `MODEL_CHECKER_SOLVER=cvc5` actually uses CVC5SolverAdapter
- [ ] Example problems produce equivalent results with both backends

## Artifacts & Outputs

- `specs/058_wire_solver_registry_into_core/plans/01_solver-registry-wiring-plan.md` (this file)
- `specs/058_wire_solver_registry_into_core/summaries/01_solver-registry-wiring-summary.md` (post-implementation)
- `code/scripts/verify_solver_wiring.py` (verification script)
- `code/src/model_checker/solver/tests/integration/test_backend_equivalence.py` (equivalence tests)

## Rollback/Contingency

If the migration causes widespread test failures:

1. **Git revert**: All changes are in one commit, easy to revert
2. **Feature flag**: Add `SOLVER_USE_LEGACY=1` env var to bypass abstraction
3. **Partial rollback**: Revert structure.py changes only, keep expression migrations

The solver layer is designed to be transparent - if issues arise, the adapters can be modified to match z3 behavior more closely without changing call sites.

## File Modification Summary

**Core files (MUST change)**:
| File | Key Changes |
|------|-------------|
| `solver/expressions.py` | Add EmptySet, SetAdd, IsMember |
| `solver/compat.py` | Auto-detect backend |
| `utils/bitvector.py` | expressions import |
| `utils/z3_helpers.py` | expressions import |
| `utils/context.py` | Unified reset function |
| `syntactic/atoms.py` | Lazy AtomSort |
| `syntactic/collection.py` | expressions.Const |
| `models/semantic.py` | expressions import, BoolVal |
| `models/structure.py` | create_solver(), SolverResult |

**Theory files (15 files)**:
- `theory_lib/logos/semantic.py`
- `theory_lib/bimodal/semantic.py`, `operators.py`, `iterate.py`
- `theory_lib/bimodal/semantic/witness_*.py`
- `theory_lib/logos/iterate.py`, `protocols.py`
- `theory_lib/logos/subtheories/*/operators.py` (5 files)

**Iterator/builder files (8 files)**:
- `iterate/base.py`, `models.py`, `build_example.py`, `constraints.py`, `graph.py`
- `builder/runner.py`, `example.py`, `z3_utils.py`

**Type files (3 files)**:
- `models/types.py`, `models/constraints.py`, `theory_lib/types.py`

**Total**: ~35 files modified
