# Research Report: Plan Review for Multi-Solver Abstraction Layer

**Task**: 47 - Implement multi-solver abstraction layer for z3, cvc5, and future constraint solvers
**Date**: 2026-03-29
**Focus**: Alternative architectures, type safety improvements, maintainability concerns
**Artifact**: 03_plan-review.md

## Executive Summary

After reviewing the implementation plan and prior research, I identify several opportunities for improvement. The current plan is sound but could benefit from:

1. **Dependency injection** over module-level aliasing for better testability
2. **Protocol-based type safety** instead of `Any` types
3. **Import shim using `__getattr__`** to minimize the 74-file import migration
4. **Critical finding**: cvc5.pythonic explicitly does NOT support unsatisfiable cores, requiring a fallback to cvc5's base API

## Key Findings

### 1. cvc5 Pythonic API Critical Limitation

The official cvc5 documentation explicitly states that the pythonic API does not support:
- **Unsatisfiable cores** (critical for ModelChecker's `print_constraints` diagnostic feature)
- Quantifier instantiation patterns
- Pseudo-boolean counting constraints

This means the implementation plan's Phase 3 (cvc5 adapter) must use the **cvc5 base API** for solver control operations, not the pythonic API. The pythonic API is only suitable for formula construction.

**Impact**: The cvc5 adapter complexity increases significantly. The current plan underestimates this.

### 2. Alternative Architectures

#### 2.1 Dependency Injection Pattern (Recommended Improvement)

Instead of module-level imports that bind at import time, use a solver factory with explicit injection:

```python
# model_checker/solver/factory.py
from typing import Protocol, TYPE_CHECKING

if TYPE_CHECKING:
    from .interface import SolverContext

_current_context: "SolverContext | None" = None

def get_context() -> "SolverContext":
    global _current_context
    if _current_context is None:
        _current_context = create_default_context()
    return _current_context

def set_context(context: "SolverContext") -> None:
    global _current_context
    _current_context = context
```

**Benefits**:
- Tests can inject mock contexts without modifying global state
- Solver selection is explicit at runtime, not import time
- Multiple solver contexts can coexist (useful for comparison testing)

**Trade-off**: Requires passing context through the call chain or using thread-local storage.

#### 2.2 Plugin Architecture with Entry Points

Use Python's `importlib.metadata` entry points for solver discovery:

```python
# pyproject.toml
[project.entry-points."model_checker.solvers"]
z3 = "model_checker.solver.z3_adapter:Z3Backend"
cvc5 = "model_checker.solver.cvc5_adapter:CVC5Backend"
```

**Benefits**:
- New solvers can be added as separate packages
- No code changes required to add new backends
- Standard Python pattern

**Trade-off**: Higher complexity, overkill for 2-3 backends.

#### 2.3 Context Manager for Solver Lifecycle

```python
from contextlib import contextmanager

@contextmanager
def solver_context(backend: str = "z3"):
    ctx = create_context(backend)
    token = _context_var.set(ctx)
    try:
        yield ctx
    finally:
        _context_var.reset(token)
        ctx.cleanup()

# Usage
with solver_context("cvc5") as ctx:
    result = solve_problem(constraints)
```

**Benefits**:
- Clear lifecycle management
- Automatic cleanup
- Explicit scope for solver operations

**Trade-off**: Requires restructuring how ModelDefaults uses solvers.

### 3. Type Safety Improvements

The current plan uses `Any` types for solver-agnostic code. This can be improved using Python's typing features:

#### 3.1 Protocol Classes for Expression Types

```python
from typing import Protocol, TypeVar, runtime_checkable

@runtime_checkable
class BoolExpr(Protocol):
    """Protocol for boolean expressions across solvers."""
    def __and__(self, other: "BoolExpr") -> "BoolExpr": ...
    def __or__(self, other: "BoolExpr") -> "BoolExpr": ...
    def __invert__(self) -> "BoolExpr": ...

@runtime_checkable
class BitVecExpr(Protocol):
    """Protocol for bitvector expressions."""
    def size(self) -> int: ...
    def __add__(self, other: "BitVecExpr") -> "BitVecExpr": ...
    def __sub__(self, other: "BitVecExpr") -> "BitVecExpr": ...

ExprT = TypeVar("ExprT", BoolExpr, BitVecExpr, covariant=True)
```

**Benefits**:
- Static type checkers (mypy, pyright) can verify expression usage
- IDE autocompletion works correctly
- Duck typing is preserved (Z3 and cvc5 objects satisfy protocols without inheritance)

#### 3.2 Generic Solver Interface

```python
from typing import Generic, TypeVar

ExprType = TypeVar("ExprType")
ModelType = TypeVar("ModelType")

class AbstractSolver(Generic[ExprType, ModelType]):
    def add(self, constraint: ExprType) -> None: ...
    def check(self) -> SatResult: ...
    def model(self) -> ModelType: ...

class Z3Solver(AbstractSolver["z3.BoolRef", "z3.ModelRef"]):
    ...

class CVC5Solver(AbstractSolver["cvc5.Term", "cvc5.Model"]):
    ...
```

**Trade-off**: Generics add complexity and may not play well with runtime type checking.

#### 3.3 Pragmatic Recommendation

Use Protocol classes for the solver interface (where method signatures matter) but accept solver-specific types for expressions:

```python
# solver/types.py
from typing import TYPE_CHECKING, Union

if TYPE_CHECKING:
    import z3
    # cvc5 types would go here
    SolverExpr = Union[z3.BoolRef, z3.BitVecRef, z3.ArithRef]
    SolverModel = z3.ModelRef
else:
    # Runtime: any expression object
    SolverExpr = object
    SolverModel = object
```

This provides type checking during development while maintaining runtime flexibility.

### 4. Minimizing Import Migration

The plan identifies 74 files needing import changes. Several strategies can reduce this burden:

#### 4.1 Import Shim Using `__getattr__` (Recommended)

Use PEP 562 module-level `__getattr__` to intercept imports:

```python
# model_checker/z3_shim.py
"""Drop-in replacement for z3 imports during migration."""
import importlib
from model_checker.solver import get_active_backend

_backend_module = None

def __getattr__(name: str):
    global _backend_module
    if _backend_module is None:
        backend = get_active_backend()
        if backend == "z3":
            _backend_module = importlib.import_module("z3")
        elif backend == "cvc5":
            _backend_module = importlib.import_module("cvc5.pythonic")
    return getattr(_backend_module, name)
```

**Migration path**:
1. Create `z3_shim.py` with `__getattr__` handler
2. Global find/replace: `from z3 import` -> `from model_checker.z3_shim import`
3. This is a single regex operation, not 74 manual edits

**Benefits**:
- Single-step migration via regex
- Backend selection happens at first attribute access
- No code changes in theory operators

#### 4.2 Import Hook (Not Recommended)

Python's `sys.meta_path` allows intercepting imports entirely:

```python
class SolverImportFinder:
    def find_module(self, fullname, path=None):
        if fullname == "z3":
            return SolverImportLoader()
```

**Trade-off**: This is too "magical" and can cause subtle issues with other tools (IDEs, type checkers, debuggers).

#### 4.3 Codemod Tool

Use a tool like `libcst` or `rope` to automate import rewriting:

```python
# Using libcst
import libcst as cst

class Z3ImportTransformer(cst.CSTTransformer):
    def leave_ImportFrom(self, original, updated):
        if original.module.value == "z3":
            return updated.with_changes(
                module=cst.Attribute(
                    value=cst.Name("model_checker"),
                    attr=cst.Name("solver"),
                    dot=cst.Dot()
                )
            )
        return updated
```

**Benefits**: Precise AST-level transformation, preserves formatting.

### 5. Testing Strategy Improvements

The current plan mentions "equivalence tests" but lacks detail. A more robust approach:

#### 5.1 Property-Based Testing with Hypothesis

```python
from hypothesis import given, strategies as st

@given(st.integers(min_value=0, max_value=15), st.integers(min_value=0, max_value=15))
def test_bitvec_addition_equivalent(a, b):
    """Verify Z3 and cvc5 produce equivalent results for bitvector addition."""
    z3_result = solve_with_z3(lambda x, y: x + y == a + b)
    cvc5_result = solve_with_cvc5(lambda x, y: x + y == a + b)
    assert z3_result.status == cvc5_result.status
    if z3_result.is_sat:
        assert z3_result.model_value == cvc5_result.model_value
```

#### 5.2 Golden Test Suite

Create a reference set of solved problems with known results:

```
tests/solver_equivalence/
  logos_basic_validity.json    # Expected: sat
  logos_contradiction.json     # Expected: unsat
  bimodal_temporal.json        # Expected: sat
```

Each solver must produce the same sat/unsat result (models may differ structurally).

#### 5.3 Differential Testing

Run both solvers on the same problem and compare results:

```python
def differential_test(constraints):
    z3_result = Z3Solver().solve(constraints)
    cvc5_result = CVC5Solver().solve(constraints)

    # Status must match
    assert z3_result.status == cvc5_result.status

    # If sat, verify model satisfies constraints in BOTH solvers
    if z3_result.is_sat:
        verify_model_in_z3(cvc5_result.model, constraints)
        verify_model_in_cvc5(z3_result.model, constraints)
```

### 6. Prior Art Beyond pySMT

The team research correctly identified pySMT, smt-switch, and pysmtlib as unsuitable. Additional prior art:

#### 6.1 SMT-LIB v2.7 Standard

The SMT-LIB standard provides a common textual format. While pysmtlib's subprocess approach is unsuitable, the standard defines:

- **Core theory**: Boolean operations, equality
- **Bitvector theory**: All BV operations standardized
- **Uninterpreted sorts**: `declare-sort` command (used by AtomSort)

**Relevance**: If a future solver lacks a Python API, SMT-LIB export is the fallback path. The abstraction layer should have a clean point to add SMT-LIB serialization.

#### 6.2 smt-fun (Haskell)

The Haskell ecosystem has `smt-fun` which uses GADTs (Generalized Algebraic Data Types) for type-safe SMT expressions. While not directly applicable to Python, the design principle is relevant: **encode theory constraints in the type system**.

#### 6.3 Z3's Own Approach

Z3's C++ API uses a similar pattern to what we're proposing:
- `context` object manages solver state
- Expression types are parameterized by context
- Solvers are created from contexts

The Python API hides this behind `_main_ctx`. Our abstraction can expose it more explicitly.

### 7. Specific Plan Improvements

Based on the analysis, I recommend these changes to the implementation plan:

#### Phase 1 Additions

- Add `solver/context.py` for solver lifecycle management
- Add `solver/compat.py` for cross-solver compatibility helpers (`is_true`, `is_false`, etc.)
- Define Protocol classes for `SolverInterface` and `ModelInterface`

#### Phase 2 Revisions

- Use `__getattr__` shim approach instead of manual import editing
- Create `z3_shim.py` as transitional module
- Single regex operation: `s/from z3 import/from model_checker.z3_shim import/g`

#### Phase 3 Revisions (Critical)

- Split cvc5 adapter into two components:
  1. **Formula construction**: Use cvc5.pythonic (API-compatible with Z3)
  2. **Solver control**: Use cvc5 base API for `assert_and_track` equivalent, unsat cores, etc.
- Implement manual constraint tracking for unsat core support
- Document feature parity matrix

#### Phase 5 Additions

- Add property-based tests using Hypothesis
- Create golden test suite with expected results
- Add differential testing harness

### 8. Recommended Architecture

Based on all findings, the recommended architecture is:

```
model_checker/solver/
    __init__.py          # Public API: get_solver(), register_backend()
    interface.py         # Protocols: SolverProtocol, ModelProtocol, ExprProtocol
    context.py           # SolverContext: manages solver lifecycle
    registry.py          # Backend detection and selection
    compat.py            # Cross-solver helpers: is_true(), is_false(), eval_model()
    expressions.py       # Re-exports: And, Or, BitVec, etc. from active backend
    z3_adapter.py        # Z3Backend: thin passthrough
    cvc5_adapter.py      # CVC5Backend: pythonic for formulas, base API for solver
    types.py             # Type aliases with TYPE_CHECKING guards

model_checker/z3_shim.py  # Transitional: __getattr__ redirects to solver/expressions
```

**Migration path**:
1. Create solver/ package with Z3 passthrough (behavior-identical)
2. Add z3_shim.py with `__getattr__` handler
3. Global regex replace imports to use z3_shim
4. Add cvc5 adapter (more complex than originally planned due to base API requirement)
5. Gradually migrate z3_shim imports to solver/expressions
6. Remove z3_shim once migration complete

## Conclusions

The current implementation plan is fundamentally sound. The recommended improvements are:

1. **Critical**: Account for cvc5.pythonic's lack of unsat core support by using base API
2. **High value**: Use `__getattr__` shim to minimize import migration effort
3. **Medium value**: Add Protocol-based typing for better static analysis
4. **Medium value**: Enhance testing with property-based and differential approaches
5. **Low priority**: Dependency injection is cleaner but requires more restructuring

The heavy lift is justified because:
- The abstraction layer will be touched every time theory semantics change
- Type safety prevents subtle bugs from solver API differences
- The `__getattr__` shim makes the 74-file migration a single command

## References

- cvc5 Pythonic API documentation: Explicitly lists unsatisfiable cores as unsupported
- PEP 562: Module `__getattr__` and `__dir__`
- SMT-LIB v2.7 standard (2025-07-07): Current standardization for solver interoperability
- Python typing documentation: Protocol classes and TypeVar for generic abstractions
