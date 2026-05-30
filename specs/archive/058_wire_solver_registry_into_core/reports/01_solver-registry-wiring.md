# Research Report: Task #58

**Task**: 58 - Wire Solver Registry into Core
**Started**: 2026-03-30T00:00:00Z
**Completed**: 2026-03-30T00:45:00Z
**Effort**: Medium-High (significant refactoring across multiple modules)
**Dependencies**: Task 47 (Multi-solver abstraction layer) - COMPLETED
**Sources/Inputs**: Codebase exploration, solver/ module documentation
**Artifacts**: specs/058_wire_solver_registry_into_core/reports/01_solver-registry-wiring.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- Found 181 files with direct z3 imports, but only 15-20 are in the core solving pipeline that needs modification
- The z3_shim.py module is functional but unused - it provides lazy import switching via `__getattr__`
- The solver adapter layer (Z3SolverAdapter, CVC5SolverAdapter) is well-designed and ready for use
- Key bottleneck: structure.py and semantic.py hardcode z3.Solver() and z3-specific result checking
- Recommended approach: Two-phase migration - first expressions.py adoption, then adapter layer integration

## Context & Scope

### Problem Statement

The ModelChecker has a complete solver abstraction layer in `code/src/model_checker/solver/` but it's not actually wired into the core solving pipeline. Specifically:

1. `structure.py` creates `z3.Solver()` directly (lines 156, 232-235)
2. `structure.py` uses `z3.sat` for result comparison (lines 248, 288)
3. `structure.py` uses `z3.is_true()` for model evaluation (lines 885, 902-905)
4. `semantic.py` imports z3 types directly and uses z3.BoolVal (lines 9-22, 303, 313, 323)
5. Many utility modules (bitvector.py, z3_helpers.py) import z3 directly

As a result, calling `switch_solver('cvc5')` has no effect on actual SAT checking.

### Existing Infrastructure

The solver abstraction layer is well-designed:

```
code/src/model_checker/solver/
  __init__.py        # Public API exports
  registry.py        # Backend selection (CLI, env, settings)
  protocols.py       # SolverProtocol, TrackedSolverProtocol
  z3_adapter.py      # Z3 adapter implementing protocols
  cvc5_adapter.py    # cvc5 adapter implementing protocols
  expressions.py     # Expression construction (And, Or, BitVec, etc.)
  compat.py          # Cross-solver helpers (is_true, simplify, etc.)
  types.py           # Type aliases
```

## Findings

### 1. Inventory of Direct z3 Imports

**Core Solving Pipeline (MUST CHANGE):**

| File | Line | Import | Usage |
|------|------|--------|-------|
| `models/structure.py` | 16 | `import z3` (TYPE_CHECKING) | Type hints |
| `models/structure.py` | 156 | `from z3 import Solver` | `Solver()` instantiation |
| `models/structure.py` | 232, 235 | `import z3` | `z3.Solver()` creation |
| `models/structure.py` | 248, 288 | - | `z3.sat` comparison |
| `models/structure.py` | 885 | `import z3` | `z3.is_true()` for model eval |
| `models/semantic.py` | 9-22 | Multiple z3 imports | BitVecVal, And, Not, simplify, etc. |
| `models/semantic.py` | 303, 313, 323 | - | `z3.BoolVal()` in constrained functions |
| `utils/z3_helpers.py` | 9 | `from z3 import ...` | ForAll/Exists implementation |
| `utils/bitvector.py` | 12 | `from z3 import BitVecVal, BitVecRef` | Conversion utilities |
| `utils/context.py` | 32, 59 | `import z3` | Context reset |
| `builder/runner.py` | 15 | `import z3` | Appears unused but imported |
| `iterate/base.py` | 8 | `import z3` | Type hints, ModelRef |

**Theory Library (SHOULD CHANGE):**

| Module | Description |
|--------|-------------|
| `theory_lib/logos/semantic.py` | `from z3 import simplify` + `import z3` |
| `theory_lib/bimodal/semantic.py` | `import z3` |
| `theory_lib/bimodal/operators.py` | `import z3` |
| `theory_lib/logos/subtheories/*/operators.py` | All use `import z3` |

**Syntactic Layer (CAREFUL - AtomSort):**

| File | Line | Import | Issue |
|------|------|--------|-------|
| `syntactic/atoms.py` | 10 | `from z3 import DeclareSort, Const` | Creates global AtomSort |
| `syntactic/collection.py` | 9 | `from z3 import Const` | Uses AtomSort |

### 2. Understanding z3_shim.py

The shim module is correctly implemented but completely unused:

```python
# z3_shim.py
def __getattr__(name: str) -> Any:
    global _backend_module
    if _backend_module is None:
        backend = get_active_backend()
        if backend == "z3":
            _backend_module = importlib.import_module("z3")
        elif backend == "cvc5":
            _backend_module = importlib.import_module("cvc5.pythonic")
    return getattr(_backend_module, name)
```

**Purpose**: Acts as a drop-in replacement for `import z3` that respects the active backend.

**Usage**: Replace `from z3 import X` with `from model_checker.z3_shim import X`

**Limitation**: The shim is "transitional" - the final target is `model_checker.solver.expressions`.

### 3. Adapter Layer Analysis

**Z3SolverAdapter** (`solver/z3_adapter.py`):
- Wraps `z3.Solver()` with protocol-compatible interface
- Provides `assert_tracked()` for unsat core support
- Returns `SolverResult.SAT/UNSAT/UNKNOWN` strings instead of z3 objects
- Already handles model access and timeout configuration

**CVC5SolverAdapter** (`solver/cvc5_adapter.py`):
- Wraps `cvc5.pythonic.Solver()`
- Maps cvc5 API differences (e.g., `tlimit-per` for timeout)
- Provides label-based unsat core even though cvc5 returns terms

**Key Insight**: The adapters return string results (`"sat"`, `"unsat"`, `"unknown"`), not z3/cvc5 objects. Code that does `result == z3.sat` must change to `result == "sat"` or use `SolverResult.is_sat(result)`.

### 4. Expression Construction Analysis

**solver/expressions.py** provides all common z3 functions:
- Boolean: `And`, `Or`, `Not`, `Implies`, `If`, `Bool`, `BoolVal`
- Bitvector: `BitVec`, `BitVecVal`, `Concat`, `Extract`, `LShR`
- Comparisons: `ULT`, `ULE`, `UGT`, `UGE`
- Arithmetic: `Int`, `IntVal`, `Real`, `RealVal`
- Quantifiers: `ForAll`, `Exists`
- Sorts: `BitVecSort`, `BoolSort`, `DeclareSort`
- Arrays: `Array`, `Select`, `Store`
- Utility: `simplify`, `substitute`, `Const`, `Function`

**Implementation**: Each function delegates to `_get_backend_module().{name}(*args)`.

**Issue**: Not all z3 functions are covered. Notably missing:
- `EmptySet`, `SetAdd`, `IsMember` (used in semantic.py)
- `ArrayRef` (used in type hints)
- `is_true`, `is_false` (use compat.py instead)

### 5. Compatibility Layer Analysis

**solver/compat.py** provides:
- `is_true(val, backend)` - Checks boolean true
- `is_false(val, backend)` - Checks boolean false
- `simplify(expr, backend)` - Expression simplification
- `eval_model(model, expr, backend)` - Model evaluation
- `get_bitvec_value(val, backend)` - Extract int from bitvector
- `substitute(expr, substitutions, backend)` - Variable substitution

**Issue**: These require explicit `backend` parameter. For seamless migration, should auto-detect backend.

### 6. Dependency Graph

Migration must respect import order to avoid circular imports:

```
Level 0 (no internal deps):
  solver/protocols.py
  solver/types.py
  solver/registry.py

Level 1 (depends on registry):
  solver/expressions.py
  solver/compat.py
  z3_shim.py

Level 2 (depends on expressions):
  solver/z3_adapter.py
  solver/cvc5_adapter.py
  utils/z3_helpers.py
  utils/bitvector.py

Level 3 (depends on utils):
  syntactic/atoms.py (SPECIAL: creates AtomSort)
  models/semantic.py

Level 4 (depends on semantic):
  models/structure.py
  theory_lib/*/semantic.py
```

### 7. AtomSort Compatibility Challenge

**Critical Issue**: `syntactic/atoms.py` creates a module-level `AtomSort`:

```python
AtomSort = DeclareSort("AtomSort")
```

This is used throughout the syntactic layer. Both z3 and cvc5.pythonic support `DeclareSort`, but:
- The sort object is backend-specific
- Once created with z3, it can't be used with cvc5

**Options**:
1. Lazy initialization (create on first use)
2. Backend-specific sort registry
3. String-based sort lookup

## Decisions

### D1: Use Two-Phase Migration Strategy

**Phase 1**: Replace expression imports with `model_checker.solver.expressions`
- Low risk, mostly mechanical
- Preserves z3.Solver() usage initially
- Allows incremental testing

**Phase 2**: Replace Solver instantiation with `create_solver()`
- Modify structure.py to use adapter interface
- Update result comparison to use SolverResult methods
- Wire in compat.py for model evaluation

### D2: Extend expressions.py Before Migration

Add missing functions to expressions.py:
- `EmptySet`, `SetAdd`, `IsMember` (for semantic.py)
- `ArrayRef` (export type from backend)
- Any other functions discovered during migration

### D3: Handle AtomSort via Lazy Initialization

Modify `syntactic/atoms.py`:

```python
_atom_sort = None

def get_atom_sort():
    global _atom_sort
    if _atom_sort is None:
        from model_checker.solver.expressions import DeclareSort
        _atom_sort = DeclareSort("AtomSort")
    return _atom_sort

AtomSort = property(get_atom_sort)  # or use __getattr__
```

### D4: Update compat.py to Auto-detect Backend

Modify compat helpers to not require explicit backend:

```python
def is_true(val: Any, backend: str = None) -> bool:
    if backend is None:
        from .registry import get_active_backend
        backend = get_active_backend()
    # ... rest unchanged
```

## Recommendations

### Migration Order

1. **First**: Update `solver/expressions.py` to include all missing functions
2. **Second**: Update `solver/compat.py` for auto-detection
3. **Third**: Migrate `utils/z3_helpers.py` and `utils/bitvector.py`
4. **Fourth**: Migrate `syntactic/atoms.py` with lazy AtomSort
5. **Fifth**: Migrate `models/semantic.py` (heavily uses z3 types)
6. **Sixth**: Migrate `models/structure.py` (the main solver integration)
7. **Seventh**: Migrate theory_lib modules
8. **Last**: Migrate test files (can use z3 directly for z3-specific tests)

### Testing Strategy

1. Run full test suite after each file migration
2. Add equivalence tests in `solver/tests/unit/test_equivalence.py`
3. Test with `MODEL_CHECKER_SOLVER=cvc5` environment variable
4. Ensure z3 remains the default and works identically

### Files to Modify (Priority Order)

| Priority | File | Changes |
|----------|------|---------|
| P1 | solver/expressions.py | Add EmptySet, SetAdd, IsMember, ArrayRef |
| P1 | solver/compat.py | Auto-detect backend in all functions |
| P2 | utils/z3_helpers.py | Use expressions.py imports |
| P2 | utils/bitvector.py | Use expressions.py imports |
| P2 | syntactic/atoms.py | Lazy AtomSort initialization |
| P3 | models/semantic.py | Use expressions.py and compat.py |
| P3 | models/structure.py | Use create_solver() and SolverResult |
| P4 | theory_lib/logos/semantic.py | Use expressions.py |
| P4 | theory_lib/bimodal/*.py | Use expressions.py |
| P5 | iterate/base.py | Use solver types |
| P5 | builder/runner.py | Remove unused z3 import |

## Risks & Mitigations

### Risk 1: Circular Import Errors
- **Likelihood**: Medium
- **Impact**: High (breaks entire module)
- **Mitigation**: Follow dependency order strictly, use lazy imports where needed

### Risk 2: Performance Regression
- **Likelihood**: Low
- **Impact**: Medium
- **Mitigation**: The adapter layer is thin; benchmark before/after

### Risk 3: Subtle API Differences
- **Likelihood**: Medium
- **Impact**: Medium (incorrect results)
- **Mitigation**: Extensive equivalence testing between backends

### Risk 4: AtomSort Context Issues
- **Likelihood**: Medium
- **Impact**: High (expressions incompatible)
- **Mitigation**: Reset AtomSort when backend changes; test multi-example runs

### Risk 5: Test File Breakage
- **Likelihood**: High
- **Impact**: Low (tests, not production)
- **Mitigation**: Many tests use z3 directly; update incrementally

## Appendix

### Search Queries Used

```bash
# Find all z3 imports
grep -r "^import z3\|^from z3 import" code/src/model_checker/

# Find Solver instantiation
grep -r "z3.Solver()\|Solver()" code/src/model_checker/models/

# Find result comparison
grep -r "z3.sat\|z3.unsat" code/src/model_checker/
```

### Reference Documentation

- Z3 Python API: https://z3prover.github.io/api/html/namespacez3py.html
- cvc5 Pythonic API: https://cvc5.github.io/docs/cvc5-1.0.0/api/python/pythonic/pythonic.html
- solver/README.md: Internal documentation for abstraction layer

### Files Examined

- code/src/model_checker/z3_shim.py
- code/src/model_checker/solver/__init__.py
- code/src/model_checker/solver/registry.py
- code/src/model_checker/solver/protocols.py
- code/src/model_checker/solver/z3_adapter.py
- code/src/model_checker/solver/cvc5_adapter.py
- code/src/model_checker/solver/expressions.py
- code/src/model_checker/solver/compat.py
- code/src/model_checker/models/structure.py
- code/src/model_checker/models/semantic.py
- code/src/model_checker/utils/z3_helpers.py
- code/src/model_checker/utils/bitvector.py
- code/src/model_checker/utils/context.py
- code/src/model_checker/syntactic/atoms.py
- code/src/model_checker/syntactic/collection.py
- code/src/model_checker/iterate/base.py
- code/src/model_checker/builder/runner.py
- code/src/model_checker/theory_lib/logos/semantic.py
