# CVC5 Constraint Compatibility Research Report

## Task Context

When CVC5 is selected as the solver backend, the model-checker fails with:
```
SMTException: True, False or SMT Boolean expression expected.
Received And(...) of type <class 'z3.z3.BoolRef'>
```

The Z3 solver works correctly. This research analyzes the constraint building pipeline and recommends a conversion strategy.

## Analysis Summary

### Root Cause

The constraint building pipeline creates **Z3 expressions** (`z3.BoolRef`, `z3.BitVecRef`, etc.) regardless of which solver backend is selected. When CVC5 is chosen, these Z3 expressions are passed directly to CVC5's solver, which correctly rejects them as incompatible types.

### Constraint Building Pipeline

```
┌─────────────────────────────────────────────────────────────────┐
│                    Current Architecture                         │
└─────────────────────────────────────────────────────────────────┘

1. SEMANTICS LAYER (theory_lib/logos/semantic.py)
   - Creates Z3 Functions via z3_shim:
     - verify: Function(BitVecSort(N), AtomSort, BoolSort)
     - falsify: Function(BitVecSort(N), AtomSort, BoolSort)
   - Uses z3_shim for all expression construction

2. OPERATOR LAYER (theory_lib/logos/subtheories/*/operators.py)
   - Imports `from model_checker import z3_shim as z3`
   - Builds constraints like: `z3.And(...)`, `z3.Or(...)`, etc.
   - These return Z3 types (z3.BoolRef)

3. CONSTRAINT COLLECTION (models/constraints.py)
   - ModelConstraints.frame_constraints
   - ModelConstraints.model_constraints
   - ModelConstraints.premise_constraints
   - ModelConstraints.conclusion_constraints
   - All constraints are Z3 expressions

4. SOLVER ADAPTER (solver/cvc5_adapter.py)
   - CVC5SolverAdapter.add(constraint) receives Z3 BoolRef
   - CVC5SolverAdapter.assert_tracked(constraint, label) receives Z3 BoolRef
   - CVC5 rejects non-CVC5 types
```

### Key Files Analyzed

| File | Role | Issue |
|------|------|-------|
| `z3_shim.py` | Transitional import shim | Returns Z3 or CVC5 module based on backend, but expressions are created at semantics init time |
| `solver/expressions.py` | Expression factories | Correctly delegates to active backend, but not used consistently |
| `theory_lib/logos/semantic.py` | Creates Z3 Functions | Uses z3_shim at class initialization time |
| `theory_lib/logos/subtheories/*/operators.py` | Builds constraint expressions | Uses z3_shim, creates Z3 expressions |
| `models/constraints.py` | Collects all constraints | Stores Z3 expressions |
| `solver/cvc5_adapter.py` | CVC5 interface | Receives Z3 expressions, CVC5 rejects them |

### The z3_shim Architecture Problem

The `z3_shim.py` module uses lazy loading:
```python
def __getattr__(name: str) -> Any:
    if _backend_module is None:
        backend = get_active_backend()
        if backend == "z3":
            _backend_module = importlib.import_module("z3")
        elif backend == "cvc5":
            _backend_module = importlib.import_module("cvc5.pythonic")
    return getattr(_backend_module, name)
```

**Problem**: The semantics class imports and uses z3_shim at initialization. If the backend is set AFTER semantics is created (e.g., in tests or late configuration), the wrong backend module is cached.

More critically, even when backend selection works correctly, **Z3 and CVC5 expressions are not interchangeable**. The cvc5.pythonic API mimics Z3's API but creates distinct CVC5 expression types.

## CVC5 Pythonic API Type Requirements

Based on web research and documentation:

1. **Type Incompatibility**: CVC5's pythonic API creates its own expression types that are structurally similar to Z3 but not the same Python objects.

2. **No Direct Conversion**: There is no built-in conversion from Z3 expressions to CVC5 expressions. The APIs are "compatible" only in the sense that code using Z3 can be ported to CVC5 by changing imports.

3. **Expression Creation**: CVC5 requires expressions created via cvc5.pythonic functions:
   ```python
   from cvc5.pythonic import And, Bool, Solver
   x = Bool('x')  # CVC5 boolean variable
   s = Solver()
   s.add(And(x, Not(x)))  # Must use CVC5's And, not Z3's
   ```

## Recommended Conversion Strategy

### Option A: Expression Reconstruction (Recommended)

Add expression conversion in the CVC5 adapter that recursively reconstructs Z3 expressions as CVC5 expressions.

**Approach**:
```python
# In cvc5_adapter.py
def _convert_z3_to_cvc5(self, z3_expr):
    """Convert a Z3 expression to equivalent CVC5 expression."""
    import z3
    from cvc5 import pythonic as cvc5

    # Handle basic boolean operations
    if z3.is_and(z3_expr):
        args = [self._convert_z3_to_cvc5(arg) for arg in z3_expr.children()]
        return cvc5.And(*args)
    elif z3.is_or(z3_expr):
        args = [self._convert_z3_to_cvc5(arg) for arg in z3_expr.children()]
        return cvc5.Or(*args)
    elif z3.is_not(z3_expr):
        return cvc5.Not(self._convert_z3_to_cvc5(z3_expr.arg(0)))
    # ... handle other operations

    # Handle variables and constants
    elif z3.is_const(z3_expr):
        name = str(z3_expr)
        sort = z3_expr.sort()
        if sort == z3.BoolSort():
            return cvc5.Bool(name)
        elif z3.is_bv_sort(sort):
            return cvc5.BitVec(name, sort.size())
        # ...
```

**Pros**:
- Transparent to rest of codebase
- No changes needed to semantics or operators
- Localized to adapter layer

**Cons**:
- Performance overhead for expression traversal
- Must handle all Z3 expression types
- Function declarations need special handling

### Option B: Consistent Backend Usage from Start

Ensure z3_shim returns correct backend from the start of execution.

**Approach**:
- Set backend before any semantics initialization
- Reset z3_shim cache on backend change
- Use solver/expressions.py instead of z3_shim

**Pros**:
- No conversion needed
- Better performance

**Cons**:
- Requires careful initialization ordering
- May break existing code patterns
- Harder to test with multiple backends

### Option C: SMT-LIB2 Intermediate Format

Convert expressions to SMT-LIB2 string format, then parse with target solver.

**Approach**:
```python
def _convert_via_smtlib(self, z3_expr):
    import z3
    from cvc5 import pythonic as cvc5

    # Convert Z3 to SMT-LIB2
    smtlib_str = z3_expr.sexpr()

    # Parse with CVC5
    return cvc5.parse(smtlib_str)
```

**Pros**:
- Standard interchange format
- Handles complex expressions

**Cons**:
- String parsing overhead
- May not preserve all metadata
- Variable binding complexity

## Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| Incomplete conversion | High - solver errors | Comprehensive test suite |
| Performance degradation | Medium - slower solving | Cache converted expressions |
| Function declaration mismatch | High - semantic errors | Maintain function registry |
| Variable binding differences | Medium - incorrect models | Careful variable tracking |
| Quantifier handling | High - incorrect results | Special case quantifiers |

## Implementation Recommendation

**Recommended: Option A (Expression Reconstruction)** with the following phases:

### Phase 1: Core Boolean Conversion
- Convert And, Or, Not, Implies, BoolVal
- Handle basic boolean constants and variables

### Phase 2: BitVector Conversion
- Convert BitVec, BitVecVal
- Handle bitvector operations (fusion, comparison)

### Phase 3: Function Declarations
- Convert Function declarations
- Handle function applications (verify, falsify)

### Phase 4: Quantifiers
- Convert ForAll, Exists
- Handle bound variables correctly

### Testing Strategy
- Unit tests for each expression type
- Integration tests with existing theory tests
- Comparison tests (Z3 vs CVC5 results)

## Key Code Locations for Implementation

1. **Primary change**: `code/src/model_checker/solver/cvc5_adapter.py`
   - Add `_convert_z3_to_cvc5()` method
   - Call conversion in `add()` and `assert_tracked()`

2. **Supporting changes**:
   - Add expression type detection utilities
   - Add function declaration registry

3. **Test files to update**:
   - `code/src/model_checker/solver/tests/unit/test_equivalence.py`
   - Add CVC5 integration tests

## Conclusion

The CVC5 compatibility issue stems from Z3 expressions being passed to CVC5's solver without conversion. The recommended fix is to add expression reconstruction in the CVC5 adapter, converting Z3 expression trees to equivalent CVC5 expressions. This approach localizes changes to the adapter layer while maintaining compatibility with the existing constraint building pipeline.

## Sources

- [cvc5 Pythonic API Documentation](https://cvc5.github.io/docs/cvc5-1.0.2/api/python/pythonic/pythonic.html)
- [cvc5_pythonic_api GitHub - Z3Py-compatible interface to cvc5](https://github.com/cvc5/cvc5_pythonic_api)
- [SMTMSMT: Gluing Together CVC5 and Z3 Nelson Oppen Style](https://www.philipzucker.com/glue-cvc5-z3/)
- [cvc5 GitHub Issue #11276 - cvc5 vs z3 behavior](https://github.com/cvc5/cvc5/issues/11276)
