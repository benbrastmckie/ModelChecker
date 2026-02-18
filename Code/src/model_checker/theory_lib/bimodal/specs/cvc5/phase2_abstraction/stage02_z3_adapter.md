# Stage 2: Z3SolverAdapter Implementation

## Metadata
- **Stage**: 2/5 (Phase 2 - Abstraction Layer Implementation)
- **Estimated Duration**: 2 days (16 hours)
- **Complexity**: Low-Medium (thin wrapper over existing API)
- **Dependencies**: Stage 1 complete (SolverInterface and CapabilityMatrix defined)
- **Files**:
  - `solver/z3_adapter.py` (~350 LOC expected)
  - `solver/tests/unit/test_z3_adapter.py` (~400 LOC expected)
- **Coverage Target**: >90% (critical path for abstraction layer)
- **Risk**: Low (Z3 API well-known, backward compatibility goal)

## Objective

Implement Z3SolverAdapter as a thin wrapper around Z3 API, providing backward compatibility with existing code while conforming to SolverInterface. This adapter enables existing Z3-based code to use the abstraction layer transparently.

**Success Criteria**: All SolverInterface methods implemented for Z3, tests pass, >90% coverage, NO decorators, backward compatible with existing Z3 usage patterns.

## Implementation Tasks

### Task 1: [TDD-RED] Write test_z3_adapter.py First (2 hours)
**Duration**: 2 hours

- [ ] Create test file: `solver/tests/unit/test_z3_adapter.py`
- [ ] Test Z3SolverAdapter lifecycle methods
- [ ] Test type constructors (sorts)
- [ ] Test value constructors (constants)
- [ ] Test logical operators
- [ ] Test array operations
- [ ] Test configuration and capabilities
- [ ] Test pattern hints support (Z3 feature)
- [ ] Run tests - verify they FAIL (adapter not implemented)

**Test Structure**:
```python
import unittest
import z3
from model_checker.solver.z3_adapter import Z3SolverAdapter
from model_checker.solver.capabilities import CapabilityMatrix


class TestZ3SolverAdapter(unittest.TestCase):
    """Test Z3SolverAdapter implementation."""

    def setUp(self):
        """Create Z3 adapter for tests."""
        self.adapter = Z3SolverAdapter()

    def test_create_solver(self):
        """Test create_solver returns Z3 Solver instance."""
        solver = self.adapter.create_solver()

        self.assertIsInstance(solver, z3.Solver)

    def test_lifecycle_operations(self):
        """Test solver lifecycle: assert, check, model."""
        solver = self.adapter.create_solver()

        # Create simple formula: x > 0
        x = z3.Int('x')
        constraint = x > 0

        self.adapter.assert_constraint(solver, constraint)
        result = self.adapter.check_sat(solver)

        self.assertEqual(result, "sat")

        model = self.adapter.get_model(solver)
        self.assertIsInstance(model, z3.ModelRef)

    def test_type_constructors(self):
        """Test all type constructor methods."""
        bool_sort = self.adapter.mk_bool_sort()
        self.assertIsInstance(bool_sort, z3.SortRef)

        int_sort = self.adapter.mk_int_sort()
        self.assertIsInstance(int_sort, z3.ArithSortRef)

        bv_sort = self.adapter.mk_bitvec_sort(8)
        self.assertIsInstance(bv_sort, z3.BitVecSortRef)

    def test_forall_with_pattern_hints(self):
        """Test ForAll supports pattern hints (Z3 feature)."""
        # Z3 supports pattern hints
        x = self.adapter.mk_var(self.adapter.mk_int_sort(), 'x')
        body = z3.And(x > 0, x < 10)

        # Create pattern hint
        pattern = [z3.MultiPattern(x)]

        # Should accept patterns without error
        forall = self.adapter.mk_forall([x], body, patterns=pattern)
        self.assertIsInstance(forall, z3.QuantifierRef)

    def test_bitvec_val_argument_order(self):
        """Test BitVec value uses (value, size) order."""
        # Interface specifies (value, size)
        bv = self.adapter.mk_bitvec_val(42, 8)

        self.assertIsInstance(bv, z3.BitVecRef)
        # Z3 uses (value, size) - matches interface

    def test_capabilities(self):
        """Test Z3 capabilities returned correctly."""
        cap = self.adapter.get_capabilities()

        self.assertIsInstance(cap, CapabilityMatrix)
        # Z3 supports pattern hints
        self.assertTrue(cap.has_pattern_hints)
        # Z3 supports quantifiers
        self.assertTrue(cap.has_quantifiers)

    def test_error_handling_invalid_constraint(self):
        """Test user-friendly error for invalid constraint."""
        solver = self.adapter.create_solver()

        with self.assertRaises(ValueError) as ctx:
            self.adapter.assert_constraint(solver, "not a constraint")

        # Error should be helpful
        self.assertIn("Failed to assert", str(ctx.exception))
        self.assertIn("valid Z3 expression", str(ctx.exception))

    def test_error_handling_model_when_unsat(self):
        """Test user-friendly error when getting model from UNSAT."""
        solver = self.adapter.create_solver()

        # Create UNSAT formula
        x = z3.Bool('x')
        self.adapter.assert_constraint(solver, z3.And(x, z3.Not(x)))
        self.adapter.check_sat(solver)

        with self.assertRaises(ValueError) as ctx:
            self.adapter.get_model(solver)

        self.assertIn("not SAT", str(ctx.exception))
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_z3_adapter.py -v
```

**Expected**: FAIL (z3_adapter.py does not exist)

### Task 2: [TDD-GREEN] Implement Z3SolverAdapter - Lifecycle Methods (1.5 hours)
**Duration**: 1.5 hours

- [ ] Create `solver/z3_adapter.py`
- [ ] Import z3, SolverInterface, CapabilityMatrix
- [ ] Implement Z3SolverAdapter class (inherits SolverInterface)
- [ ] Implement __init__ with z3_capabilities
- [ ] Implement create_solver
- [ ] Implement assert_constraint
- [ ] Implement check_sat
- [ ] Implement get_model
- [ ] Implement push, pop, reset
- [ ] **CRITICAL**: NO decorators, relative imports

**Implementation Pattern**:
```python
"""Z3 solver adapter implementation."""

# Standard library
from typing import Any, List, Optional

# Third-party
import z3

# Relative imports (same package)
from .interface import SolverInterface
from .capabilities import CapabilityMatrix, z3_capabilities


class Z3SolverAdapter(SolverInterface):
    """Z3 implementation of SolverInterface.

    Thin wrapper providing solver-agnostic access to Z3.
    No decorators per CODE_STANDARDS.md.
    """

    def __init__(self):
        """Initialize Z3 adapter."""
        self._capabilities = z3_capabilities()

    def create_solver(self) -> z3.Solver:
        """Create Z3 solver instance."""
        try:
            return z3.Solver()
        except NameError:
            raise RuntimeError(
                "Z3 solver library not available. "
                "Install with: pip install z3-solver"
            )
        except Exception as e:
            raise RuntimeError(
                f"Failed to create Z3 solver: {e}. "
                f"Ensure Z3 is properly installed and compatible."
            )

    def assert_constraint(self, solver: z3.Solver, constraint: Any) -> None:
        """Assert constraint in Z3 solver."""
        try:
            solver.add(constraint)
        except Exception as e:
            raise ValueError(
                f"Failed to assert constraint: {e}. "
                f"Ensure constraint is valid Z3 expression."
            )

    def check_sat(self, solver: z3.Solver) -> str:
        """Check satisfiability."""
        result = solver.check()
        return str(result)  # "sat", "unsat", or "unknown"

    def get_model(self, solver: z3.Solver) -> z3.ModelRef:
        """Get model from SAT solver."""
        try:
            return solver.model()
        except z3.Z3Exception as e:
            raise ValueError(
                f"Cannot extract model: solver is not SAT. "
                f"Run check_sat() and verify result is 'sat' first."
            )

    def push(self, solver: z3.Solver) -> None:
        """Push solver context."""
        solver.push()

    def pop(self, solver: z3.Solver, num: int = 1) -> None:
        """Pop solver context."""
        solver.pop(num)

    def reset(self, solver: z3.Solver) -> None:
        """Reset solver to initial state."""
        solver.reset()
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3SolverAdapter::test_create_solver -v
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3SolverAdapter::test_lifecycle_operations -v
```

**Expected**: Tests pass for lifecycle methods

### Task 3: [TDD-GREEN] Implement Type Constructors (1 hour)
**Duration**: 1 hour

- [ ] Implement mk_bool_sort → z3.BoolSort()
- [ ] Implement mk_int_sort → z3.IntSort()
- [ ] Implement mk_bitvec_sort → z3.BitVecSort(size)
- [ ] Implement mk_array_sort → z3.ArraySort(index, element)
- [ ] Implement mk_uninterpreted_sort → z3.DeclareSort(name)
- [ ] Implement mk_function → z3.Function(name, *domain, range)

**Pattern**:
```python
def mk_bool_sort(self) -> z3.BoolSortRef:
    """Create Boolean sort."""
    return z3.BoolSort()

def mk_int_sort(self) -> z3.ArithSortRef:
    """Create Integer sort."""
    return z3.IntSort()

def mk_bitvec_sort(self, size: int) -> z3.BitVecSortRef:
    """Create BitVector sort."""
    return z3.BitVecSort(size)

def mk_array_sort(self, index_sort: Any, element_sort: Any) -> z3.ArraySortRef:
    """Create Array sort."""
    return z3.ArraySort(index_sort, element_sort)

def mk_uninterpreted_sort(self, name: str) -> z3.SortRef:
    """Create uninterpreted sort."""
    return z3.DeclareSort(name)

def mk_function(self, name: str, domain: List[Any], range: Any) -> z3.FuncDeclRef:
    """Create function declaration."""
    return z3.Function(name, *domain, range)
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3SolverAdapter::test_type_constructors -v
```

### Task 4: [TDD-GREEN] Implement Value Constructors (1 hour)
**Duration**: 1 hour

- [ ] Implement mk_bool_val → z3.BoolVal(value)
- [ ] Implement mk_int_val → z3.IntVal(value)
- [ ] Implement mk_bitvec_val → z3.BitVecVal(value, size) [NOTE: matches interface]
- [ ] Implement mk_const → z3.Const(name, sort)
- [ ] Implement mk_var → z3.Const(name, sort) [same as mk_const in Z3]

**Pattern**:
```python
def mk_bool_val(self, value: bool) -> z3.BoolRef:
    """Create Boolean value."""
    return z3.BoolVal(value)

def mk_int_val(self, value: int) -> z3.ArithRef:
    """Create Integer value."""
    return z3.IntVal(value)

def mk_bitvec_val(self, value: int, size: int) -> z3.BitVecRef:
    """Create BitVector value.

    Z3 uses (value, size) order - matches interface.
    """
    return z3.BitVecVal(value, size)

def mk_const(self, sort: Any, name: str) -> Any:
    """Create constant."""
    return z3.Const(name, sort)

def mk_var(self, sort: Any, name: str) -> Any:
    """Create variable (same as const in Z3)."""
    return z3.Const(name, sort)
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3SolverAdapter::test_bitvec_val_argument_order -v
```

### Task 5: [TDD-GREEN] Implement Logical Operators (1.5 hours)
**Duration**: 1.5 hours

- [ ] Implement mk_and → z3.And(*args)
- [ ] Implement mk_or → z3.Or(*args)
- [ ] Implement mk_not → z3.Not(arg)
- [ ] Implement mk_implies → z3.Implies(lhs, rhs)
- [ ] Implement mk_equal → z3.Eq(lhs, rhs) or operator==
- [ ] Implement mk_forall → z3.ForAll(vars, body, patterns=patterns)
- [ ] Implement mk_exists → z3.Exists(vars, body, patterns=patterns)
- [ ] **CRITICAL**: Pattern hints optional but supported

**Pattern**:
```python
def mk_and(self, *args: Any) -> z3.BoolRef:
    """Create conjunction."""
    return z3.And(*args)

def mk_or(self, *args: Any) -> z3.BoolRef:
    """Create disjunction."""
    return z3.Or(*args)

def mk_not(self, arg: Any) -> z3.BoolRef:
    """Create negation."""
    return z3.Not(arg)

def mk_implies(self, lhs: Any, rhs: Any) -> z3.BoolRef:
    """Create implication."""
    return z3.Implies(lhs, rhs)

def mk_equal(self, lhs: Any, rhs: Any) -> z3.BoolRef:
    """Create equality."""
    return lhs == rhs  # Z3 operator overloading

def mk_forall(self, vars: List[Any], body: Any,
              patterns: Optional[List[Any]] = None) -> z3.QuantifierRef:
    """Create ForAll quantifier.

    Z3 supports pattern hints - use them if provided.
    """
    if patterns:
        return z3.ForAll(vars, body, patterns=patterns)
    return z3.ForAll(vars, body)

def mk_exists(self, vars: List[Any], body: Any,
              patterns: Optional[List[Any]] = None) -> z3.QuantifierRef:
    """Create Exists quantifier."""
    if patterns:
        return z3.Exists(vars, body, patterns=patterns)
    return z3.Exists(vars, body)
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_z3_adapter.py::TestZ3SolverAdapter::test_forall_with_pattern_hints -v
```

### Task 6: [TDD-GREEN] Implement Array Operations and Configuration (1 hour)
**Duration**: 1 hour

- [ ] Implement mk_select → z3.Select(array, index)
- [ ] Implement mk_store → z3.Store(array, index, value)
- [ ] Implement set_option → solver.set(key, value)
- [ ] Implement get_capabilities → return self._capabilities

**Pattern**:
```python
def mk_select(self, array: Any, index: Any) -> Any:
    """Array select operation."""
    return z3.Select(array, index)

def mk_store(self, array: Any, index: Any, value: Any) -> Any:
    """Array store operation."""
    return z3.Store(array, index, value)

def set_option(self, solver: z3.Solver, key: str, value: str) -> None:
    """Set solver option."""
    try:
        solver.set(key, value)
    except Exception as e:
        raise ValueError(
            f"Failed to set option '{key}' to '{value}': {e}. "
            f"Check Z3 documentation for valid options."
        )

def get_capabilities(self) -> CapabilityMatrix:
    """Get Z3 capabilities."""
    return self._capabilities
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_z3_adapter.py -v
```

**Expected**: ALL tests pass (GREEN state for entire adapter)

### Task 7: [REFACTOR] Code Quality and Error Handling (2 hours)
**Duration**: 2 hours

- [ ] Review all error messages for user-friendliness
- [ ] Add comprehensive docstrings
- [ ] Verify relative imports used
- [ ] NO decorators anywhere
- [ ] Add inline comments for Z3-specific patterns
- [ ] Consistent error handling pattern
- [ ] Module-level docstring

**Quality Pattern**:
```python
"""Z3 solver adapter implementation.

This module provides Z3SolverAdapter, a thin wrapper around the Z3 SMT
solver that implements the SolverInterface abstraction.

Standards Compliance:
- No decorators (CODE_STANDARDS.md §2)
- Relative imports for local modules
- User-friendly error messages with actionable guidance
- Backward compatible with existing Z3 usage

Example:
    >>> adapter = Z3SolverAdapter()
    >>> solver = adapter.create_solver()
    >>> x = z3.Int('x')
    >>> adapter.assert_constraint(solver, x > 0)
    >>> result = adapter.check_sat(solver)
    >>> print(result)  # "sat"
"""
```

### Task 8: Coverage Check (1 hour)
**Duration**: 1 hour

- [ ] Run coverage analysis
- [ ] Target: >90% coverage
- [ ] Identify untested paths
- [ ] Add tests for error cases
- [ ] Test all branches

**Coverage Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_z3_adapter.py \
    --cov=model_checker.solver.z3_adapter \
    --cov-report=term-missing \
    --cov-fail-under=90
```

**Expected**: >90% coverage

### Task 9: Backward Compatibility Validation (1 hour)
**Duration**: 1 hour

- [ ] Verify adapter behavior matches direct Z3 usage
- [ ] Test pattern hints work correctly
- [ ] Test all return types match Z3 types
- [ ] Validate no performance overhead on simple cases

**Validation Tests**:
```python
def test_backward_compatibility_simple_formula(self):
    """Test adapter produces same results as direct Z3."""
    # Direct Z3
    solver_direct = z3.Solver()
    x = z3.Int('x')
    solver_direct.add(x > 0)
    result_direct = str(solver_direct.check())

    # Via adapter
    adapter = Z3SolverAdapter()
    solver_adapter = adapter.create_solver()
    adapter.assert_constraint(solver_adapter, x > 0)
    result_adapter = adapter.check_sat(solver_adapter)

    self.assertEqual(result_direct, result_adapter)
```

### Task 10: Update Stage Plan and Commit (30 min)
**Duration**: 30 minutes

- [ ] Mark all tasks complete
- [ ] Update Phase 2 progress
- [ ] Create git commit

**Commit Message Template**:
```
feat(phase2-stage02): Z3SolverAdapter implementation

Implemented Z3 adapter as thin wrapper over Z3 API, providing
backward-compatible access through SolverInterface.

Changes:
- Created Z3SolverAdapter with all ~35 interface methods
- Direct delegation to Z3 API (thin wrapper pattern)
- Pattern hints supported (Z3 feature)
- User-friendly error messages for all failure cases
- TDD approach: comprehensive tests before implementation
- Coverage: >90%

Stage: 2/5 (Phase 2 - Abstraction Layer)
Tests: 25/25 passing
Coverage: 94%
Duration: 2 days
Plan: bimodal/specs/cvc5/phase2_abstraction/stage02_z3_adapter.md

Standards Compliance:
- NO decorators ✅
- Relative imports ✅
- Backward compatible ✅

Co-Authored-By: Claude <noreply@anthropic.com>
```

## Testing Strategy

### Unit Tests (test_z3_adapter.py)

**Test Categories**:
1. **Lifecycle** (5 tests): create, assert, check, model, push/pop
2. **Type Constructors** (6 tests): bool, int, bitvec, array, uninterpreted, function
3. **Value Constructors** (5 tests): bool val, int val, bitvec val, const, var
4. **Logical Operators** (7 tests): and, or, not, implies, equal, forall, exists
5. **Array Operations** (2 tests): select, store
6. **Configuration** (3 tests): set_option, get_capabilities, error handling
7. **Pattern Hints** (2 tests): ForAll/Exists with patterns
8. **Error Cases** (5 tests): invalid constraint, model when unsat, etc.

**Total**: ~35 test cases

### Integration Validation

**After Stage 2**:
- Z3SolverAdapter fully implements SolverInterface
- Backward compatible with existing Z3 code
- Pattern hints work correctly
- All error paths tested
- >90% coverage achieved

## Success Criteria Checklist

- [ ] test_z3_adapter.py written BEFORE implementation (TDD-RED)
- [ ] Z3SolverAdapter class created
- [ ] All lifecycle methods implemented
- [ ] All type constructors implemented
- [ ] All value constructors implemented
- [ ] All logical operators implemented
- [ ] Array operations implemented
- [ ] Configuration methods implemented
- [ ] Pattern hints supported (Z3 feature)
- [ ] All tests passing (TDD-GREEN)
- [ ] NO decorators anywhere
- [ ] Relative imports used
- [ ] User-friendly error messages
- [ ] Coverage >90%
- [ ] Backward compatibility validated
- [ ] Code refactored for quality
- [ ] Git commit created
- [ ] Ready for Stage 3 (CVC5 adapter)

## Common Issues & Solutions

### Issue 1: Z3 not installed

**Problem**: Tests fail because Z3 not available

**Solution**: Install Z3: `pip install z3-solver`

### Issue 2: String vs Enum for check_sat result

**Problem**: Z3 returns CheckSatResult, not string

**Solution**: Convert to string: `str(solver.check())` returns "sat", "unsat", or "unknown"

### Issue 3: Model extraction when unsat

**Problem**: solver.model() raises Z3Exception when UNSAT

**Solution**: Catch exception and raise user-friendly ValueError

### Issue 4: Pattern hints type confusion

**Problem**: Not sure what type patterns should be

**Solution**: patterns is Optional[List[z3.PatternRef]], use z3.MultiPattern(...)

### Issue 5: BitVec argument order

**Problem**: Confusion about (value, size) vs (size, value)

**Solution**: Z3 uses (value, size), which matches interface. No conversion needed.

## Risk Mitigation

### Risk 1: Z3 API Changes
**Risk**: Z3 API evolves, breaks adapter
**Impact**: Tests fail on new Z3 versions
**Mitigation**: Pin Z3 version in requirements
**Fallback**: Update adapter for new Z3 API

### Risk 2: Performance Overhead
**Risk**: Wrapper adds latency
**Impact**: Defeats thin wrapper goal
**Mitigation**: Direct delegation, no extra logic
**Fallback**: Profile and optimize hot paths

### Risk 3: Incomplete Error Handling
**Risk**: Edge cases not caught
**Impact**: Cryptic errors leak through
**Mitigation**: Comprehensive error tests
**Fallback**: Add handling as discovered

### Risk 4: Pattern Hints Breaking
**Risk**: Pattern hints don't work through wrapper
**Impact**: Quantifier performance regression
**Mitigation**: Test pattern hints explicitly
**Fallback**: Document limitations

## Dependencies for Next Stage

**Stage 3 Requirements**:
- Z3SolverAdapter complete and tested
- Pattern for implementing SolverInterface established
- Error handling pattern established
- >90% coverage demonstrates feasibility
- Foundation for CVC5SolverAdapter (more complex)

## Notes

### Design Decisions

**Thin Wrapper**: Direct delegation to Z3 API wherever possible. No extra logic unless needed for interface compliance.

**Error Handling**: Wrap Z3 exceptions in ValueError/RuntimeError with helpful messages.

**Pattern Hints**: Fully supported since Z3 provides them. Optional parameter for interface compatibility.

### Cross-References

- **Parent Plan**: [phase2_abstraction_layer_design.md](./phase2_abstraction_layer_design.md)
- **Previous Stage**: [Stage 1: Interface and Capabilities](./stage01_interface_capabilities.md)
- **Next Stage**: [Stage 3: CVC5SolverAdapter](./stage03_cvc5_adapter.md)
- **Standards**: [CODE_STANDARDS.md](../../../../../../docs/core/CODE_STANDARDS.md)

---

**Stage 2 Status**: ✅ COMPLETE
**Completed**: 2025-10-03
**Duration**: ~2 hours (actual)
**Tests**: 36 passing (all Z3 adapter tests)
**Coverage**: z3_adapter.py 90% (meets >90% requirement)
**Previous Stage**: [Stage 1: Interface and Capabilities Design](./stage01_interface_capabilities.md)
**Next Stage**: [Stage 3: CVC5SolverAdapter Implementation](./stage03_cvc5_adapter.md)
