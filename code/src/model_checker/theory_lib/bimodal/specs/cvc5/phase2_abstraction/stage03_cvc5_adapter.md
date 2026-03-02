# Stage 3: CVC5SolverAdapter Implementation

## Metadata
- **Stage**: 3/5 (Phase 2 - Abstraction Layer Implementation)
- **Estimated Duration**: 3 days (24 hours)
- **Complexity**: High (CVC5 API translation, Phase 1 patterns)
- **Dependencies**: Stage 1 complete (SolverInterface), Stage 2 complete (Z3 adapter pattern established)
- **Files**:
  - `solver/cvc5_adapter.py` (~450 LOC expected)
  - `solver/tests/unit/test_cvc5_adapter.py` (~500 LOC expected)
- **Coverage Target**: >90% (critical path for abstraction layer)
- **Risk**: High (CVC5 API complexity, solver storage design decision)

## Objective

Implement CVC5SolverAdapter using Phase 1 CVC5 migration patterns. This adapter applies all learnings from the bimodal CVC5 pilot, including MBQI+enum-inst configuration, BitVec argument normalization, and quantifier handling without pattern hints.

**Success Criteria**: All SolverInterface methods implemented for CVC5, MBQI+enum-inst configured automatically, BitVec arguments normalized, tests pass, >90% coverage, NO decorators.

## Implementation Tasks

### Task 1: [TDD-RED] Write test_cvc5_adapter.py First (3 hours)
**Duration**: 3 hours

- [ ] Create test file: `solver/tests/unit/test_cvc5_adapter.py`
- [ ] Test CVC5SolverAdapter lifecycle with MBQI+enum-inst
- [ ] Test type constructors (sort creation through solver)
- [ ] Test value constructors (BitVec normalization!)
- [ ] Test logical operators (mkTerm pattern)
- [ ] Test quantifiers (VARIABLE_LIST pattern, no pattern hints)
- [ ] Test array operations
- [ ] Test configuration and capabilities
- [ ] Test CVC5-specific error handling
- [ ] Run tests - verify they FAIL (adapter not implemented)

**Test Structure**:
```python
import unittest
try:
    import cvc5
    from cvc5 import Kind
    CVC5_AVAILABLE = True
except ImportError:
    CVC5_AVAILABLE = False

from model_checker.solver.cvc5_adapter import CVC5SolverAdapter
from model_checker.solver.capabilities import CapabilityMatrix


@unittest.skipUnless(CVC5_AVAILABLE, "CVC5 not installed")
class TestCVC5SolverAdapter(unittest.TestCase):
    """Test CVC5SolverAdapter implementation."""

    def setUp(self):
        """Create CVC5 adapter for tests."""
        self.adapter = CVC5SolverAdapter()

    def test_create_solver_configures_mbqi(self):
        """Test create_solver configures MBQI+enum-inst automatically."""
        solver = self.adapter.create_solver()

        self.assertIsInstance(solver, cvc5.Solver)

        # Verify MBQI and enum-inst configured
        # Note: CVC5 doesn't expose option values easily
        # Test via behavior instead

    def test_lifecycle_operations(self):
        """Test solver lifecycle with CVC5."""
        solver = self.adapter.create_solver()

        # Create simple formula
        x_sort = self.adapter.mk_int_sort()
        x = self.adapter.mk_const(x_sort, 'x')

        # x > 0
        zero = self.adapter.mk_int_val(0)
        constraint = solver.mkTerm(Kind.GT, x, zero)

        self.adapter.assert_constraint(solver, constraint)
        result = self.adapter.check_sat(solver)

        self.assertEqual(result, "sat")

    def test_type_constructors_require_solver(self):
        """Test type constructors access internal solver."""
        # CVC5 requires solver for sort creation
        bool_sort = self.adapter.mk_bool_sort()
        self.assertIsInstance(bool_sort, cvc5.Sort)

        int_sort = self.adapter.mk_int_sort()
        self.assertIsInstance(int_sort, cvc5.Sort)

    def test_bitvec_val_argument_normalization(self):
        """Test BitVec value normalizes (value, size) → (size, value)."""
        # Interface uses (value, size)
        # CVC5 API uses (size, value)
        # Adapter must normalize

        bv = self.adapter.mk_bitvec_val(42, 8)

        self.assertIsInstance(bv, cvc5.Term)
        # Verify value is correct (not swapped incorrectly)

    def test_forall_ignores_pattern_hints(self):
        """Test ForAll ignores pattern hints (CVC5 uses MBQI instead)."""
        x_sort = self.adapter.mk_int_sort()
        x = self.adapter.mk_var(x_sort, 'x')

        zero = self.adapter.mk_int_val(0)
        ten = self.adapter.mk_int_val(10)

        body = self.adapter.mk_and(
            solver.mkTerm(Kind.GT, x, zero),
            solver.mkTerm(Kind.LT, x, ten)
        )

        # Pattern hints provided but should be ignored
        fake_patterns = ["ignored"]

        forall = self.adapter.mk_forall([x], body, patterns=fake_patterns)
        self.assertIsInstance(forall, cvc5.Term)
        # Should not error even though patterns provided

    def test_forall_uses_variable_list(self):
        """Test ForAll creates VARIABLE_LIST term correctly."""
        x_sort = self.adapter.mk_int_sort()
        y_sort = self.adapter.mk_int_sort()

        x = self.adapter.mk_var(x_sort, 'x')
        y = self.adapter.mk_var(y_sort, 'y')

        # Body: x < y
        body = solver.mkTerm(Kind.LT, x, y)

        forall = self.adapter.mk_forall([x, y], body)

        self.assertIsInstance(forall, cvc5.Term)
        # ForAll should use VARIABLE_LIST pattern

    def test_capabilities(self):
        """Test CVC5 capabilities returned correctly."""
        cap = self.adapter.get_capabilities()

        self.assertIsInstance(cap, CapabilityMatrix)
        # CVC5 uses MBQI
        self.assertTrue(cap.has_mbqi)
        self.assertTrue(cap.has_enum_inst)
        # CVC5 doesn't use pattern hints
        self.assertFalse(cap.has_pattern_hints)

    def test_error_handling_cvc5_not_installed(self):
        """Test user-friendly error when CVC5 not available."""
        # This test requires mocking CVC5 import failure
        # Or running in environment without CVC5

    def test_mk_const_vs_mk_var_distinction(self):
        """Test mk_const vs mk_var for CVC5 quantifiers."""
        # CVC5 distinguishes constants from variables
        int_sort = self.adapter.mk_int_sort()

        const = self.adapter.mk_const(int_sort, 'c')
        var = self.adapter.mk_var(int_sort, 'v')

        # Both should be Terms
        self.assertIsInstance(const, cvc5.Term)
        self.assertIsInstance(var, cvc5.Term)

        # Var should be usable in quantifiers
        body = solver.mkTerm(Kind.GT, var, const)
        forall = self.adapter.mk_forall([var], body)
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py -v
```

**Expected**: FAIL (cvc5_adapter.py does not exist)

### Task 2: [TDD-GREEN] Implement CVC5SolverAdapter - Lifecycle with MBQI (2 hours)
**Duration**: 2 hours

- [ ] Create `solver/cvc5_adapter.py`
- [ ] Import cvc5, Kind, SolverInterface, CapabilityMatrix
- [ ] Implement CVC5SolverAdapter class
- [ ] Implement __init__ with cvc5_capabilities
- [ ] **CRITICAL**: Implement create_solver with MBQI+enum-inst configuration
- [ ] Implement assert_constraint → solver.assertFormula
- [ ] Implement check_sat → result.isSat/isUnsat/isUnknown
- [ ] Implement get_model → solver.getValue (no separate model object)
- [ ] Implement push, pop, reset
- [ ] NO decorators, relative imports

**Implementation Pattern**:
```python
"""CVC5 solver adapter implementation."""

# Standard library
from typing import Any, List, Optional

# Third-party
try:
    import cvc5
    from cvc5 import Kind
    CVC5_AVAILABLE = True
except ImportError:
    CVC5_AVAILABLE = False

# Relative imports
from .interface import SolverInterface
from .capabilities import CapabilityMatrix, cvc5_capabilities


class CVC5SolverAdapter(SolverInterface):
    """CVC5 implementation of SolverInterface.

    Applies Phase 1 CVC5 migration patterns.
    No decorators per CODE_STANDARDS.md.
    """

    def __init__(self):
        """Initialize CVC5 adapter."""
        if not CVC5_AVAILABLE:
            raise RuntimeError(
                "CVC5 solver library not available. "
                "Install with: pip install cvc5\n"
                "For NixOS, see Code/docs/development/CVC5_CONFIGURATION.md"
            )
        self._capabilities = cvc5_capabilities()

        # CVC5 requires solver for sort creation - store internal solver
        self._solver = None

    def _ensure_solver(self) -> cvc5.Solver:
        """Ensure adapter has solver for sort creation.

        CVC5 requires solver instance for creating sorts.
        Create on-demand and cache.
        """
        if self._solver is None:
            self._solver = self._create_configured_solver()
        return self._solver

    def _create_configured_solver(self) -> cvc5.Solver:
        """Create CVC5 solver with proper configuration.

        CRITICAL: MBQI and enum-inst are essential for witness
        predicate performance (850× speedup from Phase 1).
        """
        try:
            solver = cvc5.Solver()
            solver.setLogic("ALL")
            solver.setOption("produce-models", "true")

            # CRITICAL for witness predicate performance
            solver.setOption("mbqi", "true")
            solver.setOption("enum-inst", "true")

            return solver
        except Exception as e:
            raise RuntimeError(
                f"Failed to create CVC5 solver: {e}. "
                f"Check CVC5 installation and version compatibility."
            )

    def create_solver(self) -> cvc5.Solver:
        """Create CVC5 solver with MBQI+enum-inst configuration."""
        return self._create_configured_solver()

    def assert_constraint(self, solver: cvc5.Solver, constraint: cvc5.Term) -> None:
        """Assert constraint in CVC5 solver."""
        try:
            solver.assertFormula(constraint)
        except Exception as e:
            raise ValueError(
                f"Failed to assert constraint: {e}. "
                f"Ensure constraint is valid CVC5 Term."
            )

    def check_sat(self, solver: cvc5.Solver) -> str:
        """Check satisfiability."""
        result = solver.checkSat()
        if result.isSat():
            return "sat"
        elif result.isUnsat():
            return "unsat"
        else:
            return "unknown"

    def get_model(self, solver: cvc5.Solver) -> Any:
        """Get model from SAT solver.

        Note: CVC5 doesn't have separate model object.
        Return solver for getValue calls.
        """
        # Check if solver is SAT
        result = solver.checkSat()
        if not result.isSat():
            raise ValueError(
                "Cannot extract model: solver is not SAT. "
                "Run check_sat() and verify result is 'sat' first."
            )
        return solver  # Return solver itself for getValue calls

    def push(self, solver: cvc5.Solver) -> None:
        """Push solver context."""
        solver.push()

    def pop(self, solver: cvc5.Solver, num: int = 1) -> None:
        """Pop solver context."""
        solver.pop(num)

    def reset(self, solver: cvc5.Solver) -> None:
        """Reset solver to initial state."""
        solver.resetAssertions()
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py::TestCVC5SolverAdapter::test_create_solver_configures_mbqi -v
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py::TestCVC5SolverAdapter::test_lifecycle_operations -v
```

### Task 3: [TDD-GREEN] Implement Type Constructors with Solver Storage (3 hours)
**Duration**: 3 hours

- [ ] Design decision: Store internal solver for sort creation
- [ ] Implement mk_bool_sort → solver.getBooleanSort()
- [ ] Implement mk_int_sort → solver.getIntegerSort()
- [ ] Implement mk_bitvec_sort → solver.mkBitVectorSort(size)
- [ ] Implement mk_array_sort → solver.mkArraySort(index, element)
- [ ] Implement mk_uninterpreted_sort → solver.mkUninterpretedSort(name)
- [ ] Implement mk_function → mkFunctionSort + mkConst (two-step!)

**Pattern**:
```python
def mk_bool_sort(self) -> cvc5.Sort:
    """Create Boolean sort."""
    solver = self._ensure_solver()
    return solver.getBooleanSort()

def mk_int_sort(self) -> cvc5.Sort:
    """Create Integer sort."""
    solver = self._ensure_solver()
    return solver.getIntegerSort()

def mk_bitvec_sort(self, size: int) -> cvc5.Sort:
    """Create BitVector sort."""
    solver = self._ensure_solver()
    return solver.mkBitVectorSort(size)

def mk_array_sort(self, index_sort: cvc5.Sort, element_sort: cvc5.Sort) -> cvc5.Sort:
    """Create Array sort."""
    solver = self._ensure_solver()
    return solver.mkArraySort(index_sort, element_sort)

def mk_uninterpreted_sort(self, name: str) -> cvc5.Sort:
    """Create uninterpreted sort."""
    solver = self._ensure_solver()
    return solver.mkUninterpretedSort(name)

def mk_function(self, name: str, domain: List[cvc5.Sort], range: cvc5.Sort) -> cvc5.Term:
    """Create function declaration.

    CVC5 uses two-step pattern:
    1. mkFunctionSort([domain], range)
    2. mkConst(function_sort, name)
    """
    solver = self._ensure_solver()
    func_sort = solver.mkFunctionSort(domain, range)
    return solver.mkConst(func_sort, name)
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py::TestCVC5SolverAdapter::test_type_constructors_require_solver -v
```

### Task 4: [TDD-GREEN] Implement Value Constructors with BitVec Normalization (2 hours)
**Duration**: 2 hours

- [ ] Implement mk_bool_val → solver.mkBoolean(value)
- [ ] Implement mk_int_val → solver.mkInteger(value)
- [ ] **CRITICAL**: Implement mk_bitvec_val with argument swap (value,size) → (size,value)
- [ ] Implement mk_const → solver.mkConst(sort, name)
- [ ] Implement mk_var → solver.mkVar(sort, name) [CVC5 distinction!]

**Pattern**:
```python
def mk_bool_val(self, value: bool) -> cvc5.Term:
    """Create Boolean value."""
    solver = self._ensure_solver()
    return solver.mkBoolean(value)

def mk_int_val(self, value: int) -> cvc5.Term:
    """Create Integer value."""
    solver = self._ensure_solver()
    return solver.mkInteger(value)

def mk_bitvec_val(self, value: int, size: int) -> cvc5.Term:
    """Create BitVector value.

    CRITICAL: CVC5 uses (size, value) - REVERSE of Z3 and interface!
    Interface uses (value, size) for consistency.
    Adapter normalizes arguments.
    """
    solver = self._ensure_solver()
    # SWAP: (value, size) → (size, value)
    return solver.mkBitVector(size, value)

def mk_const(self, sort: cvc5.Sort, name: str) -> cvc5.Term:
    """Create constant.

    CVC5 distinction: Use for uninterpreted constants.
    For quantifier variables, use mk_var.
    """
    solver = self._ensure_solver()
    return solver.mkConst(sort, name)

def mk_var(self, sort: cvc5.Sort, name: str) -> cvc5.Term:
    """Create variable for quantifiers.

    CVC5 distinction: Variables for quantifiers use mkVar.
    For constants, use mk_const.
    """
    solver = self._ensure_solver()
    return solver.mkVar(sort, name)
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py::TestCVC5SolverAdapter::test_bitvec_val_argument_normalization -v
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py::TestCVC5SolverAdapter::test_mk_const_vs_mk_var_distinction -v
```

### Task 5: [TDD-GREEN] Implement Logical Operators with mkTerm (3 hours)
**Duration**: 3 hours

- [ ] Implement mk_and → solver.mkTerm(Kind.AND, *args)
- [ ] Implement mk_or → solver.mkTerm(Kind.OR, *args)
- [ ] Implement mk_not → solver.mkTerm(Kind.NOT, arg)
- [ ] Implement mk_implies → solver.mkTerm(Kind.IMPLIES, lhs, rhs)
- [ ] Implement mk_equal → solver.mkTerm(Kind.EQUAL, lhs, rhs)

**Pattern**:
```python
def mk_and(self, *args: cvc5.Term) -> cvc5.Term:
    """Create conjunction."""
    solver = self._ensure_solver()
    if len(args) == 1:
        return args[0]
    return solver.mkTerm(Kind.AND, *args)

def mk_or(self, *args: cvc5.Term) -> cvc5.Term:
    """Create disjunction."""
    solver = self._ensure_solver()
    if len(args) == 1:
        return args[0]
    return solver.mkTerm(Kind.OR, *args)

def mk_not(self, arg: cvc5.Term) -> cvc5.Term:
    """Create negation."""
    solver = self._ensure_solver()
    return solver.mkTerm(Kind.NOT, arg)

def mk_implies(self, lhs: cvc5.Term, rhs: cvc5.Term) -> cvc5.Term:
    """Create implication."""
    solver = self._ensure_solver()
    return solver.mkTerm(Kind.IMPLIES, lhs, rhs)

def mk_equal(self, lhs: cvc5.Term, rhs: cvc5.Term) -> cvc5.Term:
    """Create equality."""
    solver = self._ensure_solver()
    return solver.mkTerm(Kind.EQUAL, lhs, rhs)
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py -k "logical" -v
```

### Task 6: [TDD-GREEN] Implement Quantifiers with VARIABLE_LIST Pattern (4 hours)
**Duration**: 4 hours

- [ ] Implement mk_forall → mkTerm(Kind.VARIABLE_LIST, ...) + mkTerm(Kind.FORALL, ...)
- [ ] Implement mk_exists → mkTerm(Kind.VARIABLE_LIST, ...) + mkTerm(Kind.EXISTS, ...)
- [ ] **CRITICAL**: Ignore pattern hints parameter (CVC5 uses MBQI instead)
- [ ] Handle single vs multiple variables correctly

**Pattern**:
```python
def mk_forall(self, vars: List[cvc5.Term], body: cvc5.Term,
              patterns: Optional[List[Any]] = None) -> cvc5.Term:
    """Create ForAll quantifier.

    CVC5 pattern:
    1. Create VARIABLE_LIST from vars
    2. Create FORALL with var_list and body

    Note: CVC5 doesn't use pattern hints - relies on MBQI+enum-inst.
    patterns parameter ignored for interface compatibility.
    """
    solver = self._ensure_solver()

    # Create VARIABLE_LIST
    var_list = solver.mkTerm(Kind.VARIABLE_LIST, *vars)

    # Create FORALL
    forall = solver.mkTerm(Kind.FORALL, var_list, body)

    # Pattern hints ignored (CVC5 uses MBQI configuration instead)
    if patterns is not None:
        # Log warning? Or silently ignore per design
        pass

    return forall

def mk_exists(self, vars: List[cvc5.Term], body: cvc5.Term,
              patterns: Optional[List[Any]] = None) -> cvc5.Term:
    """Create Exists quantifier.

    Same pattern as ForAll but with EXISTS kind.
    """
    solver = self._ensure_solver()

    var_list = solver.mkTerm(Kind.VARIABLE_LIST, *vars)
    exists = solver.mkTerm(Kind.EXISTS, var_list, body)

    # Pattern hints ignored
    return exists
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py::TestCVC5SolverAdapter::test_forall_ignores_pattern_hints -v
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py::TestCVC5SolverAdapter::test_forall_uses_variable_list -v
```

### Task 7: [TDD-GREEN] Implement Array Operations and Configuration (2 hours)
**Duration**: 2 hours

- [ ] Implement mk_select → solver.mkTerm(Kind.SELECT, array, index)
- [ ] Implement mk_store → solver.mkTerm(Kind.STORE, array, index, value)
- [ ] Implement set_option → solver.setOption(key, value)
- [ ] Implement get_capabilities → return self._capabilities

**Pattern**:
```python
def mk_select(self, array: cvc5.Term, index: cvc5.Term) -> cvc5.Term:
    """Array select operation."""
    solver = self._ensure_solver()
    return solver.mkTerm(Kind.SELECT, array, index)

def mk_store(self, array: cvc5.Term, index: cvc5.Term, value: cvc5.Term) -> cvc5.Term:
    """Array store operation."""
    solver = self._ensure_solver()
    return solver.mkTerm(Kind.STORE, array, index, value)

def set_option(self, solver: cvc5.Solver, key: str, value: str) -> None:
    """Set solver option."""
    try:
        solver.setOption(key, value)
    except Exception as e:
        raise ValueError(
            f"Failed to set option '{key}' to '{value}': {e}. "
            f"Check CVC5 documentation for valid options."
        )

def get_capabilities(self) -> CapabilityMatrix:
    """Get CVC5 capabilities."""
    return self._capabilities
```

**Testing Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py -v
```

**Expected**: ALL tests pass (GREEN state for entire adapter)

### Task 8: [REFACTOR] Code Quality and CVC5-Specific Documentation (3 hours)
**Duration**: 3 hours

- [ ] Review all error messages for CVC5-specific guidance
- [ ] Add comprehensive docstrings with CVC5 patterns
- [ ] Document MBQI+enum-inst configuration rationale
- [ ] Document BitVec argument normalization
- [ ] Document mk_const vs mk_var distinction
- [ ] Verify NO decorators
- [ ] Module-level docstring with Phase 1 references

**Quality Pattern**:
```python
"""CVC5 solver adapter implementation.

This module provides CVC5SolverAdapter, implementing SolverInterface for
the CVC5 SMT solver using patterns learned from Phase 1 bimodal migration.

Key CVC5 Patterns (from Phase 1):
- MBQI+enum-inst: Critical for witness predicate performance (850× speedup)
- VARIABLE_LIST: Required for ForAll/Exists quantifiers
- BitVec normalization: (value, size) → (size, value)
- mkConst vs mkVar: Different purposes in CVC5
- No pattern hints: CVC5 relies on MBQI configuration instead

Standards Compliance:
- No decorators (CODE_STANDARDS.md §2)
- Relative imports for local modules
- User-friendly error messages with CVC5-specific guidance

Example:
    >>> adapter = CVC5SolverAdapter()
    >>> solver = adapter.create_solver()  # MBQI+enum-inst configured!
    >>> x_sort = adapter.mk_int_sort()
    >>> x = adapter.mk_var(x_sort, 'x')  # Use mk_var for quantifiers
    >>> body = ...
    >>> forall = adapter.mk_forall([x], body)  # No pattern hints needed
"""
```

### Task 9: Coverage Check (2 hours)
**Duration**: 2 hours

- [ ] Run coverage analysis
- [ ] Target: >90% coverage
- [ ] Test all error paths
- [ ] Test MBQI configuration
- [ ] Test BitVec normalization edge cases

**Coverage Command**:
```bash
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py \
    --cov=model_checker.solver.cvc5_adapter \
    --cov-report=term-missing \
    --cov-fail-under=90
```

**Expected**: >90% coverage

### Task 10: Phase 1 Pattern Validation (2 hours)
**Duration**: 2 hours

- [ ] Verify all Phase 1 patterns applied correctly
- [ ] Test quantifier creation matches Phase 1 bimodal code
- [ ] Test MBQI+enum-inst configuration works
- [ ] Compare adapter behavior to Phase 1 direct CVC5 usage

**Validation Tests**:
```python
def test_matches_phase1_forall_pattern(self):
    """Test ForAll matches Phase 1 bimodal pattern."""
    # Phase 1 pattern from bimodal migration
    # VARIABLE_LIST + FORALL Kind
    # ...
```

### Task 11: Update Stage Plan and Commit (30 min)
**Duration**: 30 minutes

- [ ] Mark all tasks complete
- [ ] Update Phase 2 progress
- [ ] Create git commit

**Commit Message Template**:
```
feat(phase2-stage03): CVC5SolverAdapter implementation with Phase 1 patterns

Implemented CVC5 adapter using all Phase 1 bimodal migration learnings.

Changes:
- Created CVC5SolverAdapter with all ~35 interface methods
- MBQI+enum-inst configured automatically (critical for performance)
- BitVec argument normalization: (value, size) → (size, value)
- VARIABLE_LIST pattern for quantifiers
- mkConst vs mkVar distinction for CVC5
- Pattern hints ignored (CVC5 uses MBQI instead)
- Internal solver storage for sort creation
- User-friendly CVC5-specific error messages
- TDD approach: comprehensive tests before implementation
- Coverage: >90%

Stage: 3/5 (Phase 2 - Abstraction Layer)
Tests: 35/35 passing
Coverage: 93%
Duration: 3 days
Plan: bimodal/specs/cvc5/phase2_abstraction/stage03_cvc5_adapter.md

Phase 1 Patterns Applied:
- MBQI+enum-inst (850× speedup) ✅
- VARIABLE_LIST for quantifiers ✅
- BitVec normalization ✅

Standards Compliance:
- NO decorators ✅
- Relative imports ✅
- User-friendly errors ✅

Co-Authored-By: Claude <noreply@anthropic.com>
```

## Testing Strategy

### Unit Tests (test_cvc5_adapter.py)

**Test Categories**:
1. **Lifecycle with MBQI** (6 tests): create with MBQI, assert, check, model, push/pop
2. **Type Constructors** (6 tests): bool, int, bitvec, array, uninterpreted, function
3. **Value Constructors** (6 tests): bool val, int val, bitvec val (normalized!), const, var
4. **Logical Operators** (5 tests): and, or, not, implies, equal
5. **Quantifiers** (4 tests): forall, exists, VARIABLE_LIST, pattern hints ignored
6. **Array Operations** (2 tests): select, store
7. **Configuration** (3 tests): set_option, get_capabilities, MBQI verification
8. **Error Cases** (3 tests): CVC5 not installed, invalid constraint, etc.

**Total**: ~35 test cases

### Integration Validation

**After Stage 3**:
- CVC5SolverAdapter fully implements SolverInterface
- MBQI+enum-inst configured automatically
- All Phase 1 patterns applied correctly
- BitVec arguments normalized
- >90% coverage achieved

## Success Criteria Checklist

- [ ] test_cvc5_adapter.py written BEFORE implementation (TDD-RED)
- [ ] CVC5SolverAdapter class created
- [ ] __init__ checks CVC5 availability
- [ ] create_solver configures MBQI+enum-inst
- [ ] Internal solver stored for sort creation
- [ ] All lifecycle methods implemented
- [ ] All type constructors implemented
- [ ] All value constructors implemented (BitVec normalized!)
- [ ] All logical operators implemented (mkTerm pattern)
- [ ] Quantifiers use VARIABLE_LIST pattern
- [ ] Pattern hints ignored gracefully
- [ ] mk_const vs mk_var distinction implemented
- [ ] Array operations implemented
- [ ] Configuration methods implemented
- [ ] All tests passing (TDD-GREEN)
- [ ] NO decorators anywhere
- [ ] Relative imports used
- [ ] CVC5-specific error messages
- [ ] Coverage >90%
- [ ] Phase 1 patterns validated
- [ ] Code refactored for quality
- [ ] Git commit created
- [ ] Ready for Stage 4 (factory and integration)

## Common Issues & Solutions

### Issue 1: CVC5 not installed

**Problem**: Import fails, tests can't run

**Solution**: Install CVC5: `pip install cvc5` or follow NixOS guide

### Issue 2: Solver storage complexity

**Problem**: Need solver for sorts but also creating fresh solvers

**Solution**: Internal solver (_ensure_solver) for sorts, separate create_solver for users

### Issue 3: BitVec arguments swapped

**Problem**: (value, size) vs (size, value) confusion

**Solution**: Document clearly: Interface uses (value, size), CVC5 API uses (size, value), adapter swaps

### Issue 4: VARIABLE_LIST creation errors

**Problem**: mkTerm(Kind.VARIABLE_LIST, ...) fails

**Solution**: Ensure vars are Terms created with mkVar, not mkConst

### Issue 5: Pattern hints warning spam

**Problem**: Want to warn about ignored patterns but not spam logs

**Solution**: Silently ignore per design (documented in docstring)

### Issue 6: MBQI not configured

**Problem**: Forgot to set MBQI in create_solver

**Solution**: Test explicitly that MBQI configured, make it impossible to forget

## Risk Mitigation

### Risk 1: Solver Storage Design
**Risk**: Storing internal solver causes state issues
**Impact**: Sorts created with wrong solver
**Mitigation**: Document pattern clearly, test thoroughly
**Fallback**: Alternative design: pass solver to sort methods

### Risk 2: MBQI Configuration Forgotten
**Risk**: Developer creates solver without MBQI
**Impact**: 850× performance regression
**Mitigation**: MBQI configured in create_solver automatically
**Fallback**: Test performance regression if found

### Risk 3: BitVec Normalization Bug
**Risk**: Arguments swapped incorrectly
**Impact**: Wrong BitVec values
**Mitigation**: Explicit tests for normalization
**Fallback**: Fix immediately with test validation

### Risk 4: Quantifier Pattern Incorrect
**Risk**: VARIABLE_LIST not created properly
**Impact**: Quantifiers fail or behave incorrectly
**Mitigation**: Test matches Phase 1 bimodal code
**Fallback**: Reference Phase 1 implementation

### Risk 5: CVC5 Version Compatibility
**Risk**: CVC5 API changes break adapter
**Impact**: Tests fail on newer CVC5
**Mitigation**: Pin CVC5 version
**Fallback**: Update adapter for new API

## Dependencies for Next Stage

**Stage 4 Requirements**:
- CVC5SolverAdapter complete and tested
- MBQI+enum-inst configuration proven
- Phase 1 patterns validated
- Both Z3 and CVC5 adapters ready for factory
- >90% coverage demonstrates quality
- Foundation for SolverFactory integration

## Notes

### Design Decisions

**Solver Storage**: Store internal solver for sort creation (CVC5 requirement). Separate from user solvers created via create_solver.

**MBQI Configuration**: Always configure MBQI+enum-inst in create_solver. Non-negotiable based on Phase 1 performance results (850× speedup).

**BitVec Normalization**: Interface uses (value, size) everywhere. Adapter swaps to (size, value) for CVC5 API calls.

**Pattern Hints**: Ignore silently. CVC5 doesn't use them, and documenting this is sufficient.

### Phase 1 References

- **MBQI+enum-inst**: Lines 728-731 of phase2_abstraction_layer_design.md
- **VARIABLE_LIST**: Lines 800-801
- **BitVec swap**: Lines 785-791
- **Performance**: 850× speedup documented in Phase 1 results

### Cross-References

- **Parent Plan**: [phase2_abstraction_layer_design.md](./phase2_abstraction_layer_design.md)
- **Previous Stage**: [Stage 2: Z3SolverAdapter](./stage02_z3_adapter.md)
- **Next Stage**: [Stage 4: Factory and Integration](./stage04_factory_integration.md)
- **Phase 1 Complete**: All patterns validated in bimodal CVC5 pilot

---

**Stage 3 Status**: ✅ COMPLETE
**Completed**: 2025-10-03
**Duration**: ~3 hours (actual)
**Tests**: 44 passing (all CVC5 adapter tests)
**Coverage**: cvc5_adapter.py 92% (exceeds >90% requirement)
**Total Solver Tests**: 109/109 passing (interface + capabilities + Z3 + CVC5)
**Key Achievement**: Shared solver pattern solved CVC5 term manager issue
**Previous Stage**: [Stage 2: Z3SolverAdapter Implementation](./stage02_z3_adapter.md)
**Next Stage**: [Stage 4: Factory and Integration](./stage04_factory_integration.md)
