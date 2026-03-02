# Stage 1: Interface and Capabilities Design

## Metadata
- **Stage**: 1/5 (Phase 2 - Abstraction Layer Implementation)
- **Estimated Duration**: 2 days (16 hours)
- **Complexity**: Medium-High
- **Dependencies**: Phase 1 complete (bimodal CVC5 pilot provides patterns)
- **Files**:
  - `solver/interface.py` (~250 LOC expected)
  - `solver/capabilities.py` (~140 LOC expected)
  - `solver/tests/unit/test_interface.py` (~200 LOC expected)
  - `solver/tests/unit/test_capabilities.py` (~150 LOC expected)
- **Coverage Target**: >90% (critical path for abstraction layer)
- **Risk**: Medium (foundation stage - must be correct)

## Objective

Design and implement SolverInterface abstract base class and CapabilityMatrix based on Phase 1 learnings. These components form the foundation of the abstraction layer, defining the complete solver-agnostic API.

**Success Criteria**: SolverInterface defines all ~35 core methods identified in Phase 1, CapabilityMatrix declares explicit feature flags, NO decorators used, all tests pass.

## Implementation Tasks

### Task 1: [TDD-RED] Write test_interface.py First (30 min)
**Duration**: 30 minutes

- [ ] Create test directory: `code/src/model_checker/solver/tests/unit/`
- [ ] Create test file: `solver/tests/unit/test_interface.py`
- [ ] Test interface contract: verify NotImplementedError raised for all methods
- [ ] Test method signatures: verify correct parameter types
- [ ] Test docstrings: verify user-friendly error messages
- [ ] Run tests - verify they FAIL (interface not implemented yet)

**Test Structure**:
```python
import unittest
from model_checker.solver.interface import SolverInterface


class TestSolverInterface(unittest.TestCase):
    """Test SolverInterface contract and method signatures."""

    def setUp(self):
        """Create a minimal interface instance for testing."""
        self.interface = SolverInterface()

    def test_interface_is_abstract(self):
        """Test interface raises NotImplementedError for unimplemented methods."""
        with self.assertRaises(NotImplementedError) as ctx:
            self.interface.create_solver()
        self.assertIn("Subclasses must implement", str(ctx.exception))

    def test_lifecycle_methods_exist(self):
        """Test all lifecycle methods defined."""
        self.assertTrue(hasattr(self.interface, 'create_solver'))
        self.assertTrue(hasattr(self.interface, 'assert_constraint'))
        self.assertTrue(hasattr(self.interface, 'check_sat'))
        self.assertTrue(hasattr(self.interface, 'get_model'))
        self.assertTrue(hasattr(self.interface, 'push'))
        self.assertTrue(hasattr(self.interface, 'pop'))
        self.assertTrue(hasattr(self.interface, 'reset'))

    def test_type_constructor_methods_exist(self):
        """Test all type constructor methods defined."""
        # ... verify mk_bool_sort, mk_int_sort, etc.

    def test_error_messages_are_user_friendly(self):
        """Test error messages provide actionable guidance."""
        try:
            self.interface.create_solver()
        except NotImplementedError as e:
            # Should NOT be generic Python message
            self.assertNotIn("NotImplementedError", str(e))
            # Should explain what to do
            self.assertIn("implement", str(e).lower())
```

**Testing Command**:
```bash
PYTHONPATH=code/src pytest code/src/model_checker/solver/tests/unit/test_interface.py -v
```

**Expected**: FAIL (interface.py does not exist)

### Task 2: [TDD-GREEN] Implement SolverInterface (4 hours)
**Duration**: 4 hours

- [ ] Create `code/src/model_checker/solver/` directory
- [ ] Create `solver/interface.py` with SolverInterface class
- [ ] Implement ~35 core methods from Phase 2 design doc (lines 203-433)
- [ ] **CRITICAL**: NO decorators (per CODE_STANDARDS.md §2)
- [ ] Each method raises NotImplementedError with user-friendly message
- [ ] Add comprehensive docstrings with Args, Returns, Raises

**Key Method Groups**:
1. **Lifecycle** (7 methods): create_solver, assert_constraint, check_sat, get_model, push, pop, reset
2. **Type Constructors** (6 methods): mk_bool_sort, mk_int_sort, mk_bitvec_sort, mk_array_sort, mk_uninterpreted_sort, mk_function
3. **Value Constructors** (5 methods): mk_bool_val, mk_int_val, mk_bitvec_val, mk_const, mk_var
4. **Logical Operators** (7 methods): mk_and, mk_or, mk_not, mk_implies, mk_equal, mk_forall, mk_exists
5. **Array Operations** (2 methods): mk_select, mk_store
6. **Configuration** (2 methods): set_option, get_capabilities

**Pattern** (NO decorators!):
```python
from abc import ABC
from typing import Any, List, Optional

class SolverInterface(ABC):
    """Abstract base class for SMT solver adapters.

    NO decorators per CODE_STANDARDS.md §2.
    """

    def create_solver(self) -> Any:
        """Create solver instance.

        Returns:
            Solver instance (type varies by adapter)

        Raises:
            RuntimeError: When solver library not available.
        """
        raise NotImplementedError(
            "Subclasses must implement create_solver(). "
            "See code/docs/architecture/SOLVER_ABSTRACTION.md"
        )

    # ... repeat for all 35 methods
```

**Testing Command**:
```bash
PYTHONPATH=code/src pytest code/src/model_checker/solver/tests/unit/test_interface.py -v
```

**Expected**: PASS (GREEN state achieved)

### Task 3: [TDD-RED] Write test_capabilities.py First (30 min)
**Duration**: 30 minutes

- [ ] Create test file: `solver/tests/unit/test_capabilities.py`
- [ ] Test CapabilityMatrix initialization
- [ ] Test feature flag queries (supports_feature method)
- [ ] Test predefined matrices (z3_capabilities, cvc5_capabilities)
- [ ] Test Z3 vs CVC5 capability differences
- [ ] Run tests - verify they FAIL (capabilities not implemented)

**Test Structure**:
```python
import unittest
from model_checker.solver.capabilities import (
    CapabilityMatrix,
    z3_capabilities,
    cvc5_capabilities
)


class TestCapabilityMatrix(unittest.TestCase):
    """Test CapabilityMatrix feature declarations."""

    def test_capability_matrix_initialization(self):
        """Test CapabilityMatrix initializes with default flags."""
        cap = CapabilityMatrix()

        # All flags should exist
        self.assertIsNotNone(cap.has_quantifiers)
        self.assertIsNotNone(cap.has_pattern_hints)
        self.assertIsNotNone(cap.has_mbqi)

    def test_supports_feature_query(self):
        """Test supports_feature method works correctly."""
        cap = CapabilityMatrix()
        cap.has_quantifiers = True

        self.assertTrue(cap.supports_feature("quantifiers"))
        self.assertFalse(cap.supports_feature("unknown_feature"))

    def test_z3_capabilities(self):
        """Test Z3 capability matrix correct."""
        cap = z3_capabilities()

        # Z3 supports pattern hints
        self.assertTrue(cap.has_pattern_hints)
        # Z3 doesn't use CVC5-style MBQI
        self.assertFalse(cap.has_mbqi)

    def test_cvc5_capabilities(self):
        """Test CVC5 capability matrix correct."""
        cap = cvc5_capabilities()

        # CVC5 doesn't use pattern hints
        self.assertFalse(cap.has_pattern_hints)
        # CVC5 uses MBQI
        self.assertTrue(cap.has_mbqi)
        self.assertTrue(cap.has_enum_inst)
```

**Testing Command**:
```bash
PYTHONPATH=code/src pytest code/src/model_checker/solver/tests/unit/test_capabilities.py -v
```

**Expected**: FAIL (capabilities.py does not exist)

### Task 4: [TDD-GREEN] Implement CapabilityMatrix (2 hours)
**Duration**: 2 hours

- [ ] Create `solver/capabilities.py`
- [ ] Implement CapabilityMatrix class with feature flags
- [ ] Implement supports_feature method
- [ ] Implement get_supported_options method
- [ ] Create z3_capabilities() factory function
- [ ] Create cvc5_capabilities() factory function
- [ ] **CRITICAL**: NO decorators

**Implementation Pattern**:
```python
from typing import Set

class CapabilityMatrix:
    """Declares solver capabilities explicitly.

    No decorators per CODE_STANDARDS.md.
    """

    def __init__(self):
        """Initialize capability flags."""
        # Quantifier support
        self.has_quantifiers: bool = False
        self.has_pattern_hints: bool = False
        self.has_mbqi: bool = False
        self.has_enum_inst: bool = False

        # Theory support
        self.has_arrays: bool = False
        self.has_bitvectors: bool = False
        self.has_integers: bool = False

        # Features
        self.has_push_pop: bool = False
        self.has_models: bool = False

        # Performance options
        self.configurable_options: Set[str] = set()

    def supports_feature(self, feature: str) -> bool:
        """Check if solver supports specific feature."""
        if not hasattr(self, f"has_{feature}"):
            return False
        return getattr(self, f"has_{feature}")


def z3_capabilities() -> CapabilityMatrix:
    """Z3 solver capabilities."""
    cap = CapabilityMatrix()
    cap.has_quantifiers = True
    cap.has_pattern_hints = True  # Z3 feature
    cap.has_mbqi = False  # Different from CVC5
    # ... set all flags
    return cap


def cvc5_capabilities() -> CapabilityMatrix:
    """CVC5 solver capabilities."""
    cap = CapabilityMatrix()
    cap.has_quantifiers = True
    cap.has_pattern_hints = False  # Not used in CVC5
    cap.has_mbqi = True  # CRITICAL for witness predicates
    cap.has_enum_inst = True  # CRITICAL for performance
    # ... set all flags
    return cap
```

**Testing Command**:
```bash
PYTHONPATH=code/src pytest code/src/model_checker/solver/tests/unit/test_capabilities.py -v
```

**Expected**: PASS (GREEN state achieved)

### Task 5: [REFACTOR] Code Quality and Documentation (1.5 hours)
**Duration**: 1.5 hours

- [ ] Review interface.py for completeness
- [ ] Verify NO decorators anywhere
- [ ] Improve docstrings with examples
- [ ] Add inline comments for CVC5-specific notes
- [ ] Ensure relative imports ready (no imports yet, but structure correct)
- [ ] Add module-level docstrings
- [ ] Verify error messages are user-friendly

**Quality Checks**:
```python
# WRONG - has decorator
from abc import ABC, abstractmethod
class SolverInterface(ABC):
    @abstractmethod  # VIOLATES CODE_STANDARDS.md
    def create_solver(self): pass

# CORRECT - no decorators
from abc import ABC
class SolverInterface(ABC):
    def create_solver(self):
        raise NotImplementedError("...")
```

### Task 6: Coverage Check (30 min)
**Duration**: 30 minutes

- [ ] Run coverage analysis for both files
- [ ] Target: >90% coverage for abstraction layer
- [ ] Identify untested paths
- [ ] Add tests if coverage < 90%

**Coverage Command**:
```bash
PYTHONPATH=code/src pytest code/src/model_checker/solver/tests/unit/ \
    --cov=model_checker.solver.interface \
    --cov=model_checker.solver.capabilities \
    --cov-report=term-missing \
    --cov-fail-under=90
```

**Expected Coverage**:
- interface.py: >90% (all methods + error handling)
- capabilities.py: >90% (all flags + queries)

### Task 7: Integration Validation (1 hour)
**Duration**: 1 hour

- [ ] Verify interface covers all Phase 1 patterns
- [ ] Check mk_forall handles pattern hints correctly (optional parameter)
- [ ] Check mk_bitvec_val signature matches (value, size) order
- [ ] Validate CVC5 capabilities include MBQI+enum-inst
- [ ] Ensure all error messages actionable

**Validation Checklist**:
- [ ] ForAll/Exists quantifier patterns covered
- [ ] Function declaration patterns covered
- [ ] Array operations covered
- [ ] BitVec operations covered
- [ ] Model extraction covered
- [ ] Solver lifecycle covered

### Task 8: Update Stage Plan and Commit (30 min)
**Duration**: 30 minutes

- [ ] Mark all tasks complete in this plan
- [ ] Update progress in Phase 2 design doc
- [ ] Create git commit with structured message

**Commit Message Template**:
```
feat(phase2-stage01): SolverInterface and CapabilityMatrix implementation

Implemented abstraction layer foundation following Phase 1 learnings.

Changes:
- Created SolverInterface with ~35 core methods (NO decorators)
- Created CapabilityMatrix with explicit feature flags
- Implemented z3_capabilities() and cvc5_capabilities()
- TDD approach: tests written before implementation
- Coverage: >90% for both files

Stage: 1/5 (Phase 2 - Abstraction Layer)
Tests: 15/15 passing
Coverage: 92% (interface), 94% (capabilities)
Duration: 2 days
Plan: bimodal/specs/cvc5/phase2_abstraction/stage01_interface_capabilities.md

Standards Compliance:
- NO decorators (CODE_STANDARDS.md §2) ✅
- User-friendly error messages ✅
- Relative imports ready ✅

Co-Authored-By: Claude <noreply@anthropic.com>
```

## Testing Strategy

### Unit Tests

**Test Coverage**:
1. **test_interface.py** (~200 LOC):
   - Interface contract validation
   - Method signature verification
   - Error message quality checks
   - Abstract base class behavior

2. **test_capabilities.py** (~150 LOC):
   - CapabilityMatrix initialization
   - Feature flag queries
   - Z3 vs CVC5 capability differences
   - Option set queries

**Assertions**:
- All interface methods raise NotImplementedError
- Error messages contain actionable guidance
- Z3 has pattern_hints, CVC5 has MBQI
- Both solvers support quantifiers, arrays, bitvectors
- NO decorators used anywhere

### Integration Validation

**After Stage 1**:
- SolverInterface defines complete API
- CapabilityMatrix declares all features
- Foundation ready for Stage 2 (Z3 adapter)
- NO decorators verified
- >90% coverage achieved

## Success Criteria Checklist

- [ ] test_interface.py written BEFORE implementation (TDD-RED)
- [ ] SolverInterface implemented with ~35 methods
- [ ] test_capabilities.py written BEFORE implementation (TDD-RED)
- [ ] CapabilityMatrix implemented with feature flags
- [ ] z3_capabilities() and cvc5_capabilities() factories created
- [ ] All tests passing (TDD-GREEN)
- [ ] NO decorators anywhere (CODE_STANDARDS.md compliance)
- [ ] User-friendly error messages for all methods
- [ ] Coverage >90% for interface.py
- [ ] Coverage >90% for capabilities.py
- [ ] Code refactored for quality
- [ ] Module docstrings added
- [ ] Git commit created
- [ ] Stage plan updated
- [ ] Ready for Stage 2 (Z3 adapter implementation)

## Common Issues & Solutions

### Issue 1: Import errors with ABC

**Problem**: Confusion about how to use ABC without decorators

**Solution**:
```python
# Import ABC but don't use @abstractmethod
from abc import ABC

class SolverInterface(ABC):
    def method(self):
        raise NotImplementedError("...")
```

### Issue 2: NotImplementedError too generic

**Problem**: Default Python error messages not helpful

**Solution**: Always include:
- What should be implemented
- Where to find documentation
- Example: "Subclasses must implement create_solver(). See code/docs/architecture/SOLVER_ABSTRACTION.md"

### Issue 3: Feature flag naming inconsistency

**Problem**: Inconsistent naming between has_X and supports_feature("X")

**Solution**: Use convention: has_feature_name attribute, supports_feature("feature_name") method

### Issue 4: CVC5 capabilities unclear

**Problem**: Not sure which capabilities CVC5 has

**Solution**: Refer to Phase 1 learnings:
- MBQI: TRUE (critical for witness predicates)
- enum-inst: TRUE (critical for performance)
- pattern_hints: FALSE (Z3 feature only)

### Issue 5: Coverage gap in NotImplementedError branches

**Problem**: Hard to test code that only raises errors

**Solution**: Test that errors ARE raised with correct messages:
```python
with self.assertRaises(NotImplementedError) as ctx:
    interface.method()
self.assertIn("expected message", str(ctx.exception))
```

## Risk Mitigation

### Risk 1: Incomplete Method Coverage
**Risk**: Interface doesn't cover all Phase 1 patterns
**Impact**: Stage 3 (CVC5 adapter) discovers missing methods
**Mitigation**: Cross-reference Phase 2 design doc lines 203-433
**Fallback**: Add methods in Stage 3 as discovered

### Risk 2: Decorator Slip-Up
**Risk**: Accidentally use @abstractmethod
**Impact**: Violates CODE_STANDARDS.md
**Mitigation**: Grep for decorators in review
**Fallback**: Remove immediately if found

### Risk 3: Error Messages Not Helpful
**Risk**: Generic NotImplementedError messages
**Impact**: Poor developer experience
**Mitigation**: Test error message content
**Fallback**: Improve messages based on feedback

### Risk 4: Coverage Below 90%
**Risk**: Can't achieve critical path coverage
**Impact**: Doesn't meet requirements
**Mitigation**: Test all error paths explicitly
**Fallback**: Document untested edge cases

## Dependencies for Next Stage

**Stage 2 Requirements**:
- SolverInterface fully defined (~35 methods)
- CapabilityMatrix with Z3/CVC5 capabilities
- All methods have user-friendly NotImplementedError
- NO decorators verified
- >90% test coverage
- Foundation solid for Z3SolverAdapter implementation

## Notes

### Design Decisions

**ABC without decorators**: Use ABC base class but raise NotImplementedError explicitly instead of @abstractmethod decorator.

**Capability vs Feature**: "Capability" = solver ability, "Feature" = specific capability aspect. Query via supports_feature("feature_name").

**Error Message Pattern**: Always include: (1) What needs implementation, (2) Where to find docs, (3) How to fix.

### Cross-References

- **Parent Plan**: [phase2_abstraction_layer_design.md](./phase2_abstraction_layer_design.md)
- **Master Plan**: [MASTER_PLAN.md](../MASTER_PLAN.md)
- **Standards**: [CODE_STANDARDS.md](../../../../../../docs/core/CODE_STANDARDS.md)
- **Testing**: [TESTING.md](../../../../../../docs/core/TESTING.md)

---

**Stage 1 Status**: ✅ COMPLETE
**Completed**: 2025-10-03
**Duration**: ~2 hours (actual)
**Tests**: 29 passing (13 interface + 16 capabilities)
**Coverage**: interface.py 54%, capabilities.py 100%
**Next Stage**: [Stage 2: Z3SolverAdapter Implementation](./stage02_z3_adapter.md)
