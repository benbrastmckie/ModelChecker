# Phase 2: Abstraction Layer Design and Implementation

## Metadata
- **Date**: 2025-10-02
- **Phase**: 2 of 3 (SMT Solver Abstraction Implementation)
- **Parent Plan**: [specs/plans/105_smt_solver_abstraction_REVISED.md](../../../../../specs/plans/105_smt_solver_abstraction_REVISED.md)
- **Prerequisite**: Phase 1 - Bimodal Theory CVC5 Pilot (MUST be complete)
- **Objective**: Create SolverInterface abstraction informed by Phase 1 pilot experience, following TDD
- **Complexity**: High
- **Estimated Duration**: 1.5 weeks
- **Branch**: `feature/solver-abstraction`
- **Standards**:
  - [CODE_STANDARDS.md](../../../../../docs/core/CODE_STANDARDS.md) - **CRITICAL: No decorators**
  - [TESTING.md](../../../../../docs/core/TESTING.md) - **>90% coverage for abstraction layer**
  - [ARCHITECTURE.md](../../../../../docs/core/ARCHITECTURE.md)

## Overview

### Strategic Context

**Phase 1 Deliverables** (Input to Phase 2):
- Complete CVC5-based bimodal theory (reference implementation)
- Documented Z3→CVC5 API translation patterns (~15 core patterns)
- Performance benchmarks (850× speedup on witness predicates)
- Identified abstraction points and solver-specific handling needs
- Pain points: pattern hints, operator overloading, API verbosity

**Phase 2 Goal**: Design and implement thin abstraction layer that:
1. Supports both Z3 and CVC5 backends transparently
2. Enables solver selection via settings configuration
3. Minimizes performance overhead (<5%)
4. Allows performance-critical paths to bypass abstraction
5. Makes future solver additions straightforward
6. Maintains 100% backward compatibility with existing Z3 code

**Key Design Principles** (from PySMT research + Phase 1 learnings):
1. **Thin Wrapper**: Direct API access for performance, minimal abstraction
2. **Explicit Capabilities**: Declare solver features upfront (quantifiers, MBQI, patterns)
3. **Adapter Pattern**: Separate formula representation from solver interaction
4. **No Decorators**: Follow CODE_STANDARDS.md - explicit methods only
5. **TDD-First**: All code has tests written before implementation

### Abstraction Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Theory Implementations                    │
│        (bimodal, exclusion, imposition, logos)              │
│         - Use SolverInterface methods only                  │
│         - Solver-agnostic constraint building               │
└────────────────────────┬────────────────────────────────────┘
                         │
                         │ Uses abstract interface
                         ▼
┌─────────────────────────────────────────────────────────────┐
│                    SolverInterface (ABC)                     │
│  ┌──────────────────────────────────────────────────────┐  │
│  │ Core Methods:                                         │  │
│  │  - create_solver() -> Solver                         │  │
│  │  - assert_constraint(solver, constraint)             │  │
│  │  - check_sat(solver) -> Result                       │  │
│  │  - get_model(solver) -> Model                        │  │
│  │                                                       │  │
│  │ Type Constructors:                                    │  │
│  │  - mk_bool_sort(), mk_int_sort(), mk_bitvec_sort()  │  │
│  │  - mk_function(name, domain, range)                  │  │
│  │  - mk_array_sort(index, element)                     │  │
│  │                                                       │  │
│  │ Logical Operators:                                    │  │
│  │  - mk_and(), mk_or(), mk_not(), mk_implies()        │  │
│  │  - mk_forall(), mk_exists()                          │  │
│  │                                                       │  │
│  │ Configuration:                                        │  │
│  │  - set_option(key, value)                            │  │
│  │  - get_capabilities() -> CapabilityMatrix            │  │
│  │                                                       │  │
│  │ **NO DECORATORS** (per CODE_STANDARDS.md)            │  │
│  └──────────────────────────────────────────────────────┘  │
└────────────────┬───────────────────────────┬────────────────┘
                 │                           │
         Implements                  Implements
                 ▼                           ▼
┌──────────────────────────────┐  ┌──────────────────────────────┐
│     Z3SolverAdapter          │  │    CVC5SolverAdapter         │
│  ┌──────────────────────┐    │  │  ┌──────────────────────┐    │
│  │ - Wraps Z3 API       │    │  │  │ - Wraps CVC5 API     │    │
│  │ - Handles patterns   │    │  │  │ - Handles MBQI opts  │    │
│  │ - Z3 optimizations   │    │  │  │ - CVC5 enum-inst     │    │
│  │ - User-friendly err  │    │  │  │ - User-friendly err  │    │
│  │ - NO DECORATORS      │    │  │  │ - NO DECORATORS      │    │
│  └──────────────────────┘    │  │  └──────────────────────┘    │
└──────────────┬───────────────┘  └──────────────┬───────────────┘
               │                                 │
         Direct API calls                  Direct API calls
               ▼                                 ▼
┌──────────────────────────────┐  ┌──────────────────────────────┐
│         Z3 Library           │  │       CVC5 Library           │
│  (import z3)                 │  │  (import cvc5)               │
└──────────────────────────────┘  └──────────────────────────────┘
```

### Existing Solver Infrastructure

**Current Z3 Utilities** (from research):
- `builder/z3_utils.py`: Model operations (difference constraints, value extraction)
- `utils/z3_helpers.py`: Quantifier expansion (ForAll/Exists via substitution)
- **105+ files** with direct Z3 API calls across theories, models, iterate, syntactic

**Phase 1 Patterns** (from bimodal CVC5 migration):
- Quantifiers: z3.ForAll with patterns → cvc5 ForAll with MBQI+enum-inst
- Functions: z3.Function → cvc5.mkConst(mkFunctionSort(...))
- Operators: z3.And/Or/Implies → cvc5.mkTerm(Kind.AND/OR/IMPLIES, ...)
- BitVecs: z3.BitVecVal(value, size) → cvc5.mkBitVector(size, value) [reversed!]

### Standards Compliance Requirements

**NO DECORATORS** (CODE_STANDARDS.md §2):
```python
# WRONG - Using decorators
from abc import ABC, abstractmethod

class SolverInterface(ABC):
    @abstractmethod  # VIOLATES CODE_STANDARDS.md
    def create_solver(self) -> Any:
        pass

# CORRECT - No decorators
class SolverInterface(ABC):
    def create_solver(self) -> Any:
        """Create solver instance."""
        raise NotImplementedError("Subclasses must implement create_solver()")
```

**Relative Imports** (CODE_STANDARDS.md §Import Organization):
```python
# WRONG - Absolute imports within solver package
from model_checker.solver.interface import SolverInterface

# CORRECT - Relative imports
from .interface import SolverInterface
from .capabilities import CapabilityMatrix
```

**User-Friendly Errors** (CODE_STANDARDS.md §Error Handling):
```python
# WRONG - Cryptic error
raise ValueError("Invalid solver")

# CORRECT - Helpful error with guidance
raise ValueError(
    f"Unknown solver: '{solver_name}'. "
    f"Available solvers: z3, cvc5\n"
    f"To add a solver, see Code/docs/architecture/SOLVER_ABSTRACTION.md"
)
```

**Test Coverage** (TESTING.md §3.1):
- **Abstraction layer**: >90% (critical path requirement)
- **Overall affected code**: >85%
- Run: `pytest --cov=model_checker.solver --cov-fail-under=90`

## Success Criteria

### Functional Requirements
- [ ] SolverInterface defines complete solver-agnostic API
- [ ] Z3SolverAdapter fully implements interface (backward compatible)
- [ ] CVC5SolverAdapter fully implements interface (using Phase 1 patterns)
- [ ] SolverFactory creates correct adapter based on settings
- [ ] Settings integration complete (smt_solver configuration)
- [ ] Both adapters pass equivalence tests on simple cases

### Quality Requirements
- [ ] **TDD Compliance**: ALL tests written BEFORE implementation
- [ ] **NO DECORATORS**: Verified throughout solver package
- [ ] **Relative imports**: All local imports use relative paths
- [ ] **Test coverage >90%**: Abstraction layer exceeds critical path requirement
- [ ] **User-friendly errors**: All error messages actionable with guidance

### Design Requirements
- [ ] Thin wrapper pattern: <5% performance overhead
- [ ] Capability matrix explicit: quantifiers, MBQI, patterns, theories
- [ ] Performance paths can bypass abstraction (direct API access)
- [ ] Future solver additions require minimal changes
- [ ] Z3 backward compatibility: 100% (no breaking changes)

## Technical Design

### Component Overview

**Core Components** (6 new files):
1. `solver/interface.py`: SolverInterface abstract base class
2. `solver/capabilities.py`: CapabilityMatrix for feature declarations
3. `solver/z3_adapter.py`: Z3SolverAdapter implementation
4. `solver/cvc5_adapter.py`: CVC5SolverAdapter implementation
5. `solver/factory.py`: SolverFactory for adapter creation
6. `solver/__init__.py`: Package exports

**Integration Points**:
- `settings/settings.py`: Add smt_solver configuration
- `builder/z3_utils.py`: Refactor into Z3SolverAdapter (optional Phase 2.5)
- `utils/z3_helpers.py`: Refactor into Z3SolverAdapter (optional Phase 2.5)

### SolverInterface Design

**File**: `Code/src/model_checker/solver/interface.py`

**Key Methods** (from Phase 1 learnings):

```python
"""Solver-agnostic interface for SMT solvers."""

from abc import ABC
from typing import Any, List, Optional, Tuple

class SolverInterface(ABC):
    """Abstract base class for SMT solver adapters.

    This interface defines solver-agnostic operations for theory implementations.
    All methods use explicit NotImplementedError (NO decorators per CODE_STANDARDS.md).

    Standards Compliance:
    - No decorators (CODE_STANDARDS.md §2)
    - User-friendly error messages
    - Comprehensive docstrings
    """

    # Lifecycle Methods
    def create_solver(self) -> Any:
        """Create solver instance.

        Returns:
            Solver instance (type varies by adapter)

        Raises:
            RuntimeError: When solver library not available.
                         "Z3 solver library not found. Install with: pip install z3-solver"
        """
        raise NotImplementedError("Subclasses must implement create_solver()")

    def assert_constraint(self, solver: Any, constraint: Any) -> None:
        """Assert constraint in solver.

        Args:
            solver: Solver instance from create_solver()
            constraint: Constraint in solver-specific format

        Raises:
            ValueError: When constraint invalid for this solver.
        """
        raise NotImplementedError("Subclasses must implement assert_constraint()")

    def check_sat(self, solver: Any) -> str:
        """Check satisfiability of asserted constraints.

        Args:
            solver: Solver instance

        Returns:
            "sat", "unsat", or "unknown"

        Raises:
            RuntimeError: When solver fails or times out.
        """
        raise NotImplementedError("Subclasses must implement check_sat()")

    def get_model(self, solver: Any) -> Any:
        """Extract model from satisfiable solver.

        Args:
            solver: Solver instance (must be SAT)

        Returns:
            Model object (type varies by adapter)

        Raises:
            ValueError: When solver not in SAT state.
                       "Cannot extract model: solver is UNSAT"
        """
        raise NotImplementedError("Subclasses must implement get_model()")

    def push(self, solver: Any) -> None:
        """Push solver context (save state)."""
        raise NotImplementedError("Subclasses must implement push()")

    def pop(self, solver: Any, num: int = 1) -> None:
        """Pop solver context (restore state)."""
        raise NotImplementedError("Subclasses must implement pop()")

    def reset(self, solver: Any) -> None:
        """Reset solver to initial state."""
        raise NotImplementedError("Subclasses must implement reset()")

    # Type Constructors
    def mk_bool_sort(self) -> Any:
        """Create Boolean sort."""
        raise NotImplementedError("Subclasses must implement mk_bool_sort()")

    def mk_int_sort(self) -> Any:
        """Create Integer sort."""
        raise NotImplementedError("Subclasses must implement mk_int_sort()")

    def mk_bitvec_sort(self, size: int) -> Any:
        """Create BitVector sort of given size."""
        raise NotImplementedError("Subclasses must implement mk_bitvec_sort()")

    def mk_array_sort(self, index_sort: Any, element_sort: Any) -> Any:
        """Create Array sort (index -> element)."""
        raise NotImplementedError("Subclasses must implement mk_array_sort()")

    def mk_uninterpreted_sort(self, name: str) -> Any:
        """Create uninterpreted sort with given name."""
        raise NotImplementedError("Subclasses must implement mk_uninterpreted_sort()")

    def mk_function(self, name: str, domain: List[Any], range: Any) -> Any:
        """Create function declaration.

        Args:
            name: Function name
            domain: List of argument sorts
            range: Return sort

        Returns:
            Function declaration (type varies by adapter)
        """
        raise NotImplementedError("Subclasses must implement mk_function()")

    # Value Constructors
    def mk_bool_val(self, value: bool) -> Any:
        """Create Boolean constant value."""
        raise NotImplementedError("Subclasses must implement mk_bool_val()")

    def mk_int_val(self, value: int) -> Any:
        """Create Integer constant value."""
        raise NotImplementedError("Subclasses must implement mk_int_val()")

    def mk_bitvec_val(self, value: int, size: int) -> Any:
        """Create BitVector constant value.

        IMPORTANT: Adapters normalize argument order.
        Z3 uses (value, size), CVC5 uses (size, value).
        This interface always uses (value, size) for consistency.
        """
        raise NotImplementedError("Subclasses must implement mk_bitvec_val()")

    def mk_const(self, sort: Any, name: str) -> Any:
        """Create constant (uninterpreted or variable).

        CVC5 distinction: Use this for constants.
        Z3: Same as declaring a variable.
        """
        raise NotImplementedError("Subclasses must implement mk_const()")

    def mk_var(self, sort: Any, name: str) -> Any:
        """Create variable (for quantifiers).

        CVC5 distinction: Use this for quantifier variables.
        Z3: Same as mk_const.
        """
        raise NotImplementedError("Subclasses must implement mk_var()")

    # Logical Operators
    def mk_and(self, *args: Any) -> Any:
        """Create conjunction (And)."""
        raise NotImplementedError("Subclasses must implement mk_and()")

    def mk_or(self, *args: Any) -> Any:
        """Create disjunction (Or)."""
        raise NotImplementedError("Subclasses must implement mk_or()")

    def mk_not(self, arg: Any) -> Any:
        """Create negation (Not)."""
        raise NotImplementedError("Subclasses must implement mk_not()")

    def mk_implies(self, lhs: Any, rhs: Any) -> Any:
        """Create implication (lhs => rhs)."""
        raise NotImplementedError("Subclasses must implement mk_implies()")

    def mk_equal(self, lhs: Any, rhs: Any) -> Any:
        """Create equality (lhs == rhs)."""
        raise NotImplementedError("Subclasses must implement mk_equal()")

    def mk_forall(self, vars: List[Any], body: Any, patterns: Optional[List[Any]] = None) -> Any:
        """Create universal quantifier.

        Args:
            vars: List of quantified variables (from mk_var)
            body: Quantifier body formula
            patterns: Optional pattern hints (Z3 only, CVC5 ignores)

        Note:
            Z3 uses pattern hints for quantifier instantiation.
            CVC5 relies on MBQI+enum-inst configuration instead.
            Adapters handle this difference transparently.
        """
        raise NotImplementedError("Subclasses must implement mk_forall()")

    def mk_exists(self, vars: List[Any], body: Any, patterns: Optional[List[Any]] = None) -> Any:
        """Create existential quantifier."""
        raise NotImplementedError("Subclasses must implement mk_exists()")

    # Array Operations
    def mk_select(self, array: Any, index: Any) -> Any:
        """Array select (array[index])."""
        raise NotImplementedError("Subclasses must implement mk_select()")

    def mk_store(self, array: Any, index: Any, value: Any) -> Any:
        """Array store (array[index] = value)."""
        raise NotImplementedError("Subclasses must implement mk_store()")

    # Configuration
    def set_option(self, solver: Any, key: str, value: str) -> None:
        """Set solver option.

        Args:
            solver: Solver instance
            key: Option name (solver-specific)
            value: Option value

        Note:
            Options are solver-specific. Use CapabilityMatrix
            to check which options are supported.
        """
        raise NotImplementedError("Subclasses must implement set_option()")

    def get_capabilities(self) -> 'CapabilityMatrix':
        """Get solver capability matrix.

        Returns:
            CapabilityMatrix declaring supported features.
        """
        raise NotImplementedError("Subclasses must implement get_capabilities()")
```

**Method Count**: ~35 core methods covering all Phase 1 patterns

### CapabilityMatrix Design

**File**: `Code/src/model_checker/solver/capabilities.py`

**Purpose**: Explicit feature declarations per solver

```python
"""Solver capability declarations."""

from typing import Dict, Set

class CapabilityMatrix:
    """Declares solver capabilities explicitly.

    No decorators - plain class per CODE_STANDARDS.md.
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
        self.has_reals: bool = False
        self.has_strings: bool = False

        # Features
        self.has_push_pop: bool = False
        self.has_unsat_core: bool = False
        self.has_models: bool = False

        # Performance options
        self.configurable_options: Set[str] = set()

    def supports_feature(self, feature: str) -> bool:
        """Check if solver supports specific feature.

        Args:
            feature: Feature name (e.g., "quantifiers", "mbqi")

        Returns:
            True if supported, False otherwise
        """
        if not hasattr(self, f"has_{feature}"):
            return False
        return getattr(self, f"has_{feature}")

    def get_supported_options(self) -> Set[str]:
        """Get set of configurable option names."""
        return self.configurable_options


# Predefined capability matrices
def z3_capabilities() -> CapabilityMatrix:
    """Z3 solver capabilities."""
    cap = CapabilityMatrix()
    cap.has_quantifiers = True
    cap.has_pattern_hints = True  # Z3 supports pattern hints
    cap.has_mbqi = False  # Z3 MBQI different from CVC5
    cap.has_enum_inst = False

    cap.has_arrays = True
    cap.has_bitvectors = True
    cap.has_integers = True
    cap.has_reals = True
    cap.has_strings = True

    cap.has_push_pop = True
    cap.has_unsat_core = True
    cap.has_models = True

    cap.configurable_options = {"timeout", "auto_config", "smt.mbqi"}
    return cap


def cvc5_capabilities() -> CapabilityMatrix:
    """CVC5 solver capabilities."""
    cap = CapabilityMatrix()
    cap.has_quantifiers = True
    cap.has_pattern_hints = False  # CVC5 doesn't use pattern hints
    cap.has_mbqi = True  # CVC5 MBQI is critical
    cap.has_enum_inst = True  # CVC5 enum-inst is critical

    cap.has_arrays = True
    cap.has_bitvectors = True
    cap.has_integers = True
    cap.has_reals = True
    cap.has_strings = True

    cap.has_push_pop = True
    cap.has_unsat_core = True
    cap.has_models = True

    cap.configurable_options = {"mbqi", "enum-inst", "produce-models"}
    return cap
```

### Z3SolverAdapter Implementation

**File**: `Code/src/model_checker/solver/z3_adapter.py`

**Strategy**: Thin wrapper around existing Z3 API (backward compatible)

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

    # Lifecycle
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

    # Type Constructors (direct Z3 API)
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

    def mk_function(self, name: str, domain: List[Any], range: Any) -> z3.FuncDeclRef:
        """Create function declaration."""
        return z3.Function(name, *domain, range)

    # Value Constructors
    def mk_bool_val(self, value: bool) -> z3.BoolRef:
        """Create Boolean value."""
        return z3.BoolVal(value)

    def mk_bitvec_val(self, value: int, size: int) -> z3.BitVecRef:
        """Create BitVector value.

        Z3 uses (value, size) order - matches interface.
        """
        return z3.BitVecVal(value, size)

    def mk_var(self, sort: Any, name: str) -> Any:
        """Create variable (same as const in Z3)."""
        return z3.Const(name, sort)

    # Logical Operators (direct delegation)
    def mk_and(self, *args: Any) -> z3.BoolRef:
        """Create And."""
        return z3.And(*args)

    def mk_or(self, *args: Any) -> z3.BoolRef:
        """Create Or."""
        return z3.Or(*args)

    def mk_forall(self, vars: List[Any], body: Any, patterns: Optional[List[Any]] = None) -> z3.QuantifierRef:
        """Create ForAll.

        Z3 supports pattern hints - use them if provided.
        """
        if patterns:
            return z3.ForAll(vars, body, patterns=patterns)
        return z3.ForAll(vars, body)

    # ... (remaining methods follow same pattern)

    def get_capabilities(self) -> CapabilityMatrix:
        """Get Z3 capabilities."""
        return self._capabilities
```

**Key Points**:
- Thin wrapper: Direct delegation to Z3 API
- Backward compatible: Same behavior as existing code
- User-friendly errors with installation guidance
- Pattern hints supported (Z3 feature)

### CVC5SolverAdapter Implementation

**File**: `Code/src/model_checker/solver/cvc5_adapter.py`

**Strategy**: Apply Phase 1 translation patterns

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

    # Lifecycle
    def create_solver(self) -> cvc5.Solver:
        """Create CVC5 solver with MBQI+enum-inst configuration."""
        try:
            solver = cvc5.Solver()
            solver.setLogic("ALL")
            solver.setOption("produce-models", "true")

            # CRITICAL for witness predicate performance (Phase 1 learnings)
            solver.setOption("mbqi", "true")
            solver.setOption("enum-inst", "true")

            return solver
        except Exception as e:
            raise RuntimeError(
                f"Failed to create CVC5 solver: {e}. "
                f"Check CVC5 installation and version compatibility."
            )

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

    # Type Constructors (CVC5 API)
    def mk_bool_sort(self) -> cvc5.Sort:
        """Create Boolean sort."""
        # Note: Need solver instance for sorts in CVC5
        # Store solver or pass as parameter - design decision
        raise NotImplementedError("CVC5 requires solver for sorts - design TBD")

    # Alternative: Store solver in adapter
    def _ensure_solver(self):
        """Ensure adapter has solver for sort creation."""
        if not hasattr(self, '_solver'):
            self._solver = self.create_solver()
        return self._solver

    def mk_bool_sort(self) -> cvc5.Sort:
        """Create Boolean sort."""
        solver = self._ensure_solver()
        return solver.getBooleanSort()

    def mk_int_sort(self) -> cvc5.Sort:
        """Create Integer sort."""
        solver = self._ensure_solver()
        return solver.getIntegerSort()

    def mk_bitvec_val(self, value: int, size: int) -> cvc5.Term:
        """Create BitVector value.

        CRITICAL: CVC5 uses (size, value) - REVERSE of Z3!
        Interface uses (value, size) for consistency.
        """
        solver = self._ensure_solver()
        return solver.mkBitVector(size, value)  # Note: reversed args!

    def mk_forall(self, vars: List[cvc5.Term], body: cvc5.Term, patterns: Optional[List[Any]] = None) -> cvc5.Term:
        """Create ForAll quantifier.

        CVC5 doesn't use pattern hints - relies on MBQI+enum-inst.
        Patterns parameter ignored (kept for interface compatibility).
        """
        solver = self._ensure_solver()
        var_list = solver.mkTerm(Kind.VARIABLE_LIST, *vars)
        return solver.mkTerm(Kind.FORALL, var_list, body)

    def mk_and(self, *args: cvc5.Term) -> cvc5.Term:
        """Create And."""
        solver = self._ensure_solver()
        return solver.mkTerm(Kind.AND, *args)

    # ... (remaining methods follow Phase 1 patterns)

    def get_capabilities(self) -> CapabilityMatrix:
        """Get CVC5 capabilities."""
        return self._capabilities
```

**Key Points**:
- Apply Phase 1 CVC5 patterns learned from bimodal migration
- MBQI+enum-inst configured automatically
- BitVec argument order normalized (value, size)
- Pattern hints ignored (CVC5 uses MBQI instead)
- User-friendly errors with CVC5-specific guidance

**Design Decision**: Store solver in adapter for sort creation (CVC5 requirement)

### SolverFactory Implementation

**File**: `Code/src/model_checker/solver/factory.py`

```python
"""Solver factory for creating adapter instances."""

from typing import Dict, Type

# Relative imports
from .interface import SolverInterface
from .z3_adapter import Z3SolverAdapter
from .cvc5_adapter import CVC5SolverAdapter


class SolverFactory:
    """Factory for creating solver adapter instances.

    No decorators per CODE_STANDARDS.md.
    """

    # Registry (no decorator needed!)
    _ADAPTERS: Dict[str, Type[SolverInterface]] = {
        "z3": Z3SolverAdapter,
        "cvc5": CVC5SolverAdapter,
    }

    def create(self, solver_name: str) -> SolverInterface:
        """Create solver adapter instance.

        Args:
            solver_name: Solver name ("z3" or "cvc5")

        Returns:
            Solver adapter instance

        Raises:
            ValueError: Invalid solver name
            RuntimeError: Solver library unavailable
        """
        if not solver_name:
            raise ValueError(
                f"Solver name cannot be empty. "
                f"Valid solvers: {', '.join(self._ADAPTERS.keys())}"
            )

        solver_name = solver_name.lower().strip()

        if solver_name not in self._ADAPTERS:
            available = ', '.join(sorted(self._ADAPTERS.keys()))
            raise ValueError(
                f"Unknown solver: '{solver_name}'. "
                f"Available solvers: {available}\n"
                f"To add a solver, see Code/docs/architecture/SOLVER_ABSTRACTION.md"
            )

        adapter_class = self._ADAPTERS[solver_name]

        try:
            return adapter_class()
        except Exception as e:
            raise RuntimeError(
                f"Failed to initialize {solver_name.upper()} adapter: {e}"
            ) from e
```

### Settings Integration

**File**: `Code/src/model_checker/settings/settings.py`

**Add solver configuration** (no decorators!):

```python
# WRONG - Using decorator
from dataclasses import dataclass

@dataclass  # VIOLATES CODE_STANDARDS.md
class Settings:
    smt_solver: str = "z3"

# CORRECT - No decorators
class Settings:
    """Model checker settings.

    No decorators per CODE_STANDARDS.md §2.
    """

    def __init__(self):
        """Initialize settings with defaults."""
        # Solver selection
        self.smt_solver = "z3"  # Options: "z3", "cvc5"

        # Solver-specific options
        self.z3_timeout = None
        self.z3_auto_config = True

        self.cvc5_mbqi = True  # Critical for witness predicates
        self.cvc5_enum_inst = True  # Critical for performance

        # Existing settings...
        self.N = 3
        self.max_time = 10

    def validate_solver(self) -> None:
        """Validate solver selection."""
        valid = ["z3", "cvc5"]
        if self.smt_solver not in valid:
            raise ValueError(
                f"Invalid solver: '{self.smt_solver}'. "
                f"Valid options: {', '.join(valid)}"
            )
```

## Implementation Phases

### Sub-Phase 2.1: Interface and Capabilities Design (2 days)

**Objective**: Design SolverInterface and CapabilityMatrix based on Phase 1 learnings

#### Tasks
- [ ] **[TDD] Write test_interface.py** (RED first)
  - File: `solver/tests/unit/test_interface.py`
  - Test: Interface contract and method signatures
  - Expected: FAIL (interface not implemented)

- [ ] **Implement SolverInterface**
  - File: `solver/interface.py`
  - Methods: ~35 core methods from Phase 1 patterns
  - Standards: NO decorators, user-friendly errors
  - Verify: Tests pass (GREEN)

- [ ] **[TDD] Write test_capabilities.py** (RED first)
  - File: `solver/tests/unit/test_capabilities.py`
  - Test: Capability flag declarations and queries
  - Expected: FAIL (capabilities not implemented)

- [ ] **Implement CapabilityMatrix**
  - File: `solver/capabilities.py`
  - Content: Feature flags, predefined matrices (z3_capabilities, cvc5_capabilities)
  - Standards: NO decorators
  - Verify: Tests pass (GREEN)

- [ ] **Refactor for quality**
  - Improve: Documentation, error messages
  - Verify: Tests pass

#### Testing
```bash
# TDD cycle for interface
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_interface.py -v

# TDD cycle for capabilities
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_capabilities.py -v

# Coverage check
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/ --cov=model_checker.solver --cov-report=term-missing
```

**Success Criteria**:
- Tests written BEFORE implementation
- Interface defines complete API (35+ methods)
- CapabilityMatrix declares all features
- NO decorators verified
- User-friendly error messages

### Sub-Phase 2.2: Z3SolverAdapter Implementation (2 days)

**Objective**: Implement Z3 adapter as thin wrapper (backward compatible)

#### Tasks
- [ ] **[TDD] Write test_z3_adapter.py** (RED first)
  - File: `solver/tests/unit/test_z3_adapter.py`
  - Test: All SolverInterface methods for Z3
  - Expected: FAIL (adapter not implemented)

- [ ] **Implement Z3SolverAdapter lifecycle methods**
  - Methods: create_solver, assert_constraint, check_sat, get_model, push, pop
  - Strategy: Direct delegation to Z3 API
  - Verify: Tests pass

- [ ] **Implement Z3SolverAdapter type constructors**
  - Methods: mk_bool_sort, mk_int_sort, mk_bitvec_sort, mk_array_sort, mk_function
  - Strategy: Direct Z3 API calls
  - Verify: Tests pass

- [ ] **Implement Z3SolverAdapter value constructors**
  - Methods: mk_bool_val, mk_int_val, mk_bitvec_val, mk_const, mk_var
  - Note: Z3 uses (value, size) for BitVec - matches interface
  - Verify: Tests pass

- [ ] **Implement Z3SolverAdapter logical operators**
  - Methods: mk_and, mk_or, mk_not, mk_implies, mk_equal, mk_forall, mk_exists
  - Pattern hints: Support via patterns parameter (Z3 feature)
  - Verify: Tests pass

- [ ] **Implement Z3SolverAdapter array operations**
  - Methods: mk_select, mk_store
  - Verify: Tests pass

- [ ] **Implement configuration and capabilities**
  - Methods: set_option, get_capabilities
  - Return: z3_capabilities()
  - Verify: Tests pass

- [ ] **Refactor for quality**
  - Improve: Error handling, documentation
  - Standards: Relative imports, no decorators
  - Verify: Tests pass

#### Testing
```bash
# TDD cycle for Z3 adapter
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_z3_adapter.py -v --cov=model_checker.solver.z3_adapter --cov-report=term-missing --cov-fail-under=90
```

**Success Criteria**:
- Tests written BEFORE implementation
- All interface methods implemented
- Backward compatible with existing Z3 code
- Test coverage >90% (critical path)
- NO decorators, relative imports

### Sub-Phase 2.3: CVC5SolverAdapter Implementation (3 days)

**Objective**: Implement CVC5 adapter using Phase 1 patterns

#### Tasks
- [ ] **[TDD] Write test_cvc5_adapter.py** (RED first)
  - File: `solver/tests/unit/test_cvc5_adapter.py`
  - Test: All SolverInterface methods for CVC5
  - Expected: FAIL (adapter not implemented)

- [ ] **Implement CVC5SolverAdapter lifecycle**
  - Methods: create_solver (with MBQI+enum-inst!), assert_constraint, check_sat, get_model
  - CRITICAL: Configure MBQI+enum-inst for witness predicates
  - Verify: Tests pass

- [ ] **Implement CVC5SolverAdapter type constructors**
  - Methods: mk_bool_sort, mk_int_sort, mk_bitvec_sort, mk_array_sort, mk_function
  - Design: Store solver in adapter (CVC5 requirement for sorts)
  - Verify: Tests pass

- [ ] **Implement CVC5SolverAdapter value constructors**
  - Methods: mk_bool_val, mk_int_val, mk_bitvec_val, mk_const, mk_var
  - CRITICAL: BitVec argument normalization (value, size) → (size, value)
  - CVC5 distinction: mk_const vs mk_var for quantifiers
  - Verify: Tests pass

- [ ] **Implement CVC5SolverAdapter logical operators**
  - Methods: mk_and, mk_or, mk_not, mk_implies, mk_equal
  - Translation: z3.And(*args) → solver.mkTerm(Kind.AND, *args)
  - Verify: Tests pass

- [ ] **Implement CVC5SolverAdapter quantifiers**
  - Methods: mk_forall, mk_exists
  - Pattern: VARIABLE_LIST term + ForAll/Exists Kind
  - Note: Pattern hints parameter IGNORED (use MBQI instead)
  - Verify: Tests pass

- [ ] **Implement CVC5SolverAdapter array operations**
  - Methods: mk_select, mk_store
  - Translation: solver.mkTerm(Kind.SELECT/STORE, ...)
  - Verify: Tests pass

- [ ] **Implement configuration and capabilities**
  - Methods: set_option, get_capabilities
  - Return: cvc5_capabilities()
  - Verify: Tests pass

- [ ] **Refactor for quality**
  - Improve: Error handling, CVC5-specific documentation
  - Standards: Relative imports, no decorators
  - Verify: Tests pass

#### Testing
```bash
# TDD cycle for CVC5 adapter
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py -v --cov=model_checker.solver.cvc5_adapter --cov-report=term-missing --cov-fail-under=90

# Validate MBQI+enum-inst configuration
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py::test_create_solver_configures_mbqi -v
```

**Success Criteria**:
- Tests written BEFORE implementation
- All interface methods implemented
- Phase 1 patterns applied correctly
- MBQI+enum-inst configured
- BitVec args normalized
- Test coverage >90%

### Sub-Phase 2.4: Factory and Integration (1.5 days)

**Objective**: Implement factory and integrate with settings

#### Tasks
- [ ] **[TDD] Write test_factory.py** (RED first)
  - File: `solver/tests/unit/test_factory.py`
  - Test: Factory creation logic, error cases
  - Expected: FAIL (factory not implemented)

- [ ] **Implement SolverFactory**
  - File: `solver/factory.py`
  - Method: create(solver_name) → SolverInterface
  - Validation: Check solver name, provide clear errors
  - Standards: NO decorators
  - Verify: Tests pass

- [ ] **[TDD] Write test_settings_integration.py** (RED first)
  - File: `settings/tests/test_settings_solver.py`
  - Test: Settings.smt_solver integration
  - Expected: FAIL (settings not updated)

- [ ] **Update Settings class**
  - File: `settings/settings.py`
  - Add: smt_solver field (default "z3")
  - Add: Solver-specific options
  - Standards: NO decorators (no @dataclass)
  - Verify: Tests pass

- [ ] **Create solver package __init__.py**
  - File: `solver/__init__.py`
  - Exports: SolverInterface, SolverFactory, CapabilityMatrix
  - Enable: `from model_checker.solver import SolverFactory`

- [ ] **[TDD] Write integration tests** (RED first)
  - File: `solver/tests/integration/test_adapter_equivalence.py`
  - Test: Z3 and CVC5 produce same results on simple cases
  - Expected: Initially fails until equivalence validated

- [ ] **Run equivalence tests**
  - Execute: Compare Z3 vs CVC5 on simple formulas
  - Validate: sat/unsat agreement
  - Document: Expected differences (if any)

#### Testing
```bash
# Factory tests
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_factory.py -v

# Settings integration
PYTHONPATH=Code/src pytest Code/src/model_checker/settings/tests/test_settings_solver.py -v

# Equivalence testing
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/integration/test_adapter_equivalence.py -v

# Full package coverage (must be >90%)
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/ --cov=model_checker.solver --cov-report=term-missing --cov-fail-under=90
```

**Success Criteria**:
- Factory creates correct adapters
- Settings integration complete
- Package exports clean
- Equivalence tests pass
- Coverage >90% for solver package

### Sub-Phase 2.5: Documentation and Validation (0.5 days)

**Objective**: Document abstraction layer and validate design

#### Tasks
- [ ] **Create solver package README**
  - File: `solver/README.md`
  - Content: Usage guide, adapter selection, capability matrix
  - Standards: No historical references

- [ ] **Update architecture documentation**
  - File: `Code/docs/architecture/SOLVER_ABSTRACTION.md` (new)
  - Content: Abstraction design, adding new solvers, performance notes
  - No historical references

- [ ] **Create Phase 2 results report**
  - File: `specs/reports/015_abstraction_layer_results.md`
  - Content:
    - Design decisions and rationale
    - Performance overhead analysis (<5% target)
    - Test coverage achieved (>90% goal)
    - API completeness validation
    - Recommendations for Phase 3

- [ ] **Validate design against Phase 1 learnings**
  - Review: Does abstraction handle all Phase 1 patterns?
  - Check: Witness predicates supported (MBQI+enum-inst)?
  - Verify: Pattern hints abstracted correctly?
  - Confirm: Performance paths available?

- [ ] **Run comprehensive test suite**
  - Execute: All solver package tests
  - Verify: >90% coverage achieved
  - Check: NO decorators in entire package
  - Validate: All imports relative within package

#### Documentation Standards
- No historical references (current state only)
- Clear examples for both Z3 and CVC5
- User-friendly error guidance
- Performance considerations documented

**Success Criteria**:
- Complete documentation created
- Phase 2 results report written
- Design validated against Phase 1 learnings
- Test suite passes with >90% coverage
- NO decorators verified throughout

## Risk Mitigation

### Risk 1: CVC5 Sort Creation Pattern
**Risk**: CVC5 requires solver for sort creation (different from Z3)
**Impact**: Design decision affects API ergonomics
**Mitigation**: Store solver in adapter, create on-demand
**Fallback**: Pass solver to sort methods (breaks interface uniformity)

### Risk 2: Performance Overhead
**Risk**: Abstraction layer adds >5% overhead
**Impact**: Defeats performance goals
**Mitigation**: Benchmark after implementation, optimize hot paths
**Fallback**: Provide bypass mechanism for critical paths

### Risk 3: Interface Incompleteness
**Risk**: Phase 1 patterns don't cover all use cases
**Impact**: Theory migrations discover missing methods
**Mitigation**: Add methods incrementally in Phase 3
**Fallback**: Document limitations, extend interface as needed

### Risk 4: Test Coverage Gap
**Risk**: Complex adapter logic hard to test to >90%
**Impact**: Doesn't meet critical path coverage requirement
**Mitigation**: Comprehensive unit + integration tests
**Fallback**: Document untested edge cases, manual validation

### Risk 5: Backward Compatibility Break
**Risk**: Z3 adapter changes existing behavior
**Impact**: Regression in existing code
**Mitigation**: Regression test suite, careful delegation
**Fallback**: Fix breaks immediately, validate against baseline

## Dependencies

### External Dependencies
- **Z3**: Already installed
- **CVC5**: Installed in Phase 0
- **pytest**: Testing framework

### Internal Dependencies
- **Phase 1**: MUST be complete (bimodal CVC5 pilot provides patterns)
- **Phase 1 deliverables**:
  - API translation patterns documented
  - CVC5 configuration validated (MBQI+enum-inst)
  - Performance benchmarks established
  - Pain points identified

### Branch Dependencies
- **Base branch**: `feature/bimodal-cvc5-pilot` (Phase 1 complete)
- **New branch**: `feature/solver-abstraction`
- **Merge target**: After Phase 2, prepare for Phase 3

## Progress Tracking

### Completion Checklist

#### Sub-Phase 2.1: Interface & Capabilities ☐
- [ ] test_interface.py written (RED)
- [ ] SolverInterface implemented (~35 methods)
- [ ] test_capabilities.py written (RED)
- [ ] CapabilityMatrix implemented
- [ ] Tests pass (GREEN)
- [ ] NO decorators verified

#### Sub-Phase 2.2: Z3SolverAdapter ☐
- [ ] test_z3_adapter.py written (RED)
- [ ] Lifecycle methods implemented
- [ ] Type constructors implemented
- [ ] Logical operators implemented
- [ ] Tests pass (GREEN)
- [ ] Coverage >90%

#### Sub-Phase 2.3: CVC5SolverAdapter ☐
- [ ] test_cvc5_adapter.py written (RED)
- [ ] Lifecycle with MBQI+enum-inst
- [ ] Type constructors (solver stored)
- [ ] BitVec normalization
- [ ] Quantifiers (VARIABLE_LIST pattern)
- [ ] Tests pass (GREEN)
- [ ] Coverage >90%

#### Sub-Phase 2.4: Factory & Integration ☐
- [ ] test_factory.py written (RED)
- [ ] SolverFactory implemented
- [ ] Settings updated (NO decorators)
- [ ] Package exports created
- [ ] Equivalence tests pass
- [ ] Coverage >90% for package

#### Sub-Phase 2.5: Documentation ☐
- [ ] Solver README created
- [ ] Architecture doc created
- [ ] Phase 2 results report written
- [ ] Design validated
- [ ] Test suite comprehensive

### Test Coverage Metrics

| Component | Target | Current | Status |
|-----------|--------|---------|--------|
| interface.py | >90% | - | ☐ |
| capabilities.py | >90% | - | ☐ |
| z3_adapter.py | >90% | - | ☐ |
| cvc5_adapter.py | >90% | - | ☐ |
| factory.py | >90% | - | ☐ |
| **Package Overall** | **>90%** | - | ☐ |

### Standards Compliance Checklist

- [ ] **NO decorators** anywhere in solver/ package
- [ ] **Relative imports** for all intra-package imports
- [ ] **User-friendly errors** with actionable guidance
- [ ] **TDD compliance** - all tests written first
- [ ] **Documentation** - no historical references

## Next Steps

**Upon Phase 2 Completion**:
1. ✓ Create Phase 2 results report
2. ✓ Update master plan with abstraction layer details
3. → Proceed to **Phase 3**: Bimodal Theory Abstraction Integration
4. Migrate bimodal from direct CVC5 to SolverInterface
5. Validate dual-solver support (Z3 and CVC5 through abstraction)

**Phase 3 Preview**:
- Migrate bimodal theory to use SolverInterface
- Test with both Z3 (regression) and CVC5 (performance)
- Create equivalence test suite
- Validate no performance degradation
- Update bimodal documentation

**Deliverables to Phase 3**:
- Complete abstraction layer (SolverInterface + adapters)
- Solver factory for runtime selection
- Settings integration for configuration
- >90% test coverage on abstraction layer
- Performance overhead analysis (<5%)
- Migration patterns documented for theory developers
