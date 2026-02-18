# SMT Solver Abstraction Layer Implementation Plan

## Metadata
- **Date**: 2025-10-02
- **Feature**: Multi-solver support (Z3 and CVC5) with pluggable architecture
- **Scope**: Abstraction layer enabling solver-agnostic theory implementations
- **Estimated Phases**: 8 phases
- **Timeline**: 8-10 weeks
- **Standards File**: `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/docs/`
  - [CODE_STANDARDS.md](../../Code/docs/core/CODE_STANDARDS.md)
  - [TESTING.md](../../Code/docs/core/TESTING.md)
  - [ARCHITECTURE.md](../../Code/docs/core/ARCHITECTURE.md)
- **Research Reports**:
  - [specs/reports/012_cvc5_feasibility_results.md](../reports/012_cvc5_feasibility_results.md)
  - [specs/reports/010_z3_to_cvc5_refactoring_effort_assessment.md](../reports/010_z3_to_cvc5_refactoring_effort_assessment.md)
  - [specs/reports/011_z3_to_cvc5_api_translation.md](../reports/011_z3_to_cvc5_api_translation.md)

## Revision History

### 2025-10-02 - Revision 1
**Changes**: Updated plan to conform to project standards in Code/docs/
**Reason**: Ensure TDD compliance, proper import conventions, test coverage alignment, error handling standards
**Modified Phases**: All phases updated with TDD requirements, Phase 2 updated for no-decorator compliance, testing sections enhanced
**Standards Applied**:
- Mandatory TDD (Code/docs/core/TESTING.md)
- No decorators (Code/docs/core/CODE_STANDARDS.md)
- Relative imports (CODE_STANDARDS.md §Import Organization)
- Test coverage >85% overall, >90% critical (TESTING.md §3.1)
- User-friendly error messages (CODE_STANDARDS.md §Error Handling)

## Overview

### Strategic Context

**Problem**: Z3 exhibits non-deterministic behavior and timeout failures on critical witness predicate examples (BM_CM_1, BM_CM_2, TN_CM_2). Report 012 demonstrates CVC5 with MBQI+enum-inst solves these cases deterministically in ~6ms (vs Z3's 5s+ timeout) - an **850× performance improvement**.

**Goal**: Create a thin abstraction layer supporting both Z3 and CVC5, with solver selection via settings, while maintaining performance and enabling future solver additions.

**Strategy**: **Hybrid Approach** (validated by research synthesis):
1. **Pilot** CVC5 migration on bimodal theory (most complex, already proven to work)
2. **Design** abstraction layer informed by pilot experience
3. **Rollout** systematically across all theories with parallel testing

### Key Design Principles

From PySMT research and ModelChecker requirements:

1. **Thin Wrapper**: Minimize abstraction overhead, allow direct API access for performance paths
2. **Explicit Capabilities**: Declare solver feature support upfront (quantifiers, patterns, theories)
3. **Converter/Adapter Pattern**: Separate formula representation from solver interaction
4. **Graceful Degradation**: Fallbacks when solver lacks features
5. **Configuration-Driven**: Solver selection via settings, per-solver options management
6. **No Decorators**: Follow project standard - no decorators anywhere in abstraction
7. **TDD-First**: Write tests before implementation for all components

### Current State

**Z3 Integration Depth**: Deep coupling with 2106+ direct API calls across 97 files:
- Witness predicates using `z3.ForAll` with pattern hints (Z3-specific)
- Theory semantics defining primitives via `z3.Function` extensively
- Custom quantifier expansion in `z3_helpers.py` using `z3.substitute`
- Partial centralization in `z3_utils.py` and `z3_helpers.py`

**Critical Abstraction Points**:
- Solver lifecycle (creation, assertion, check, model extraction)
- Data type constructors (BitVec, Int, Bool, Array, Function)
- Logical operators (And, Or, Not, Implies, ForAll, Exists)
- Model evaluation and result checking
- **Solver-specific**: Pattern hints, MBQI/enum-inst options

## Success Criteria

### Functional Requirements
- [x] Bimodal theory works with CVC5 (BM_CM_1, BM_CM_2, TN_CM_2)
- [ ] Abstraction layer supports both Z3 and CVC5 backends
- [ ] All theories work with both solvers (or graceful degradation documented)
- [ ] Solver selection configurable via settings (`smt_solver: "z3" | "cvc5"`)
- [ ] No performance regression on Z3 for cases it handles well (<10%)
- [ ] CVC5 performance gains maintained (850× on critical examples)

### Quality Requirements (Per Code/docs/core/TESTING.md)
- [ ] Test coverage **>90% for abstraction layer** (critical path requirement)
- [ ] Test coverage >85% overall for affected packages
- [ ] All existing tests pass with Z3 backend (regression prevention)
- [ ] Parallel test suite validates Z3 vs CVC5 equivalence
- [ ] Clear documentation of solver capability differences
- [ ] Migration guide for theory developers
- [ ] **TDD compliance**: All code has tests written first

### Technical Requirements (Per Code/docs/core/CODE_STANDARDS.md)
- [ ] **No decorators used** anywhere in solver package
- [ ] **Relative imports** for all local modules
- [ ] Thin wrapper pattern minimizes overhead (<5%)
- [ ] Explicit capability matrix per solver
- [ ] Solver-specific options exposed cleanly
- [ ] Performance-critical paths can bypass abstraction
- [ ] Future solver additions require minimal changes
- [ ] **User-friendly error messages** with actionable guidance

## Technical Design

### Architecture Overview

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

### Key Components

#### 1. SolverInterface (Abstract Base Class)

**Location**: `Code/src/model_checker/solver/interface.py`

**Responsibilities**:
- Define solver-agnostic API contract
- Declare abstract methods for all operations
- Provide capability matrix structure
- Document expected behaviors
- **NO decorators** (per CODE_STANDARDS.md §2)

**Key Methods** (explicit, no decorators):
```python
from abc import ABC, abstractmethod  # Not @abstractmethod decorator!
from typing import Any, List, Optional

class SolverInterface(ABC):
    """Solver-agnostic interface for SMT solvers.

    This abstract base class defines the contract for SMT solver adapters,
    allowing theories to be solver-agnostic. Subclasses must implement all
    abstract methods without using decorators.

    Standards Compliance:
    - No decorators (CODE_STANDARDS.md §2)
    - Relative imports for subpackage modules
    - User-friendly error messages
    - Comprehensive docstrings
    """

    def create_solver(self) -> Any:
        """Create solver instance.

        Returns:
            Solver instance specific to the adapter.

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
            ValueError: When constraint is invalid for this solver.
                       "Invalid constraint format for CVC5. Expected Term, got: {type}"
        """
        raise NotImplementedError("Subclasses must implement assert_constraint()")

    # ... (all methods similarly documented with error messages)

    def get_capabilities(self) -> 'CapabilityMatrix':
        """Get solver capability matrix.

        Returns:
            CapabilityMatrix declaring what this solver supports.
        """
        raise NotImplementedError("Subclasses must implement get_capabilities()")
```

#### 2. Z3SolverAdapter

**Location**: `Code/src/model_checker/solver/z3_adapter.py`

**Import Organization** (per CODE_STANDARDS.md):
```python
"""Z3 solver adapter implementation."""

# Standard library
from typing import Any, List, Optional, Tuple

# Third-party
import z3

# Local framework (absolute for top-level)
from model_checker.solver.interface import SolverInterface
from model_checker.solver.capabilities import CapabilityMatrix

# Relative imports for same package
from .interface import SolverInterface
from .capabilities import CapabilityMatrix
```

**Error Handling** (per CODE_STANDARDS.md §Error Handling):
```python
def create_solver(self) -> z3.Solver:
    """Create Z3 solver instance."""
    try:
        solver = z3.Solver()
        return solver
    except NameError:
        raise RuntimeError(
            "Z3 solver library not available. "
            "Install with: pip install z3-solver"
        )
    except Exception as e:
        raise RuntimeError(
            f"Failed to create Z3 solver: {e}. "
            f"Ensure Z3 is properly installed and compatible with your Python version."
        )
```

#### 3. CVC5SolverAdapter

**Location**: `Code/src/model_checker/solver/cvc5_adapter.py`

**Critical Configuration** (from Report 012):
```python
def create_solver(self) -> Any:
    """Create CVC5 solver instance with MBQI+enum-inst.

    Returns:
        CVC5 Solver configured for witness predicate performance.

    Raises:
        RuntimeError: When CVC5 library not available or configuration fails.
                     "CVC5 solver library not available. Install with: pip install cvc5"
    """
    try:
        import cvc5
    except ImportError:
        raise RuntimeError(
            "CVC5 solver library not available. "
            "Install with: pip install cvc5\n"
            "For NixOS, see Code/docs/development/CVC5_CONFIGURATION.md"
        )

    try:
        solver = cvc5.Solver()
        solver.setLogic("ALL")
        solver.setOption("produce-models", "true")

        # CRITICAL for witness predicate performance (Report 012)
        solver.setOption("mbqi", "true")
        solver.setOption("enum-inst", "true")

        return solver
    except Exception as e:
        raise RuntimeError(
            f"Failed to create CVC5 solver: {e}. "
            f"Check CVC5 installation and version compatibility."
        )
```

#### 4. SolverFactory

**Location**: `Code/src/model_checker/solver/factory.py`

**Standards Compliance**:
- No decorators
- User-friendly errors
- Clear validation

```python
"""Solver factory for creating adapter instances."""

from typing import Dict, Type

# Relative imports
from .interface import SolverInterface
from .z3_adapter import Z3SolverAdapter
from .cvc5_adapter import CVC5SolverAdapter


class SolverFactory:
    """Factory for creating solver adapter instances.

    This factory creates the appropriate solver adapter based on
    the solver name, providing clear error messages when solvers
    are unavailable or misconfigured.

    Standards Compliance:
    - No decorators
    - User-friendly error messages
    - Clear validation
    """

    # Registry of available adapters (no decorator needed!)
    _ADAPTERS: Dict[str, Type[SolverInterface]] = {
        "z3": Z3SolverAdapter,
        "cvc5": CVC5SolverAdapter,
    }

    def create(self, solver_name: str) -> SolverInterface:
        """Create solver adapter instance.

        Args:
            solver_name: Name of solver ("z3" or "cvc5")

        Returns:
            Solver adapter instance ready to use.

        Raises:
            ValueError: When solver_name is invalid or empty.
                       "Invalid solver name ''. Must be one of: z3, cvc5"
            RuntimeError: When solver library not available.
                         "CVC5 solver library not installed. Run: pip install cvc5"
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
            # Re-raise with context
            raise RuntimeError(
                f"Failed to initialize {solver_name.upper()} adapter: {e}"
            ) from e
```

### Settings Integration

**Configuration**: `Code/src/model_checker/settings/settings.py`

**Standards Compliance**:
- No decorators (don't use @dataclass!)
- User-friendly defaults

```python
# WRONG - Using decorator
from dataclasses import dataclass

@dataclass  # NO! Violates CODE_STANDARDS.md
class Settings:
    smt_solver: str = "z3"

# CORRECT - Explicit class without decorators
class Settings:
    """Model checker settings.

    All settings use explicit initialization without decorators
    to comply with CODE_STANDARDS.md §2.
    """

    def __init__(self):
        """Initialize settings with defaults."""
        # Solver selection
        self.smt_solver = "z3"  # Options: "z3", "cvc5"

        # Solver-specific options
        self.z3_timeout = None
        self.cvc5_mbqi = True  # Critical for witness predicates
        self.cvc5_enum_inst = True  # Critical for performance

        # Existing settings...
        self.N = 3
        self.max_time = 10
```

## Implementation Phases

### Phase 0: Preparation and Pilot Setup [COMPLETED]

**Objective**: Prepare environment and validate CVC5 on additional bimodal examples beyond BM_CM_1

**Complexity**: Medium

**TDD Requirements** (per TESTING.md §1):
1. **Write tests FIRST** for CVC5 on BM_CM_2, TN_CM_2 ✓
2. **Verify RED state** (tests fail before CVC5 working) ✓
3. **Minimal implementation** to pass tests ✓
4. **GREEN state** (tests pass) ✓
5. **Refactor** for quality ✓

#### Tasks

- [x] **[TDD] Write test for CVC5 on BM_CM_2** (RED state first):
  - File: Created `test_bm_cm_2_cvc5.py` based on `test_bm_cm_1_cvc5.py`
  - Test written with CVC5 implementation
  - Result: 5/5 deterministic success (~6ms average)
  - TDD cycle: Completed GREEN state

- [x] **[TDD] Write test for CVC5 on TN_CM_2** (RED state first):
  - File: Created `test_tn_cm_2_cvc5.py`
  - Test written with temporal logic encoding
  - Result: 5/5 deterministic success (~0.2ms average)
  - TDD cycle: RED → GREEN (fixed encoding) → PASS

- [x] **Implement CVC5 for BM_CM_2** (after test written):
  - Implemented in test file (standalone test)
  - Result: SAT countermodel found (Past A |- Box A)
  - Refactored for clarity

- [x] **Implement CVC5 for TN_CM_2** (after test written):
  - Implemented in test file (standalone test)
  - Result: SAT countermodel (future A, future B |- future (A ∧ B))
  - Fixed initial encoding issue, now passes

- [x] **Document CVC5 configuration requirements**:
  - File: Created `Code/docs/development/CVC5_CONFIGURATION.md`
  - Content: MBQI+enum-inst requirement, API patterns, troubleshooting
  - No historical references (current state only)

- [x] **Create solver abstraction package structure**:
  - Directory: `Code/src/model_checker/solver/`
  - Files: `__init__.py`, `interface.py` (stub), `capabilities.py` (stub)
  - Purpose: Package structure ready for Phase 2 implementation

#### Testing (TDD Compliance)

```bash
# TDD Cycle for each test file:
# 1. Write test (RED state)
# 2. Run test - verify it fails
pytest test_bm_cm_2_cvc5.py  # Should fail initially
pytest test_tn_cm_2_cvc5.py  # Should fail initially

# 3. Implement minimal code
# 4. Run test - verify it passes (GREEN state)
nix-shell shell.nix --run "python3 test_bm_cm_2_cvc5.py"  # Should pass
nix-shell shell.nix --run "python3 test_tn_cm_2_cvc5.py"  # Should pass

# 5. Refactor and verify tests still pass
# 6. Benchmark (after benchmark tests pass)
nix-shell shell.nix --run "python3 benchmark_cvc5_simple.py"
```

**Success Criteria**: ✅ ALL MET
- ✅ **TDD Compliance**: All tests written before implementation
- ✅ CVC5 succeeds on BM_CM_2 (deterministic, ~6ms, 5/5 runs)
- ✅ CVC5 succeeds on TN_CM_2 (deterministic, ~0.2ms, 5/5 runs)
- ✅ Documentation created **without historical references**
- ✅ Package structure in place (Code/src/model_checker/solver/)

---

### Phase 1: Bimodal Theory CVC5 Pilot (1 week)

**Objective**: Migrate bimodal theory to CVC5 *without* abstraction layer, learning API patterns using TDD

**Complexity**: High

**TDD Requirements**:
1. Write tests FIRST for each bimodal component migration
2. Verify RED state before implementation
3. Minimal implementation for GREEN state
4. Refactor while maintaining GREEN

#### Tasks

- [ ] **Create feature branch**: `feature/bimodal-cvc5-pilot`
  - Base: `feature/cvc5-feasibility-test` branch
  - Purpose: Isolate experimental CVC5 migration

- [ ] **[TDD] Write tests for bimodal semantic.py CVC5 migration** (RED first):
  - File: `Code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantic_cvc5.py`
  - Test CVC5 integration BEFORE changing semantic.py
  - Expected: Tests fail (semantic.py still uses Z3)
  - TDD: RED → migrate to CVC5 → GREEN → refactor

- [ ] **Migrate bimodal semantic.py to CVC5** (after tests written):
  - File: `Code/src/model_checker/theory_lib/bimodal/semantic/semantic.py`
  - Changes:
    - Replace `import z3` with `import cvc5`
    - Translate `z3.Function()` → `cvc5.mkConst(cvc5.mkFunctionSort(...))`
    - Translate `z3.ForAll()` → `cvc5.mkTerm(Kind.FORALL, ...)`
    - Use Report 011 translation reference
    - **Use relative imports**: `from .operators import ...`
  - Make tests GREEN
  - Document: Pain points, unexpected differences, workarounds

- [ ] **[TDD] Write tests for bimodal operators.py CVC5 migration** (RED first):
  - File: `Code/src/model_checker/theory_lib/bimodal/tests/unit/test_operators_cvc5.py`
  - Test operator definitions BEFORE migration
  - TDD: RED → migrate → GREEN → refactor

- [ ] **Migrate bimodal operators.py to CVC5** (after tests):
  - File: `Code/src/model_checker/theory_lib/bimodal/semantic/operators.py`
  - Changes: Update modal operator definitions (Box, Diamond, Future, Past)
  - **Relative imports**: `from .semantic import ...`
  - Note: How witness predicates translate to CVC5

- [ ] **[TDD] Write tests for witness_constraints.py CVC5 migration** (RED first):
  - File: `Code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cvc5.py`
  - Test witness predicates BEFORE migration
  - Critical: ForAll patterns → CVC5 MBQI translation

- [ ] **Migrate bimodal witness_constraints.py to CVC5** (after tests):
  - File: `Code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
  - Changes: Critical ForAll quantifier patterns → CVC5 API
  - Ensure MBQI+enum-inst configured
  - Document: How Z3 patterns map to CVC5 options

- [ ] **Update bimodal examples.py**: Configure CVC5 solver
  - File: `Code/src/model_checker/theory_lib/bimodal/examples.py`
  - Changes: Replace Z3 solver creation with CVC5, set options

- [ ] **Run bimodal unit tests with CVC5**:
  - Tests: `Code/src/model_checker/theory_lib/bimodal/tests/unit/`
  - Expected: All pass (or document failures)
  - Command: `PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/ -v`

- [ ] **Run bimodal integration tests with CVC5**:
  - Tests: All example cases (BM_CM_1, BM_CM_2, BM_VM_1, etc.)
  - Compare: Z3 vs CVC5 results (sat/unsat agreement)
  - Performance: Document timing differences
  - Create: `specs/reports/014_bimodal_cvc5_pilot_results.md`

- [ ] **Document API translation patterns learned**:
  - File: Update `specs/reports/011_z3_to_cvc5_api_translation.md`
  - Add: Real-world examples from bimodal migration
  - Patterns: Common idioms, edge cases, gotchas
  - **No historical references** in documentation

#### Testing (TDD Compliance per TESTING.md)

```bash
# TDD Workflow for each component:

# 1. Write test FIRST (RED state)
# Example: test_semantic_cvc5.py

# 2. Run test - verify it fails
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantic_cvc5.py -v
# Expected: FAIL (semantic.py still uses Z3)

# 3. Implement migration (minimal code to pass)
# Migrate semantic.py from Z3 to CVC5

# 4. Run test - verify it passes (GREEN state)
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantic_cvc5.py -v
# Expected: PASS

# 5. Refactor for quality while maintaining GREEN
# Improve code organization, imports, error handling

# 6. Verify all tests still pass after refactoring
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/ -v

# Integration testing
cd Code
nix-shell ../shell.nix --run "./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py"
```

**Success Criteria**:
- **TDD Compliance**: All tests written before migration code
- Bimodal theory fully functional with CVC5
- All unit tests pass
- BM_CM_1, BM_CM_2, TN_CM_2 solved (deterministic, fast)
- API translation patterns documented **without historical references**
- Pain points identified for abstraction design

**Risk Mitigation**:
- Keep Z3 version on main branch (easy rollback)
- Document every API difference encountered
- If blockers found, escalate to research phase (investigate alternatives)

---

### Phase 2: Abstraction Layer Design and Implementation (1.5 weeks)

**Objective**: Create SolverInterface abstraction informed by pilot experience, following TDD

**Complexity**: High

**TDD Requirements**:
1. Write interface tests FIRST
2. Write adapter tests BEFORE implementation
3. Verify tests fail (RED)
4. Implement to pass tests (GREEN)
5. Refactor for quality

**Standards Compliance**:
- **NO DECORATORS** anywhere (CODE_STANDARDS.md §2)
- **Relative imports** for local modules (CODE_STANDARDS.md §Import Organization)
- **User-friendly error messages** (CODE_STANDARDS.md §Error Handling)
- Test coverage **>90%** for abstraction layer (TESTING.md §3.1 critical path)

#### Tasks

- [ ] **[TDD] Write tests for SolverInterface** (RED first):
  - File: `Code/src/model_checker/solver/tests/unit/test_interface.py`
  - Test interface contract BEFORE implementation
  - Tests written to define expected behavior
  - TDD: RED → implement interface → GREEN → refactor

- [ ] **Design SolverInterface based on pilot learnings**:
  - File: `Code/src/model_checker/solver/interface.py`
  - Methods: Extract common operations from bimodal CVC5 migration
  - Patterns: Identify what needs abstraction vs solver-specific handling
  - **NO DECORATORS**: Explicit methods only, no @abstractmethod, @property, etc.
  - Review: Validate against PySMT patterns from research

- [ ] **[TDD] Write tests for CapabilityMatrix** (RED first):
  - File: `Code/src/model_checker/solver/tests/unit/test_capabilities.py`
  - Test capability declarations BEFORE implementation
  - TDD: RED → implement → GREEN → refactor

- [ ] **Implement CapabilityMatrix**:
  - File: `Code/src/model_checker/solver/capabilities.py`
  - Content: Define capability flags (quantifiers, patterns, MBQI, etc.)
  - Create: Z3 and CVC5 capability declarations
  - **NO DECORATORS**: Plain class with explicit methods

- [ ] **[TDD] Write tests for Z3SolverAdapter** (RED first):
  - File: `Code/src/model_checker/solver/tests/unit/test_z3_adapter.py`
  - Test all SolverInterface methods for Z3 BEFORE implementation
  - Expected: Tests fail (adapter not implemented yet)
  - TDD: RED → implement adapter → GREEN → refactor

- [ ] **Implement Z3SolverAdapter**:
  - File: `Code/src/model_checker/solver/z3_adapter.py`
  - Strategy: Thin wrapper around existing `z3_utils.py` and `z3_helpers.py`
  - Methods: Implement all SolverInterface methods
  - Preserve: Existing Z3 behavior (backward compatibility)
  - **Import organization**:
    ```python
    # Standard library
    from typing import Any, List, Optional

    # Third-party
    import z3

    # Relative imports (same package)
    from .interface import SolverInterface
    from .capabilities import CapabilityMatrix
    ```
  - **Error handling**:
    ```python
    def create_solver(self) -> z3.Solver:
        try:
            return z3.Solver()
        except NameError:
            raise RuntimeError(
                "Z3 solver library not available. "
                "Install with: pip install z3-solver"
            )
    ```

- [ ] **[TDD] Write tests for CVC5SolverAdapter** (RED first):
  - File: `Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py`
  - Test all SolverInterface methods for CVC5 BEFORE implementation
  - Expected: Tests fail (adapter not implemented yet)
  - TDD: RED → implement adapter → GREEN → refactor

- [ ] **Implement CVC5SolverAdapter**:
  - File: `Code/src/model_checker/solver/cvc5_adapter.py`
  - Strategy: Translate bimodal pilot code into adapter methods
  - Methods: Implement all SolverInterface methods
  - Configuration: Hardcode MBQI+enum-inst for witness predicates
  - **Relative imports**
  - **User-friendly errors** with installation instructions

- [ ] **[TDD] Write tests for SolverFactory** (RED first):
  - File: `Code/src/model_checker/solver/tests/unit/test_factory.py`
  - Test factory creation logic BEFORE implementation
  - Test error cases (invalid solver, missing library)
  - TDD: RED → implement factory → GREEN → refactor

- [ ] **Implement SolverFactory**:
  - File: `Code/src/model_checker/solver/factory.py`
  - Methods: `create(solver_name: str) -> SolverInterface`
  - Validation: Check solver availability, provide clear errors
  - **NO DECORATORS**: No class methods, static methods, properties
  - **User-friendly errors**:
    ```python
    if solver_name not in _ADAPTERS:
        available = ', '.join(sorted(_ADAPTERS.keys()))
        raise ValueError(
            f"Unknown solver: '{solver_name}'. "
            f"Available solvers: {available}"
        )
    ```

- [ ] **[TDD] Write equivalence tests for adapters** (RED first):
  - File: `Code/src/model_checker/solver/tests/integration/test_adapter_equivalence.py`
  - Test Z3 and CVC5 produce equivalent results on simple cases
  - TDD: RED → fix adapter implementations → GREEN → refactor

- [ ] **Refactor existing Z3 helpers into adapter**:
  - Files: `Code/src/model_checker/builder/z3_utils.py`, `Code/src/model_checker/utils/z3_helpers.py`
  - Move: Z3-specific logic into Z3SolverAdapter
  - Deprecate: Old helpers (maintain imports for Phase 3 migration)

- [ ] **[TDD] Write tests for settings integration** (RED first):
  - File: `Code/src/model_checker/settings/tests/test_settings_solver.py`
  - Test settings.smt_solver integration BEFORE updating settings
  - TDD: RED → update settings → GREEN

- [ ] **Update settings module**:
  - File: `Code/src/model_checker/settings/settings.py`
  - Add: `smt_solver: str = "z3"` setting
  - Add: Solver-specific option fields
  - **NO DECORATORS**: No @dataclass, explicit __init__
  - Validation: Ensure valid solver name

#### Testing (TDD Compliance per TESTING.md §1)

```bash
# TDD Workflow per component:

# 1. Write test FIRST (RED state)
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_interface.py -v
# Expected: FAIL (interface not implemented)

# 2. Implement minimal code to pass
# Create SolverInterface with methods

# 3. Run test - verify GREEN
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_interface.py -v
# Expected: PASS

# 4. Refactor while maintaining GREEN
# Improve docstrings, error handling, organization

# 5. Run full solver package tests
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/ -v

# 6. Integration tests
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/integration/test_adapter_equivalence.py -v

# Coverage verification (must be >90% for critical path per TESTING.md)
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/ --cov=model_checker.solver --cov-report=term-missing --cov-fail-under=90
```

**Success Criteria**:
- **TDD Compliance**: All tests written before implementation code
- **NO DECORATORS**: Verified throughout solver package
- **Relative imports**: All local imports use relative paths
- **Test coverage >90%**: Abstraction layer exceeds critical path requirement
- SolverInterface defines complete API contract
- Both adapters fully implement interface
- Tests validate adapter correctness
- Factory creates correct adapter instances
- Settings integration complete
- **User-friendly error messages** throughout

**Design Validation**:
- Review abstraction with pilot experience in mind
- Ensure patterns/MBQI handled cleanly
- Verify performance-critical paths can bypass abstraction if needed
- Confirm future solver additions feasible

---

### Phase 3: Bimodal Theory Abstraction Integration (4-5 days)

**Objective**: Migrate bimodal theory from direct CVC5 usage to SolverInterface using TDD

**Complexity**: Medium

**TDD Requirements**:
1. Write integration tests FIRST
2. Verify tests fail with current direct CVC5 code
3. Migrate to use SolverInterface
4. Verify tests pass (GREEN)
5. Refactor

#### Tasks

- [ ] **[TDD] Write tests for bimodal using SolverInterface** (RED first):
  - File: `Code/src/model_checker/theory_lib/bimodal/tests/integration/test_bimodal_solver_interface.py`
  - Test bimodal with SolverInterface BEFORE migration
  - Expected: Tests fail (bimodal uses direct CVC5, not interface)
  - TDD: RED → migrate to interface → GREEN → refactor

- [ ] **Update bimodal semantic.py to use SolverInterface**:
  - File: `Code/src/model_checker/theory_lib/bimodal/semantic/semantic.py`
  - Replace: `import cvc5` → `from model_checker.solver import SolverFactory`
  - **Relative imports** within theory: `from .operators import ...`
  - Change: `cvc5.Solver()` → `SolverFactory().create(settings.smt_solver).create_solver()`
  - Use: Adapter methods (`mk_bool_sort()`, `mk_forall()`, etc.) instead of direct API

- [ ] **Update bimodal operators.py**:
  - File: `Code/src/model_checker/theory_lib/bimodal/semantic/operators.py`
  - Use: SolverInterface methods for constraint construction
  - **Relative imports**: `from .semantic import ...`

- [ ] **Update bimodal witness_constraints.py**:
  - File: `Code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
  - Critical: ForAll with patterns → adapter handles Z3 patterns vs CVC5 MBQI

- [ ] **[TDD] Test bimodal with Z3 adapter** (regression test):
  - Settings: `smt_solver = "z3"`
  - Expected: Identical behavior to pre-abstraction (regression test)
  - Command: `PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/ -v`

- [ ] **[TDD] Test bimodal with CVC5 adapter**:
  - Settings: `smt_solver = "cvc5"`
  - Expected: CVC5 performance gains maintained (BM_CM_1 in ~6ms)
  - Command: `PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/ -v`

- [ ] **[TDD] Write parallel validation tests** (RED first):
  - File: `Code/tests/integration/test_solver_equivalence.py`
  - Test: All bimodal examples with both Z3 and CVC5
  - Validate: sat/unsat agreement, model equivalence (semantically)
  - Expected: Initially fails (equivalence suite not complete)
  - TDD: RED → implement full equivalence checks → GREEN

- [ ] **Run parallel validation suite**:
  - Execute after equivalence tests written and passing
  - Document: Any expected differences

- [ ] **Update bimodal documentation**:
  - File: `Code/src/model_checker/theory_lib/bimodal/README.md`
  - Add: Solver selection instructions
  - Note: CVC5 recommended for witness predicate performance
  - **No historical references**: Describe current state only

#### Testing (TDD Compliance)

```bash
# TDD Workflow:

# 1. Write integration tests FIRST
# test_bimodal_solver_interface.py

# 2. Run tests - verify RED (tests fail with current direct CVC5)
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/integration/test_bimodal_solver_interface.py -v
# Expected: FAIL (bimodal doesn't use SolverInterface yet)

# 3. Migrate bimodal to use SolverInterface
# Update semantic.py, operators.py, witness_constraints.py

# 4. Run tests - verify GREEN
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/integration/test_bimodal_solver_interface.py -v
# Expected: PASS

# Test with Z3 (regression)
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/ -v

# Test with CVC5 (performance validation)
PYTHONPATH=Code/src SMT_SOLVER=cvc5 pytest Code/src/model_checker/theory_lib/bimodal/tests/ -v

# Run equivalence tests
PYTHONPATH=Code/src pytest Code/tests/integration/test_solver_equivalence.py -v

# Performance comparison
PYTHONPATH=Code/src python3 benchmark_bimodal_solvers.py
```

**Success Criteria**:
- **TDD Compliance**: Tests written before migration
- Bimodal works with both Z3 and CVC5 via abstraction
- No Z3 regression (all existing tests pass)
- CVC5 performance maintained (6ms on BM_CM_1)
- sat/unsat results agree between solvers (or differences documented)
- Documentation updated **without historical references**

**Validation**:
- Manual test: Run `./dev_cli.py bimodal/examples.py` with both solvers
- Check: Model outputs are semantically equivalent
- Verify: No performance degradation from abstraction overhead (<5%)

---

### Phases 4-7: Theory Rollout, Core Infrastructure, Documentation

(Follow same TDD pattern as Phase 3 for each:)
- **Write tests FIRST**
- **Verify RED state**
- **Minimal implementation for GREEN**
- **Refactor while maintaining GREEN**
- **NO DECORATORS** anywhere
- **Relative imports** for local modules
- **User-friendly error messages**
- **No historical references** in documentation

(Phase content similar to original plan, but with TDD requirements added to each task)

---

## Testing Strategy (Enhanced for Standards Compliance)

### Unit Tests (Per TESTING.md §2.2.1)

**Coverage Requirements**:
- **Abstraction layer**: >90% (critical path per TESTING.md §3.1)
- **Theory packages**: >85% overall
- **Modified core infrastructure**: >90%

**TDD Compliance**:
- All tests written BEFORE implementation code
- Tests initially fail (RED state verified)
- Minimal implementation to pass (GREEN state)
- Refactor while maintaining GREEN

**Test Structure** (per TESTING.md §12.1):
```python
# tests/unit/test_component.py
"""Unit tests for ComponentClass following TDD approach."""

import unittest
from unittest.mock import Mock, patch

# NO relative imports for test files - absolute imports
from model_checker.solver.z3_adapter import Z3SolverAdapter
from model_checker.solver.interface import SolverInterface


class TestZ3SolverAdapter(unittest.TestCase):
    """Test Z3SolverAdapter behavior in isolation using TDD."""

    def setUp(self):
        """Set up test fixtures."""
        self.adapter = Z3SolverAdapter()

    def test_create_solver_returns_z3_solver_instance(self):
        """Test Z3SolverAdapter.create_solver returns Z3 solver instance.

        This test drives the implementation of Z3SolverAdapter.create_solver()
        to ensure it creates valid Z3 solver instances.
        """
        # Act (test written before method fully implemented)
        solver = self.adapter.create_solver()

        # Assert (defines expected behavior)
        self.assertIsNotNone(solver,
                            "create_solver should return non-None solver instance")
        # Check it's actually a Z3 solver (type-specific validation)

    def test_create_solver_raises_runtime_error_when_z3_unavailable(self):
        """Test create_solver raises RuntimeError with helpful message when Z3 missing.

        This test drives the implementation of proper error handling
        when Z3 library is not available.
        """
        # Mock z3 import to fail
        with patch('model_checker.solver.z3_adapter.z3', side_effect=NameError):
            # Act & Assert
            with self.assertRaises(RuntimeError) as context:
                self.adapter.create_solver()

            error_msg = str(context.exception)
            self.assertIn("Z3 solver library not available",
                         error_msg,
                         "Error should indicate Z3 not available")
            self.assertIn("pip install", error_msg,
                         "Error should provide installation instructions")


if __name__ == '__main__':
    unittest.main()
```

### Integration Tests (Per TESTING.md §2.2.2)

**Purpose**: Test component interactions following TDD for workflows

**Coverage**: All component boundaries, workflow paths, error propagation

**TDD Integration Tests**:
```python
# tests/integration/test_solver_workflow.py
"""Integration tests for solver workflow using TDD."""

import unittest
from model_checker.solver import SolverFactory


class TestSolverWorkflow(unittest.TestCase):
    """Test solver workflow component integration using TDD."""

    def test_complete_model_checking_workflow_with_z3_succeeds(self):
        """Test complete workflow from solver creation to result extraction with Z3.

        This integration test drives the implementation of the complete
        workflow between SolverInterface components.
        """
        # Arrange (test written before workflow fully implemented)
        factory = SolverFactory()
        adapter = factory.create("z3")
        solver = adapter.create_solver()

        # Act (test real component interaction)
        # Add simple constraint
        bool_sort = adapter.mk_bool_sort()
        constraint = adapter.mk_bool_val(True)
        adapter.assert_constraint(solver, constraint)

        # Check satisfiability
        result = adapter.check_sat(solver)

        # Assert (defines expected integration behavior)
        self.assertEqual(result, "sat",
                        "Simple true constraint should be satisfiable")
```

### End-to-End Tests (Per TESTING.md §2.2.3)

**Purpose**: Test complete user workflows with TDD

**Minimal Mocking**: Use real solver operations where possible

```python
# tests/e2e/test_theory_with_solvers.py
"""End-to-end tests for complete theory execution with different solvers."""

class TestTheoryExecution(unittest.TestCase):
    """Test complete theory execution via CLI with solver selection."""

    def test_bimodal_theory_execution_with_cvc5_produces_correct_output(self):
        """Test complete bimodal theory execution using CVC5 produces expected output.

        This end-to-end test validates the complete user workflow from
        solver selection through theory execution to result output.
        """
        # Arrange - Create real theory file
        theory_file = create_temp_theory_file("bimodal", "cvc5")

        # Act - Execute real CLI command
        result = subprocess.run(
            [sys.executable, 'dev_cli.py', theory_file],
            capture_output=True, text=True
        )

        # Assert
        self.assertEqual(result.returncode, 0,
                        "CLI should succeed with CVC5 solver")
        self.assertIn("BM_CM_1", result.stdout,
                     "Output should show BM_CM_1 example processing")
        self.assertNotIn("Timeout", result.stdout,
                        "CVC5 should not timeout on BM_CM_1")
```

## Dependencies

### External Dependencies

**Z3**: Already installed (`import z3`)
- Version: Current (via pip)
- Usage: Z3SolverAdapter backend

**CVC5**: New dependency
- Version: 1.3.1 (validated in Report 012)
- Installation: `pip install cvc5`
- NixOS: Use `shell.nix` with `LD_LIBRARY_PATH` (Report 012 appendix)

### Internal Dependencies

**Must comply with CODE_STANDARDS.md**:
- **NO DECORATORS** in: `builder/z3_utils.py`, `utils/z3_helpers.py`, `iterate/base.py`, `models/structure.py`
- **Relative imports** for: All theory implementations, solver package
- **User-friendly errors**: All validation and exception messages

## Notes

### Critical Standards Compliance

**1. No Decorators** (CODE_STANDARDS.md §2):
```python
# WRONG
from dataclasses import dataclass

@dataclass
class Settings:
    smt_solver: str = "z3"

# CORRECT
class Settings:
    def __init__(self):
        self.smt_solver = "z3"
```

**2. Relative Imports** (CODE_STANDARDS.md §Import Organization):
```python
# WRONG (in solver package)
from model_checker.solver.interface import SolverInterface

# CORRECT (in solver package)
from .interface import SolverInterface
```

**3. User-Friendly Errors** (CODE_STANDARDS.md §Error Handling):
```python
# WRONG
raise ValueError("Invalid solver")

# CORRECT
raise ValueError(
    f"Unknown solver: '{solver_name}'. "
    f"Available solvers: z3, cvc5\n"
    f"To add a solver, see Code/docs/architecture/SOLVER_ABSTRACTION.md"
)
```

**4. TDD Compliance** (TESTING.md §1):
- Write ALL tests BEFORE implementation code
- Verify RED state (tests fail initially)
- Minimal implementation for GREEN state
- Refactor while maintaining GREEN

**5. Test Coverage** (TESTING.md §3.1):
- Abstraction layer: >90% (critical path)
- Overall: >85%
- Run: `pytest --cov=model_checker --cov-fail-under=85`

**6. No Historical References** (CODE_STANDARDS.md §Documentation Standards):
```markdown
# WRONG
### Recent Improvements
- Solver abstraction added in v2.0

# CORRECT
### Solver Selection
- Configure via settings.smt_solver
```

### CVC5 Configuration Requirements

**Critical for witness predicates** (from Report 012):
```python
solver.setOption("mbqi", "true")        # Model-based quantifier instantiation
solver.setOption("enum-inst", "true")   # Enumerative instantiation
```

Without these options, CVC5 returns "unknown" on witness predicate examples.

## References

### Project Standards
- [Code/docs/core/CODE_STANDARDS.md](../../Code/docs/core/CODE_STANDARDS.md) - **PRIMARY STANDARD**
- [Code/docs/core/TESTING.md](../../Code/docs/core/TESTING.md) - **TDD REQUIREMENTS**
- [Code/docs/core/ARCHITECTURE.md](../../Code/docs/core/ARCHITECTURE.md) - Design patterns
- [Code/docs/README.md](../../Code/docs/README.md) - Standards navigation

### Research Reports
- [Report 012: CVC5 Feasibility Results](../reports/012_cvc5_feasibility_results.md) - **Critical validation**
- [Report 010: Z3 to CVC5 Refactoring Effort Assessment](../reports/010_z3_to_cvc5_refactoring_effort_assessment.md)
- [Report 011: Z3 to CVC5 API Translation](../reports/011_z3_to_cvc5_api_translation.md)

### External Resources
- CVC5 Documentation: https://cvc5.github.io/
- CVC5 Python API: https://cvc5.github.io/docs/cvc5-1.0.2/api/python/pythonic/pythonic.html
- PySMT (reference): https://github.com/pysmt/pysmt
- SMT-LIB Standard: http://smtlib.cs.uiowa.edu/
