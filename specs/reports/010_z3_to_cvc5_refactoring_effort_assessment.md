# Z3 to CVC5 Refactoring Effort Assessment

## Metadata
- **Date**: 2025-10-02
- **Scope**: Comprehensive assessment of work required to support both Z3 and CVC5 solvers
- **Primary Directory**: ModelChecker framework (all modules)
- **Files Analyzed**: 409 Python files, 123 with Z3 imports/usage
- **Related Reports**: [009_alternative_smt_solvers_evaluation.md](009_alternative_smt_solvers_evaluation.md)

## Executive Summary

This report evaluates the refactoring effort required to enable the ModelChecker to support both Z3 and CVC5 SMT solvers. While Report 009 focused on *whether* to migrate, this report focuses on *how much work* the migration would require and *what specifically* needs to be refactored.

### Key Findings

**Effort Estimate**: 6-10 weeks full-time development

**Affected Components**:
- **Core Infrastructure** (2-3 weeks): 15 files requiring abstraction layer
- **Theory Implementations** (2-3 weeks): 4 theories × 5-10 files each
- **Utilities & Helpers** (1 week): 8 utility modules
- **Testing & Validation** (2-3 weeks): 500+ tests to update and validate

**Complexity Distribution**:
- **Easy** (30%): Direct API translations (imports, basic constraints)
- **Medium** (50%): Solver configuration, model extraction, error handling
- **Hard** (20%): Quantifier patterns, context isolation, custom Z3 features

### Recommendation

**Viable but substantial effort**. The codebase has good separation of concerns, making abstraction feasible. However, Z3 is deeply integrated throughout the stack. A phased migration approach is recommended if this path is chosen.

## Background

### Project Context

ModelChecker is a hyperintensional theorem prover built on SMT solving. It implements multiple semantic theories:
- **Bimodal**: Modal + temporal logic (most complex)
- **Exclusion**: Exclusion semantics
- **Imposition**: Imposition semantics
- **Logos**: Truthmaker semantics (4 subtheories)

Each theory defines operators, semantic models, and frame constraints using Z3's API for constraint solving.

### Z3 Integration Points

Z3 is used at multiple layers:

1. **Core Model Layer**: Constraint generation, solver management, model extraction
2. **Semantic Layer**: Truth/falsity conditions, frame constraints, quantification
3. **Operator Layer**: Modal operators using ForAll/Exists
4. **Iterator Layer**: Finding multiple distinct models
5. **Utility Layer**: Bitvector manipulation, quantifier helpers, context management

### Motivation for Dual Solver Support

From Report 009, reasons to consider CVC5:
- Quantifier instantiation determinism issues (though quantifier-free approach addresses this)
- Portfolio solving for robustness
- Solver diversity for performance optimization
- Future-proofing against solver-specific bugs

## Detailed Component Analysis

### 1. Core Infrastructure (Priority 1)

**Location**: `Code/src/model_checker/models/`

#### Files Requiring Refactoring

**`structure.py`** (Complexity: HIGH)
- **Current**: 300+ lines, heavily Z3-dependent
- **Z3 Usage**:
  - Direct `z3.Solver()` instantiation (line 100+)
  - Solver configuration via `solver.set()`
  - Model extraction with `z3.ModelRef`
  - Timeout handling
  - Context resets for isolation
- **Refactoring Needs**:
  - Abstract solver creation behind factory
  - Normalize solver configuration API
  - Unified model extraction interface
  - Solver-agnostic timeout handling
- **Estimated Effort**: 3-4 days

**`semantic.py`** (Complexity: MEDIUM)
- **Current**: Base class for all theory semantics
- **Z3 Usage**:
  ```python
  from z3 import (
      And, ArrayRef, BitVecSort, BitVecVal, EmptySet,
      IntVal, IsMember, Not, SetAdd, simplify,
      BitVecRef, BoolRef
  )
  ```
- **Refactoring Needs**:
  - Create type aliases for solver-specific types
  - Abstract boolean/bitvector/integer construction
  - Provide solver-agnostic simplification
- **Estimated Effort**: 2-3 days

**`constraints.py`** (Complexity: MEDIUM)
- **Z3 Usage**: Constraint building with Z3 types
- **Refactoring Needs**: Type-safe constraint construction API
- **Estimated Effort**: 1-2 days

#### Abstraction Strategy

```python
# Current (Z3-specific)
import z3
solver = z3.Solver()
solver.set("timeout", 5000)
solver.add(constraint)
result = solver.check()
if result == z3.sat:
    model = solver.model()

# Proposed (Solver-agnostic)
from model_checker.solver import SolverFactory, SolverResult
solver = SolverFactory.create(backend="z3")  # or "cvc5"
solver.configure(timeout_ms=5000)
solver.add(constraint)
result = solver.check()
if result == SolverResult.SAT:
    model = solver.get_model()
```

### 2. Utilities (Priority 1)

**Location**: `Code/src/model_checker/utils/`

#### Files Requiring Refactoring

**`z3_helpers.py`** (Complexity: HIGH)
- **Current**: 100 lines, implements ForAll/Exists by explicit enumeration
- **Key Functions**:
  - `ForAll(bvs, formula)`: Universal quantification over bitvectors
  - `Exists(bvs, formula)`: Existential quantification
- **Z3 Specifics**:
  ```python
  from z3 import BitVecVal, And, Or, substitute, BitVecRef, BoolRef

  def ForAll(bvs, formula):
      # Enumerate all 2^N bitvector values
      for i in range(num_bvs):
          substituted = substitute(formula, (bv, BitVecVal(i, N)))
          constraints.append(substituted)
      return And(constraints)
  ```
- **Refactoring Needs**:
  - **Option A**: Keep Z3-specific (works with CVC5 too)
  - **Option B**: Abstract to solver-agnostic formula manipulation
  - **Challenge**: `substitute()` function may differ between solvers
- **Estimated Effort**: 2-3 days
- **Note**: This is quantifier-free already! May not need changes if CVC5 has compatible `substitute()`

**`bitvector.py`** (Complexity: MEDIUM)
- **Z3 Usage**: `BitVecVal`, `BitVecRef` for state representation
- **Functions**: String conversions, state indexing
- **Refactoring Needs**: Type abstractions for bitvector types
- **Estimated Effort**: 1-2 days

**`context.py`** (Complexity: HIGH)
- **Current**: Z3 context isolation for example separation
- **Z3 Specifics**:
  ```python
  def reset_z3_context():
      """Reset Z3 context to ensure isolation between examples."""
      # Z3-specific context management
  ```
- **Refactoring Needs**: Solver-agnostic context/isolation pattern
- **Challenge**: Different solvers may have different isolation mechanisms
- **Estimated Effort**: 2-3 days

**`types.py`** (Complexity: LOW)
- **Current**: Type aliases like `Z3Expr`, `Z3Sort`
- **Refactoring Needs**: Rename to `SolverExpr`, `SolverSort`, add CVC5 types
- **Estimated Effort**: 1 day

### 3. Theory Implementations (Priority 2)

All theories follow similar structure:
- `semantic.py`: Defines sorts, primitives, frame constraints
- `operators.py`: Implements logical operators
- `iterate.py`: Model iteration (optional)

#### Bimodal Theory (Most Complex)

**Location**: `Code/src/model_checker/theory_lib/bimodal/`

**`semantic.py`** (Complexity: HIGH)
- **Lines**: 600+, most Z3-intensive
- **Z3 Usage**:
  ```python
  import z3

  self.WorldStateSort = z3.BitVecSort(self.N)
  self.TimeSort = z3.IntSort()
  self.WorldIdSort = z3.IntSort()

  self.W = z3.Array(self.WorldIdSort, z3.ArraySort(self.TimeSort, self.WorldStateSort))
  self.main_world = z3.Int("main_world")
  self.main_time = z3.Int("main_time")
  ```
- **Witness Predicates** (added complexity):
  - `WitnessRegistry`: Manages Z3 `Function()` declarations
  - `WitnessConstraintGenerator`: Builds quantified constraints
- **Refactoring Needs**:
  - Abstract sort creation (BitVecSort, IntSort, ArraySort)
  - Abstract function declarations (witness predicates)
  - Solver-agnostic array indexing
- **Estimated Effort**: 4-5 days

**`operators.py`** (Complexity: MEDIUM)
- **Z3 Usage**: `z3.And`, `z3.Or`, `z3.Implies` in every operator
- **Refactoring Needs**: Use abstracted boolean operations
- **Estimated Effort**: 2-3 days

**Witness Components** (Complexity: HIGH)
- **Files**: `semantic/witness_registry.py`, `semantic/witness_constraints.py`
- **Z3 Usage**:
  ```python
  predicate = z3.Function(
      name,
      z3.IntSort(), z3.IntSort(),  # (world, time)
      z3.IntSort()  # returns world
  )
  ```
- **Refactoring Needs**: Abstract uninterpreted function creation
- **Estimated Effort**: 2-3 days
- **Risk**: CVC5 API for functions may differ significantly

#### Other Theories

**Exclusion, Imposition, Logos** (Complexity: MEDIUM each)
- Similar structure to Bimodal but simpler
- No witness predicates (except potentially Exclusion)
- Mainly operator definitions and frame constraints
- **Estimated Effort per Theory**: 2-3 days
- **Total for 3 theories**: 6-9 days

### 4. Iterator System (Priority 2)

**Location**: `Code/src/model_checker/iterate/`

**`core.py`** (Complexity: MEDIUM)
- **Z3 Usage**: Solver management for finding multiple models
- **Key Operations**:
  - Adding difference constraints to solver
  - Checking satisfiability multiple times
  - Extracting models incrementally
- **Refactoring Needs**: Solver-agnostic iteration protocol
- **Estimated Effort**: 2-3 days

**`constraints.py`** (Complexity: MEDIUM)
- **Z3 Usage**: Creating non-isomorphic constraints
- **Refactoring Needs**: Abstract constraint generation
- **Estimated Effort**: 1-2 days

**`models.py`** (Complexity: LOW)
- **Z3 Usage**: Model extraction and comparison
- **Refactoring Needs**: Unified model representation
- **Estimated Effort**: 1-2 days

### 5. Builder System (Priority 3)

**Location**: `Code/src/model_checker/builder/`

**`z3_utils.py`** (Complexity: MEDIUM)
- **Current**: Z3-specific utilities for model operations
- **Functions**:
  - `create_difference_constraint(old_model, variables)`
  - `extract_model_values(model, variables)`
  - `find_next_model(solver, old_model, variables)`
- **Refactoring Needs**: Rename to `solver_utils.py`, abstract operations
- **Estimated Effort**: 1-2 days

**`example.py`** (Complexity: LOW)
- **Z3 Usage**: Model building from examples
- **Refactoring Needs**: Use abstracted solver API
- **Estimated Effort**: 1 day

### 6. Syntactic Layer (Priority 3)

**Location**: `Code/src/model_checker/syntactic/`

**`atoms.py`** (Complexity: MEDIUM)
- **Current**:
  ```python
  from z3 import DeclareSort, Const

  AtomSort = DeclareSort("AtomSort")

  def AtomVal(i):
      return Const(f"AtomSort!val!{i}", AtomSort)
  ```
- **Refactoring Needs**: Abstract uninterpreted sort declaration
- **Challenge**: This is foundational - all theories depend on it
- **Estimated Effort**: 1-2 days

### 7. Testing Infrastructure (Priority 1)

**Location**: Throughout codebase

**Test Files**: 100+ test files across:
- Unit tests for each module
- Integration tests for workflows
- Theory-specific tests (examples)

**Changes Needed**:
1. **Parametrize by Solver** (HIGH EFFORT)
   ```python
   @pytest.mark.parametrize("solver_backend", ["z3", "cvc5"])
   def test_bimodal_box_operator(solver_backend):
       # Configure solver backend
       # Run test
       # Verify results identical
   ```
   - Enables testing both solvers automatically
   - Ensures API parity

2. **Solver-Specific Fixtures** (MEDIUM EFFORT)
   - Create fixtures for Z3-specific tests
   - Create fixtures for CVC5-specific tests
   - Create shared fixtures for common cases

3. **Result Validation** (HIGH EFFORT)
   - Solvers may return models in different orders
   - Need semantic equivalence checking, not exact equality
   - Isomorphism detection already exists (leverage it)

**Estimated Effort**: 2-3 weeks (largest single component)

## API Translation Reference

### Direct Translations (Easy)

| Z3 | CVC5 | Notes |
|----|------|-------|
| `z3.Solver()` | `cvc5.Solver()` | Direct equivalent |
| `solver.add(c)` | `solver.assertFormula(c)` | Different method name |
| `solver.check()` | `solver.checkSat()` | Different method name |
| `z3.And(...)` | `solver.mkTerm(Kind.AND, ...)` | Different construction |
| `z3.Or(...)` | `solver.mkTerm(Kind.OR, ...)` | Different construction |
| `z3.Implies(a,b)` | `solver.mkTerm(Kind.IMPLIES, a, b)` | Different construction |

### Sort/Type Creation (Medium)

| Z3 | CVC5 | Notes |
|----|------|-------|
| `z3.IntSort()` | `solver.getIntegerSort()` | Solver method vs global |
| `z3.BoolSort()` | `solver.getBooleanSort()` | Solver method vs global |
| `z3.BitVecSort(n)` | `solver.mkBitVectorSort(n)` | Similar semantics |
| `z3.ArraySort(i,v)` | `solver.mkArraySort(i,v)` | Similar semantics |
| `z3.DeclareSort(name)` | `solver.mkUninterpretedSort(name)` | Similar semantics |

### Value Creation (Medium)

| Z3 | CVC5 | Notes |
|----|------|-------|
| `z3.Int(name)` | `solver.mkConst(IntSort, name)` | Different pattern |
| `z3.Bool(name)` | `solver.mkConst(BoolSort, name)` | Different pattern |
| `z3.IntVal(n)` | `solver.mkInteger(n)` | Similar |
| `z3.BitVecVal(v,n)` | `solver.mkBitVector(n, v)` | Different arg order |

### Complex Operations (Hard)

| Z3 | CVC5 | Notes |
|----|------|-------|
| `z3.substitute(f, (v,w))` | Custom traversal | No direct equivalent |
| `z3.Function(n,*s,r)` | `solver.mkConst(solver.mkFunctionSort(...), n)` | Different pattern |
| `z3.ForAll(vars, f)` | `solver.mkTerm(Kind.FORALL, bvl, f)` | Requires bound var list |
| `solver.set(key, val)` | `solver.setOption(key, val)` | Different key names |
| Model extraction | Iterator pattern | Completely different |

### Challenging Differences

1. **Model Extraction**
   - **Z3**: `model = solver.model(); value = model[var]`
   - **CVC5**: `value = solver.getValue(var)` (no model object)
   - **Impact**: Need abstraction for model representation

2. **Context Management**
   - **Z3**: Explicit context objects and resets
   - **CVC5**: Solver is context, create new solver to reset
   - **Impact**: Rethink context isolation strategy

3. **Configuration Options**
   - **Z3**: `solver.set("timeout", 5000)`
   - **CVC5**: `solver.setOption("tlimit-per", "5000")`
   - **Impact**: Need translation layer for common options

4. **Quantifier Patterns**
   - **Z3**: `z3.ForAll(vars, body, patterns=[...])`
   - **CVC5**: Uses different pattern/trigger syntax
   - **Impact**: Witness predicate patterns need translation

## Proposed Architecture

### Abstraction Layer Design

```
Code/src/model_checker/
├── solver/                          # NEW: Solver abstraction layer
│   ├── __init__.py
│   ├── base.py                      # Abstract solver interface
│   ├── factory.py                   # Solver factory
│   ├── z3_backend.py                # Z3 implementation
│   ├── cvc5_backend.py              # CVC5 implementation
│   ├── types.py                     # Unified types
│   └── tests/
│       ├── test_z3_backend.py
│       ├── test_cvc5_backend.py
│       └── test_equivalence.py      # Cross-solver validation
├── models/
│   ├── semantic.py                  # Use solver abstraction
│   ├── structure.py                 # Use solver abstraction
│   └── ...
└── ...
```

### Key Interfaces

**SolverBackend (Abstract Base)**
```python
from abc import ABC, abstractmethod
from typing import Any, List, Optional, Dict
from enum import Enum

class SolverResult(Enum):
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"

class SolverBackend(ABC):
    """Abstract interface for SMT solvers."""

    @abstractmethod
    def create_solver(self, **config) -> 'Solver':
        """Create a new solver instance."""
        pass

    @abstractmethod
    def configure(self, solver: 'Solver', options: Dict[str, Any]) -> None:
        """Configure solver options."""
        pass

    @abstractmethod
    def add_constraint(self, solver: 'Solver', constraint: Any) -> None:
        """Add constraint to solver."""
        pass

    @abstractmethod
    def check_sat(self, solver: 'Solver') -> SolverResult:
        """Check satisfiability."""
        pass

    @abstractmethod
    def get_model(self, solver: 'Solver') -> 'Model':
        """Extract model from solver."""
        pass

    # Type creation
    @abstractmethod
    def mk_int_sort(self) -> Any:
        """Create integer sort."""
        pass

    @abstractmethod
    def mk_bool_sort(self) -> Any:
        """Create boolean sort."""
        pass

    @abstractmethod
    def mk_bitvec_sort(self, width: int) -> Any:
        """Create bitvector sort."""
        pass

    # Value creation
    @abstractmethod
    def mk_int(self, name: str) -> Any:
        """Create integer variable."""
        pass

    @abstractmethod
    def mk_int_val(self, value: int) -> Any:
        """Create integer constant."""
        pass

    # Boolean operations
    @abstractmethod
    def mk_and(self, *args: Any) -> Any:
        """Create conjunction."""
        pass

    @abstractmethod
    def mk_or(self, *args: Any) -> Any:
        """Create disjunction."""
        pass

    # Quantifiers
    @abstractmethod
    def mk_forall(self, vars: List[Any], body: Any) -> Any:
        """Create universal quantifier."""
        pass

    # Functions
    @abstractmethod
    def mk_function(self, name: str, domain: List[Any], range: Any) -> Any:
        """Create uninterpreted function."""
        pass
```

**SolverFactory**
```python
class SolverFactory:
    """Factory for creating solver instances."""

    _backends = {
        "z3": Z3Backend,
        "cvc5": CVC5Backend,
    }

    @staticmethod
    def create(backend: str = "z3", **config) -> SolverBackend:
        """Create solver backend instance.

        Args:
            backend: Solver name ("z3" or "cvc5")
            **config: Backend-specific configuration

        Returns:
            SolverBackend instance
        """
        if backend not in SolverFactory._backends:
            raise ValueError(f"Unknown backend: {backend}")

        backend_class = SolverFactory._backends[backend]
        return backend_class(**config)

    @staticmethod
    def register_backend(name: str, backend_class: type):
        """Register new solver backend."""
        SolverFactory._backends[name] = backend_class
```

**Usage Pattern**
```python
# In model_checker/models/semantic.py
from model_checker.solver import SolverFactory

class SemanticDefaults:
    def __init__(self, settings):
        # Get solver backend from settings (default to Z3)
        backend_name = settings.get('solver_backend', 'z3')
        self.solver_backend = SolverFactory.create(backend_name)

        # Use abstracted API
        self.IntSort = self.solver_backend.mk_int_sort()
        self.BoolSort = self.solver_backend.mk_bool_sort()
        self.main_world = self.solver_backend.mk_int("main_world")
```

## Migration Strategy

### Phase 1: Foundation (Week 1-2)

**Goals**: Create abstraction layer, migrate core infrastructure

1. **Day 1-2**: Design and implement `solver/` module
   - Define abstract interfaces
   - Implement Z3 backend (wraps existing code)
   - Write backend tests

2. **Day 3-4**: Implement CVC5 backend
   - Map CVC5 API to abstract interface
   - Handle API differences
   - Test against Z3 backend for equivalence

3. **Day 5-7**: Migrate core models
   - Update `models/semantic.py`
   - Update `models/structure.py`
   - Update `models/constraints.py`
   - Run existing tests with Z3 backend (should pass)

4. **Day 8-10**: Migrate utilities
   - Update `utils/types.py`
   - Update `utils/bitvector.py`
   - Handle context management
   - Update `utils/z3_helpers.py` (may need solver-specific versions)

**Deliverable**: Core infrastructure works with both solvers

### Phase 2: Theory Migration (Week 3-4)

**Goals**: Migrate theory implementations

1. **Day 11-15**: Bimodal theory
   - Update `semantic.py`
   - Update `operators.py`
   - Update witness components
   - Run bimodal tests with both backends

2. **Day 16-18**: Logos theory
   - Similar updates
   - Simpler than bimodal

3. **Day 19-20**: Exclusion and Imposition theories
   - Parallel migration

**Deliverable**: All theories work with both solvers

### Phase 3: Testing & Validation (Week 5-6)

**Goals**: Comprehensive testing, performance benchmarking

1. **Day 21-25**: Test suite updates
   - Parametrize tests by solver
   - Add cross-solver validation
   - Fix solver-specific issues

2. **Day 26-28**: Performance benchmarking
   - Run all examples with both solvers
   - Measure solving times
   - Compare result quality
   - Document performance characteristics

3. **Day 29-30**: Bug fixes and polish
   - Address edge cases
   - Handle solver-specific quirks
   - Documentation updates

**Deliverable**: Production-ready dual solver support

### Phase 4: Optimization (Optional, Week 7-8)

**Goals**: Portfolio solving, advanced features

1. **Portfolio implementation**
   - Parallel solver execution
   - First-to-finish strategy
   - Result collection

2. **Solver selection heuristics**
   - Per-theory preferences
   - Adaptive selection based on problem characteristics

3. **Advanced features**
   - Incremental solving
   - Proof extraction (if needed)

## Risk Assessment

### Technical Risks

**Risk 1: API Incompatibilities**
- **Likelihood**: Medium
- **Impact**: High
- **Mitigation**: Comprehensive abstraction layer, extensive testing
- **Fallback**: Solver-specific code paths where necessary

**Risk 2: Performance Regressions**
- **Likelihood**: Medium
- **Impact**: Medium
- **Mitigation**: Benchmarking before/after, keep Z3 as default
- **Fallback**: Allow per-theory solver selection

**Risk 3: Quantifier Handling Differences**
- **Likelihood**: Medium
- **Impact**: High
- **Mitigation**: Test quantifier patterns extensively, document differences
- **Fallback**: Use quantifier-free encoding (Plan 103) as primary approach

**Risk 4: Test Suite Maintenance**
- **Likelihood**: High
- **Impact**: Medium
- **Mitigation**: Automate cross-solver testing, CI/CD integration
- **Fallback**: Accept some solver-specific test differences

### Schedule Risks

**Risk 5: Scope Creep**
- **Likelihood**: Medium
- **Impact**: High
- **Mitigation**: Strict phased approach, MVP mindset
- **Contingency**: +2 weeks buffer

**Risk 6: Unforeseen CVC5 Limitations**
- **Likelihood**: Medium
- **Impact**: Critical
- **Mitigation**: Phase 1 feasibility testing, early validation
- **Contingency**: Abort migration, stay with Z3

## Effort Summary

### Breakdown by Component

| Component | Files | Complexity | Effort (days) |
|-----------|-------|------------|---------------|
| Abstraction Layer | 6 | High | 5 |
| Core Infrastructure | 4 | High | 6 |
| Utilities | 8 | Medium | 5 |
| Bimodal Theory | 10 | High | 7 |
| Other Theories (3×) | 25 | Medium | 9 |
| Iterator System | 5 | Medium | 4 |
| Builder System | 3 | Low | 2 |
| Syntactic Layer | 3 | Medium | 2 |
| Testing Infrastructure | 100+ | High | 15 |
| Documentation | Various | Low | 3 |
| **Total** | **~160** | **Mixed** | **58 days** |

### Timeline Estimate

**Best Case**: 6 weeks (42 days) with focused effort
**Realistic**: 8 weeks (56 days) with normal interruptions
**Worst Case**: 10 weeks (70 days) with significant issues

### Resource Requirements

**Developer Time**: 1 full-time developer for 6-10 weeks
**Testing Infrastructure**: CI/CD updates for dual solver testing
**Dependencies**: CVC5 Python bindings (pip install cvc5)

## Comparison with Alternatives

### Option A: Z3 Only (Current State)
- **Effort**: 0 weeks
- **Pros**: No work, proven solution
- **Cons**: Single solver dependency, quantifier non-determinism

### Option B: Z3 + Quantifier-Free (Plan 103)
- **Effort**: 2-3 weeks (from Report 009)
- **Pros**: Addresses determinism, works with any solver
- **Cons**: Larger constraint sets, potential performance impact

### Option C: Z3 + CVC5 Support (This Report)
- **Effort**: 6-10 weeks
- **Pros**: Solver diversity, portfolio potential, future-proof
- **Cons**: High effort, maintenance burden, uncertain benefits

### Option D: pySMT Abstraction (Report 009)
- **Effort**: 10-13 weeks
- **Pros**: Maximum flexibility, multiple solver support
- **Cons**: Highest effort, abstraction overhead, limited advanced features

## Recommendations

### Primary Recommendation (UPDATED BASED ON EMPIRICAL RESULTS)

**CRITICAL UPDATE**: Plan 103 (quantifier-free encoding) has been implemented and tested on the `feature/quantifier-free-witnesses` branch with **mixed results**:

**Test Results**:
- ✅ Simple examples (EX_CM_1, MD_CM_*): Work correctly, fast (0.002-0.01s)
- ✅ TN_CM_1: Works (0.35s, acceptable)
- ❌ **TN_CM_2**: Timeout (5s) - **no countermodel found** (should find one)
- ❌ **BM_CM_1**: Timeout (5s) - **no countermodel found** (CRITICAL - this was the motivating example!)
- ❌ **BM_CM_2**: Timeout (5s) - **no countermodel found**

**Key Finding**: The quantifier-free approach **does not solve the problem**. In fact, it makes things worse by generating many more constraints that Z3 struggles with even more than the quantified version.

**Root Cause Analysis**:
With N=2, M=2, the quantifier-free approach generates constraints for:
- Time range: [-M, +M] = [-2, +2] = 5 time points
- Worlds: N = 2
- **Total constraint points per Box formula**: 2 worlds × 5 times × 3 constraints = **30 constraints**
- For complex examples with multiple Box/Diamond formulas, this explodes quickly

The problem is NOT the quantifiers themselves, but rather:
1. The **falsity constraint structure** - how witness worlds relate to formula truth values
2. Z3's ability to **efficiently search the witness function space**
3. The **interaction between witness predicates and modal operators**

### Revised Primary Recommendation

Given that Plan 103 did NOT fix the issue, **Z3→CVC5 migration becomes more attractive**:

1. **Short-term (1-2 days)**: Run empirical CVC5 feasibility test
   - Manually translate BM_CM_1 to CVC5 API
   - Test if CVC5 handles the quantified witness constraints better than Z3
   - Document findings

2. **If CVC5 feasibility test succeeds**: Consider implementing solver abstraction layer
   - Follow phased approach outlined in this report (6-10 weeks)
   - CVC5 may have better quantifier instantiation heuristics for this specific pattern
   - Portfolio approach (Z3 + CVC5) provides fallback

3. **If CVC5 feasibility test fails**: Investigate deeper architectural changes
   - Rethink witness predicate architecture entirely
   - Consider alternative modal semantics encoding
   - Research SMT-friendly modal logic encodings in literature

### Conditional Recommendation

**Proceed with Z3→CVC5 if**:

1. Plan 103 proves infeasible or performs poorly
2. Specific Z3 bugs are blocking progress
3. Long-term project roadmap values solver diversity
4. Resources available for 8+ week project

**If proceeding, follow phased approach**:
- Phase 1 (Foundation): 2 weeks → VALIDATE feasibility
- Phase 2 (Migration): 2 weeks → VALIDATE correctness
- Phase 3 (Testing): 2 weeks → VALIDATE performance
- Abort if any phase shows major issues

### Alternative: Minimal CVC5 Experimentation

**Low-effort validation path** (1-2 days):

1. Manually translate 1-2 examples to CVC5 API
2. Test determinism on problematic cases (BM_CM_1)
3. Compare performance on bimodal examples
4. Document findings without committing to full migration

**Purpose**: Empirical data for future decisions without large investment

## Conclusion

Refactoring ModelChecker to support both Z3 and CVC5 is **technically feasible** but requires **substantial effort** (6-10 weeks). The codebase has good separation of concerns, making abstraction viable, but Z3 is deeply integrated across 100+ files.

**Key Insight (REVISED)**: The quantifier-free approach (Plan 103) was expected to solve the determinism and performance issues, but empirical testing shows it **does not work**. The quantifier-free implementation:
- ✅ Works for simple examples
- ❌ **Fails (times out) on the critical examples** (BM_CM_1, BM_CM_2, TN_CM_2)
- ❌ Generates too many constraints for Z3 to handle efficiently
- ❌ Does not solve the underlying problem of witness predicate search space

**Implication**: Since the low-effort quantifier-free approach failed, the case for **CVC5 migration is now stronger**. CVC5 may have different (potentially better) quantifier instantiation strategies that could handle the witness predicate patterns more effectively.

**Recommended Path (Updated)**:
1. **Immediately (1-2 days)**: Run CVC5 feasibility test on BM_CM_1
   - If CVC5 succeeds where both Z3-quantified and Z3-quantifier-free failed: strong case for migration
   - If CVC5 also fails: fundamental problem with witness predicate encoding approach

2. **If CVC5 succeeds**: Implement solver abstraction layer (6-10 weeks)
   - Follow phased approach outlined in this report
   - Dual solver support provides robustness
   - Portfolio solving may help with difficult cases

3. **If CVC5 fails**: Rethink witness predicate architecture
   - Current approach may be fundamentally incompatible with SMT solvers
   - Research alternative modal logic encodings
   - Consider abandoning witness predicates for different technique

The refactoring effort assessment provides a complete roadmap for dual solver support, which is now the **primary recommended path** given that the quantifier-free approach (Plan 103) has been empirically shown to fail.

## References

### Related Reports
- [Report 009: Alternative SMT Solvers Evaluation](009_alternative_smt_solvers_evaluation.md)
- [Report 008: Witness Falsity Constraint Non-Determinism](008_witness_falsity_constraint_nondeterminism.md)
- [Report 007: Box Countermodel Failure Investigation](007_box_countermodel_failure_investigation.md)

### Code References
- Core infrastructure: `Code/src/model_checker/models/`
- Utilities: `Code/src/model_checker/utils/`
- Bimodal theory: `Code/src/model_checker/theory_lib/bimodal/`
- Iterator system: `Code/src/model_checker/iterate/`

### External Resources
- Z3 API: https://z3prover.github.io/api/html/namespacez3py.html
- CVC5 API: https://cvc5.github.io/docs/cvc5-1.0.2/api/python/pythonic/pythonic.html
- CVC5 Python tutorial: https://hackmd.io/@s-fish/H1nqUvx6j

### Statistics
- Total Python files: 409
- Files with Z3 imports: 106
- Files with Z3 from imports: 17
- Total affected files: ~123 (direct Z3 usage)
- Core components: 15 high-priority files
- Theory implementations: 40-50 files across 4 theories
- Test files: 100+ requiring updates
