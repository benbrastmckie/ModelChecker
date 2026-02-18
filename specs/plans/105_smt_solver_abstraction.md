# SMT Solver Abstraction Layer Implementation Plan

## Metadata
- **Date**: 2025-10-02
- **Feature**: Multi-solver support (Z3 and CVC5) with pluggable architecture
- **Scope**: Abstraction layer enabling solver-agnostic theory implementations
- **Estimated Phases**: 8 phases
- **Timeline**: 8-10 weeks
- **Standards File**: `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/CLAUDE.md`
- **Research Reports**:
  - [specs/reports/012_cvc5_feasibility_results.md](../reports/012_cvc5_feasibility_results.md)
  - [specs/reports/010_z3_to_cvc5_refactoring_effort_assessment.md](../reports/010_z3_to_cvc5_refactoring_effort_assessment.md)
  - [specs/reports/011_z3_to_cvc5_api_translation.md](../reports/011_z3_to_cvc5_api_translation.md)

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

### Quality Requirements
- [ ] Test coverage >85% for abstraction layer
- [ ] All existing tests pass with Z3 backend (regression prevention)
- [ ] Parallel test suite validates Z3 vs CVC5 equivalence
- [ ] Clear documentation of solver capability differences
- [ ] Migration guide for theory developers

### Technical Requirements
- [ ] Thin wrapper pattern minimizes overhead
- [ ] Explicit capability matrix per solver
- [ ] Solver-specific options exposed cleanly
- [ ] Performance-critical paths can bypass abstraction
- [ ] Future solver additions require minimal changes

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
│  │ - Legacy API compat  │    │  │  │ - Term construction  │    │
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

**Key Methods**:
```python
class SolverInterface(ABC):
    @abstractmethod
    def create_solver(self) -> Any: ...

    @abstractmethod
    def assert_constraint(self, solver: Any, constraint: Any) -> None: ...

    @abstractmethod
    def check_sat(self, solver: Any) -> SatResult: ...

    @abstractmethod
    def get_model(self, solver: Any) -> Optional[Any]: ...

    @abstractmethod
    def mk_bool_sort(self) -> Any: ...

    @abstractmethod
    def mk_forall(self, vars: List[Any], body: Any,
                  patterns: Optional[List[Any]] = None) -> Any: ...

    @abstractmethod
    def get_capabilities(self) -> CapabilityMatrix: ...
```

#### 2. Z3SolverAdapter

**Location**: `Code/src/model_checker/solver/z3_adapter.py`

**Responsibilities**:
- Implement SolverInterface for Z3
- Wrap existing Z3 API calls
- Maintain current Z3 behavior (backward compatibility for pilot)
- Handle Z3-specific features (patterns for quantifiers)

**Strategy**: Initially **thin wrapper** around existing Z3 code in `z3_utils.py` and `z3_helpers.py`

#### 3. CVC5SolverAdapter

**Location**: `Code/src/model_checker/solver/cvc5_adapter.py`

**Responsibilities**:
- Implement SolverInterface for CVC5
- Translate Z3 patterns to CVC5 API
- Configure MBQI + enum-inst by default for witness predicates
- Handle CVC5 term construction verbosity

**Configuration**:
```python
def create_solver(self) -> cvc5.Solver:
    solver = cvc5.Solver()
    solver.setLogic("ALL")
    solver.setOption("produce-models", "true")
    solver.setOption("mbqi", "true")        # Critical for witness predicates
    solver.setOption("enum-inst", "true")   # Critical for performance
    return solver
```

#### 4. SolverFactory

**Location**: `Code/src/model_checker/solver/factory.py`

**Responsibilities**:
- Create solver adapter instances based on settings
- Validate solver availability
- Provide fallback strategies
- Handle solver registration

```python
class SolverFactory:
    @staticmethod
    def create(solver_name: str) -> SolverInterface:
        if solver_name == "z3":
            return Z3SolverAdapter()
        elif solver_name == "cvc5":
            return CVC5SolverAdapter()
        else:
            raise UnsupportedSolverError(f"Unknown solver: {solver_name}")
```

#### 5. CapabilityMatrix

**Location**: `Code/src/model_checker/solver/capabilities.py`

**Responsibilities**:
- Declare what each solver supports
- Enable runtime feature detection
- Guide theory implementations on solver compatibility

```python
@dataclass
class CapabilityMatrix:
    quantifiers: bool
    quantifier_patterns: bool  # Z3: yes, CVC5: no (uses MBQI instead)
    uninterpreted_functions: bool
    arrays: bool
    bitvectors: bool
    incremental: bool
    model_extraction: bool
    unsat_cores: bool

    # Solver-specific
    supports_mbqi: bool
    supports_enum_inst: bool
```

### Migration Path: Hybrid Approach

**Phase 1: Pilot (Bimodal Theory)**
- Validate CVC5 on bimodal (most complex theory)
- Learn API pain points empirically
- Document translation patterns
- **Risk**: Low - Report 012 proves BM_CM_1 works

**Phase 2: Abstraction Design**
- Create SolverInterface based on pilot learnings
- Design Z3SolverAdapter wrapping existing code
- Design CVC5SolverAdapter based on pilot
- **Risk**: Low - informed by real experience

**Phase 3: Systematic Rollout**
- Implement abstraction in core infrastructure
- Migrate theories one-by-one (bimodal first, then others)
- Run parallel tests (Z3 vs CVC5) after each migration
- **Risk**: Medium - incremental validation reduces risk

### Settings Integration

**Configuration**: `Code/src/model_checker/settings/settings.py`

Add new setting:
```python
@dataclass
class Settings:
    # ... existing settings ...
    smt_solver: str = "z3"  # Options: "z3", "cvc5"

    # Solver-specific options
    z3_timeout: Optional[int] = None
    cvc5_mbqi: bool = True
    cvc5_enum_inst: bool = True
```

**Usage in theories**:
```python
# Before abstraction:
import z3
solver = z3.Solver()

# After abstraction:
from model_checker.solver import SolverFactory
from model_checker.settings import settings

adapter = SolverFactory.create(settings.smt_solver)
solver = adapter.create_solver()
```

## Implementation Phases

### Phase 0: Preparation and Pilot Setup (3-4 days)

**Objective**: Prepare environment and validate CVC5 on additional bimodal examples beyond BM_CM_1

**Complexity**: Medium

#### Tasks

- [ ] **Test CVC5 on BM_CM_2**: Run test_bm_cm_1_cvc5.py adapted for BM_CM_2 example
  - File: Create `test_bm_cm_2_cvc5.py` based on `test_bm_cm_1_cvc5.py`
  - Expected: CVC5 succeeds where Z3 times out
  - Validates: CVC5 works on multiple bimodal examples

- [ ] **Test CVC5 on TN_CM_2**: Run on temporal-only example (no modal operators)
  - File: Create `test_tn_cm_2_cvc5.py`
  - Expected: CVC5 succeeds (simpler case)
  - Validates: CVC5 handles temporal logic correctly

- [ ] **Benchmark simple cases with CVC5**: Test on examples Z3 handles well
  - File: Adapt `Code/src/model_checker/theory_lib/bimodal/examples.py` simple cases
  - Expected: CVC5 no performance regression (<10% slower acceptable)
  - Validates: CVC5 doesn't break working cases

- [ ] **Document CVC5 configuration requirements**: Based on Report 012 findings
  - File: Create `Code/docs/development/CVC5_CONFIGURATION.md`
  - Content: MBQI+enum-inst requirement, option reference, troubleshooting
  - Purpose: Standard setup for witness predicates

- [ ] **Create solver abstraction package structure**:
  - Directory: `Code/src/model_checker/solver/`
  - Files: `__init__.py`, `interface.py` (stub), `capabilities.py` (stub)
  - Purpose: Establish package for Phase 1 implementation

#### Testing

```bash
# Run CVC5 tests on additional examples
nix-shell shell.nix --run "python3 test_bm_cm_2_cvc5.py"
nix-shell shell.nix --run "python3 test_tn_cm_2_cvc5.py"

# Benchmark simple cases (create script)
nix-shell shell.nix --run "python3 benchmark_cvc5_simple.py"

# Verify all pass
```

**Success Criteria**:
- CVC5 succeeds on BM_CM_2, TN_CM_2 (deterministic, <100ms)
- CVC5 simple case performance within 10% of Z3
- Documentation created and reviewed
- Package structure in place

---

### Phase 1: Bimodal Theory CVC5 Pilot (1 week)

**Objective**: Migrate bimodal theory to CVC5 *without* abstraction layer, learning API patterns

**Complexity**: High

#### Tasks

- [ ] **Create feature branch**: `feature/bimodal-cvc5-pilot`
  - Base: `feature/cvc5-feasibility-test` branch
  - Purpose: Isolate experimental CVC5 migration

- [ ] **Migrate bimodal semantic.py to CVC5**:
  - File: `Code/src/model_checker/theory_lib/bimodal/semantic/semantic.py`
  - Changes:
    - Replace `import z3` with `import cvc5`
    - Translate `z3.Function()` → `cvc5.mkConst(cvc5.mkFunctionSort(...))`
    - Translate `z3.ForAll()` → `cvc5.mkTerm(Kind.FORALL, ...)`
    - Use Report 011 translation reference
  - Document: Pain points, unexpected differences, workarounds

- [ ] **Migrate bimodal operators.py to CVC5**:
  - File: `Code/src/model_checker/theory_lib/bimodal/semantic/operators.py`
  - Changes: Update modal operator definitions (Box, Diamond, Future, Past)
  - Note: How witness predicates translate to CVC5

- [ ] **Migrate bimodal witness_constraints.py to CVC5**:
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

#### Testing

```bash
# Set PYTHONPATH and run bimodal tests
cd /home/benjamin/Documents/Philosophy/Projects/ModelChecker
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/ -v

# Run specific examples
cd Code
nix-shell ../shell.nix --run "./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py"

# Compare Z3 (main branch) vs CVC5 (pilot branch) results
# Create comparison script: compare_z3_cvc5_bimodal.py
```

**Success Criteria**:
- Bimodal theory fully functional with CVC5
- All unit tests pass
- BM_CM_1, BM_CM_2, TN_CM_2 solved (deterministic, fast)
- API translation patterns documented
- Pain points identified for abstraction design

**Risk Mitigation**:
- Keep Z3 version on main branch (easy rollback)
- Document every API difference encountered
- If blockers found, escalate to research phase (investigate alternatives)

---

### Phase 2: Abstraction Layer Design and Implementation (1.5 weeks)

**Objective**: Create SolverInterface abstraction informed by pilot experience

**Complexity**: High

#### Tasks

- [ ] **Design SolverInterface based on pilot learnings**:
  - File: `Code/src/model_checker/solver/interface.py`
  - Methods: Extract common operations from bimodal CVC5 migration
  - Patterns: Identify what needs abstraction vs solver-specific handling
  - Review: Validate against PySMT patterns from research

- [ ] **Implement CapabilityMatrix**:
  - File: `Code/src/model_checker/solver/capabilities.py`
  - Content: Define capability flags (quantifiers, patterns, MBQI, etc.)
  - Create: Z3 and CVC5 capability declarations

- [ ] **Implement Z3SolverAdapter**:
  - File: `Code/src/model_checker/solver/z3_adapter.py`
  - Strategy: Thin wrapper around existing `z3_utils.py` and `z3_helpers.py`
  - Methods: Implement all SolverInterface methods
  - Preserve: Existing Z3 behavior (backward compatibility)

- [ ] **Refactor existing Z3 helpers into adapter**:
  - Files: `Code/src/model_checker/builder/z3_utils.py`, `Code/src/model_checker/utils/z3_helpers.py`
  - Move: Z3-specific logic into Z3SolverAdapter
  - Deprecate: Old helpers (maintain imports for Phase 3 migration)

- [ ] **Implement CVC5SolverAdapter**:
  - File: `Code/src/model_checker/solver/cvc5_adapter.py`
  - Strategy: Translate bimodal pilot code into adapter methods
  - Methods: Implement all SolverInterface methods
  - Configuration: Hardcode MBQI+enum-inst for witness predicates

- [ ] **Implement SolverFactory**:
  - File: `Code/src/model_checker/solver/factory.py`
  - Methods: `create(solver_name: str) -> SolverInterface`
  - Validation: Check solver availability, provide clear errors
  - Registration: Allow future solver additions

- [ ] **Create abstraction layer tests**:
  - Directory: `Code/src/model_checker/solver/tests/unit/`
  - Tests: Test both adapters implement SolverInterface correctly
  - Coverage: >85% for abstraction layer
  - Validation: Z3 and CVC5 produce equivalent results on simple cases

- [ ] **Update settings module**:
  - File: `Code/src/model_checker/settings/settings.py`
  - Add: `smt_solver: str = "z3"` setting
  - Add: Solver-specific option fields
  - Validation: Ensure valid solver name

#### Testing

```bash
# Test abstraction layer
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/ -v

# Test both adapters equivalence
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_equivalence.py -v

# Verify settings integration
PYTHONPATH=Code/src python3 -c "from model_checker.settings import settings; print(settings.smt_solver)"
```

**Success Criteria**:
- SolverInterface defines complete API contract
- Both adapters fully implement interface
- Tests validate adapter correctness
- Factory creates correct adapter instances
- Settings integration complete

**Design Validation**:
- Review abstraction with pilot experience in mind
- Ensure patterns/MBQI handled cleanly
- Verify performance-critical paths can bypass abstraction if needed
- Confirm future solver additions feasible

---

### Phase 3: Bimodal Theory Abstraction Integration (4-5 days)

**Objective**: Migrate bimodal theory from direct CVC5 usage to SolverInterface

**Complexity**: Medium

#### Tasks

- [ ] **Update bimodal semantic.py to use SolverInterface**:
  - File: `Code/src/model_checker/theory_lib/bimodal/semantic/semantic.py`
  - Replace: `import cvc5` → `from model_checker.solver import SolverFactory, settings`
  - Change: `cvc5.Solver()` → `SolverFactory.create(settings.smt_solver).create_solver()`
  - Use: Adapter methods (`mk_bool_sort()`, `mk_forall()`, etc.) instead of direct API

- [ ] **Update bimodal operators.py**:
  - File: `Code/src/model_checker/theory_lib/bimodal/semantic/operators.py`
  - Use: SolverInterface methods for constraint construction

- [ ] **Update bimodal witness_constraints.py**:
  - File: `Code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py`
  - Critical: ForAll with patterns → adapter handles Z3 patterns vs CVC5 MBQI

- [ ] **Test bimodal with Z3 adapter**:
  - Settings: `smt_solver = "z3"`
  - Expected: Identical behavior to pre-abstraction (regression test)
  - Command: `PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/ -v`

- [ ] **Test bimodal with CVC5 adapter**:
  - Settings: `smt_solver = "cvc5"`
  - Expected: CVC5 performance gains maintained (BM_CM_1 in ~6ms)
  - Command: `PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/unit/ -v`

- [ ] **Run parallel validation suite**:
  - Create: `Code/tests/integration/test_solver_equivalence.py`
  - Test: All bimodal examples with both Z3 and CVC5
  - Validate: sat/unsat agreement, model equivalence (semantically)
  - Document: Any expected differences

- [ ] **Update bimodal documentation**:
  - File: `Code/src/model_checker/theory_lib/bimodal/README.md`
  - Add: Solver selection instructions
  - Note: CVC5 recommended for witness predicate performance

#### Testing

```bash
# Test with Z3 (default)
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/ -v

# Test with CVC5
PYTHONPATH=Code/src SMT_SOLVER=cvc5 pytest Code/src/model_checker/theory_lib/bimodal/tests/ -v

# Run equivalence tests
PYTHONPATH=Code/src pytest Code/tests/integration/test_solver_equivalence.py -v

# Performance comparison
PYTHONPATH=Code/src python3 benchmark_bimodal_solvers.py
```

**Success Criteria**:
- Bimodal works with both Z3 and CVC5 via abstraction
- No Z3 regression (all existing tests pass)
- CVC5 performance maintained (6ms on BM_CM_1)
- sat/unsat results agree between solvers (or differences documented)
- Documentation updated

**Validation**:
- Manual test: Run `./dev_cli.py bimodal/examples.py` with both solvers
- Check: Model outputs are semantically equivalent
- Verify: No performance degradation from abstraction overhead (<5%)

---

### Phase 4: Exclusion Theory Migration (3-4 days)

**Objective**: Migrate exclusion theory to SolverInterface

**Complexity**: Medium

#### Tasks

- [ ] **Migrate exclusion semantic.py**:
  - File: `Code/src/model_checker/theory_lib/exclusion/semantic/semantic.py`
  - Replace: Direct Z3 imports → SolverInterface usage
  - Pattern: Follow bimodal migration approach

- [ ] **Migrate exclusion operators.py**:
  - File: `Code/src/model_checker/theory_lib/exclusion/semantic/operators.py`
  - Update: Exclusion operators to use SolverInterface

- [ ] **Update exclusion witness_constraints.py** (if exists):
  - File: `Code/src/model_checker/theory_lib/exclusion/semantic/witness_constraints.py`
  - Handle: Quantifier patterns similar to bimodal

- [ ] **Test exclusion with Z3 adapter**:
  - Tests: `Code/src/model_checker/theory_lib/exclusion/tests/unit/`
  - Expected: No regression
  - Command: `PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/exclusion/tests/unit/ -v`

- [ ] **Test exclusion with CVC5 adapter**:
  - Settings: `smt_solver = "cvc5"`
  - Expected: CVC5 handles exclusion examples correctly
  - Validate: Performance comparable or better

- [ ] **Document exclusion solver compatibility**:
  - File: Update `Code/src/model_checker/theory_lib/exclusion/README.md`
  - Note: Solver recommendations, any known issues

#### Testing

```bash
# Test with both solvers
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/exclusion/tests/ -v
PYTHONPATH=Code/src SMT_SOLVER=cvc5 pytest Code/src/model_checker/theory_lib/exclusion/tests/ -v

# Add to equivalence suite
PYTHONPATH=Code/src pytest Code/tests/integration/test_solver_equivalence.py::test_exclusion_equivalence -v
```

**Success Criteria**:
- Exclusion works with both Z3 and CVC5
- All tests pass with both adapters
- No performance regression
- Solver equivalence validated

---

### Phase 5: Imposition Theory Migration (3-4 days)

**Objective**: Migrate imposition theory to SolverInterface

**Complexity**: Medium

#### Tasks

- [ ] **Migrate imposition semantic.py**:
  - File: `Code/src/model_checker/theory_lib/imposition/semantic/semantic.py`
  - Replace: Direct Z3 imports → SolverInterface usage

- [ ] **Migrate imposition operators.py**:
  - File: `Code/src/model_checker/theory_lib/imposition/semantic/operators.py`
  - Update: Imposition operators to use SolverInterface

- [ ] **Test imposition with Z3 adapter**:
  - Tests: `Code/src/model_checker/theory_lib/imposition/tests/unit/`
  - Expected: No regression

- [ ] **Test imposition with CVC5 adapter**:
  - Settings: `smt_solver = "cvc5"`
  - Validate: CVC5 handles imposition examples

- [ ] **Document imposition solver compatibility**:
  - File: Update `Code/src/model_checker/theory_lib/imposition/README.md`

#### Testing

```bash
# Test with both solvers
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/imposition/tests/ -v
PYTHONPATH=Code/src SMT_SOLVER=cvc5 pytest Code/src/model_checker/theory_lib/imposition/tests/ -v

# Equivalence validation
PYTHONPATH=Code/src pytest Code/tests/integration/test_solver_equivalence.py::test_imposition_equivalence -v
```

**Success Criteria**:
- Imposition works with both Z3 and CVC5
- All tests pass with both adapters
- Solver equivalence validated

---

### Phase 6: Logos Theory Migration (3-4 days)

**Objective**: Migrate logos theory to SolverInterface

**Complexity**: Low-Medium (simpler theory, no witness predicates)

#### Tasks

- [ ] **Migrate logos semantic.py**:
  - File: `Code/src/model_checker/theory_lib/logos/semantic/semantic.py`
  - Replace: Direct Z3 imports → SolverInterface usage

- [ ] **Migrate logos operators.py**:
  - File: `Code/src/model_checker/theory_lib/logos/semantic/operators.py`
  - Update: Logos operators (simpler, no quantifiers)

- [ ] **Test logos with Z3 adapter**:
  - Tests: `Code/src/model_checker/theory_lib/logos/tests/unit/`
  - Expected: No regression

- [ ] **Test logos with CVC5 adapter**:
  - Settings: `smt_solver = "cvc5"`
  - Expected: Faster (logos is simpler, both solvers should handle well)

- [ ] **Document logos solver compatibility**:
  - File: Update `Code/src/model_checker/theory_lib/logos/README.md`

#### Testing

```bash
# Test with both solvers
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/logos/tests/ -v
PYTHONPATH=Code/src SMT_SOLVER=cvc5 pytest Code/src/model_checker/theory_lib/logos/tests/ -v

# Equivalence validation
PYTHONPATH=Code/src pytest Code/tests/integration/test_solver_equivalence.py::test_logos_equivalence -v
```

**Success Criteria**:
- Logos works with both Z3 and CVC5
- All tests pass with both adapters
- Solver equivalence validated

---

### Phase 7: Core Infrastructure Migration (1 week)

**Objective**: Migrate core packages (builder, iterate, models) to SolverInterface

**Complexity**: High

#### Tasks

- [ ] **Migrate builder/z3_utils.py to abstraction**:
  - File: `Code/src/model_checker/builder/z3_utils.py`
  - Rename: `builder/solver_utils.py` (solver-agnostic)
  - Replace: Z3-specific logic → SolverInterface methods
  - Deprecate: Old z3_utils imports (provide compatibility shim)

- [ ] **Migrate utils/z3_helpers.py to abstraction**:
  - File: `Code/src/model_checker/utils/z3_helpers.py`
  - Rename: `utils/solver_helpers.py`
  - Replace: Custom ForAll/Exists → Adapter handles translation
  - Strategy: May need solver-specific implementations in adapters

- [ ] **Update iterate/base.py solver creation**:
  - File: `Code/src/model_checker/iterate/base.py`
  - Replace: `z3.Solver()` → `SolverFactory.create(settings.smt_solver).create_solver()`
  - Ensure: Iteration loop works with both solvers

- [ ] **Update iterate/constraints.py**:
  - File: `Code/src/model_checker/iterate/constraints.py`
  - Use: SolverInterface methods for constraint generation

- [ ] **Update models/structure.py**:
  - File: `Code/src/model_checker/models/structure.py`
  - Replace: Direct Z3 model extraction → Adapter methods
  - Handle: Solver-specific model representations

- [ ] **Test builder with both solvers**:
  - Tests: `Code/src/model_checker/builder/tests/`
  - Command: `PYTHONPATH=Code/src pytest Code/src/model_checker/builder/tests/ -v`

- [ ] **Test iterate with both solvers**:
  - Tests: `Code/src/model_checker/iterate/tests/`
  - Command: `PYTHONPATH=Code/src pytest Code/src/model_checker/iterate/tests/ -v`

- [ ] **Test models with both solvers**:
  - Tests: `Code/src/model_checker/models/tests/`
  - Command: `PYTHONPATH=Code/src pytest Code/src/model_checker/models/tests/ -v`

#### Testing

```bash
# Test all core packages with Z3
PYTHONPATH=Code/src pytest Code/src/model_checker/builder/tests/ -v
PYTHONPATH=Code/src pytest Code/src/model_checker/iterate/tests/ -v
PYTHONPATH=Code/src pytest Code/src/model_checker/models/tests/ -v

# Test all core packages with CVC5
PYTHONPATH=Code/src SMT_SOLVER=cvc5 pytest Code/src/model_checker/builder/tests/ -v
PYTHONPATH=Code/src SMT_SOLVER=cvc5 pytest Code/src/model_checker/iterate/tests/ -v
PYTHONPATH=Code/src SMT_SOLVER=cvc5 pytest Code/src/model_checker/models/tests/ -v

# Integration tests
PYTHONPATH=Code/src pytest Code/tests/integration/ -v
```

**Success Criteria**:
- All core packages work with both solvers
- No Z3 regression
- CVC5 performance maintained
- Model iteration deterministic with CVC5
- All integration tests pass

---

### Phase 8: Documentation, Polish, and Release (3-4 days)

**Objective**: Complete documentation, cleanup, and prepare for production

**Complexity**: Low

#### Tasks

- [ ] **Create solver abstraction documentation**:
  - File: `Code/docs/architecture/SOLVER_ABSTRACTION.md`
  - Content: Architecture overview, adding new solvers, capability matrix
  - Diagrams: Architecture diagram (Unicode box-drawing)

- [ ] **Update CLAUDE.md**:
  - File: `CLAUDE.md`
  - Update: Note multi-solver support, CVC5 recommendation for witness predicates
  - Add: Solver selection instructions

- [ ] **Create migration guide for theory developers**:
  - File: `Code/docs/development/SOLVER_MIGRATION_GUIDE.md`
  - Content: How to use SolverInterface, patterns to follow, gotchas

- [ ] **Update all theory READMEs**:
  - Files: `Code/src/model_checker/theory_lib/*/README.md`
  - Add: Solver compatibility notes, performance recommendations

- [ ] **Create solver comparison report**:
  - File: `specs/reports/015_solver_abstraction_implementation_summary.md`
  - Content: Migration results, performance comparison, lessons learned

- [ ] **Update main README.md**:
  - File: `README.md`
  - Add: Solver selection section, CVC5 benefits

- [ ] **Run complete test suite with both solvers**:
  - Command: `PYTHONPATH=Code/src pytest Code/tests/ -v`
  - Command: `PYTHONPATH=Code/src SMT_SOLVER=cvc5 pytest Code/tests/ -v`
  - Expected: All pass

- [ ] **Create benchmark suite**:
  - File: `Code/scripts/benchmark_solvers.py`
  - Purpose: Compare Z3 vs CVC5 performance across all theories
  - Output: Performance report for documentation

- [ ] **Deprecate old Z3-specific files**:
  - Files: `builder/z3_utils.py`, `utils/z3_helpers.py`
  - Action: Add deprecation warnings, maintain imports for compatibility
  - Plan: Remove in next major version

- [ ] **Final code quality check**:
  - Coverage: Ensure >85% test coverage for solver package
  - Typing: Run mypy on solver package
  - Linting: Run flake8/black on solver package

#### Testing

```bash
# Full test suite with both solvers
PYTHONPATH=Code/src pytest Code/tests/ -v --cov=model_checker --cov-report=term-missing
PYTHONPATH=Code/src SMT_SOLVER=cvc5 pytest Code/tests/ -v

# Run benchmarks
PYTHONPATH=Code/src python3 Code/scripts/benchmark_solvers.py

# Type checking
mypy Code/src/model_checker/solver/

# Code quality
black Code/src/model_checker/solver/
flake8 Code/src/model_checker/solver/
```

**Success Criteria**:
- All documentation complete and accurate
- Test coverage >85%
- No mypy/flake8 errors
- Benchmark report generated
- Migration guide clear and comprehensive

**Release Readiness**:
- [ ] All tests pass with both solvers
- [ ] Documentation complete
- [ ] Performance validated
- [ ] No known critical issues
- [ ] Migration guide reviewed

---

## Testing Strategy

### Unit Tests

**Per-Package Testing**:
- `solver/`: Test interface, adapters, factory, capabilities
- `theory_lib/*/`: Test theory logic with both Z3 and CVC5
- `builder/`: Test solver-agnostic constraint building
- `iterate/`: Test model iteration with both solvers
- `models/`: Test model structures with both solvers

**Test Structure**:
```python
# Example: test_z3_adapter.py
class TestZ3Adapter:
    def test_create_solver(self):
        adapter = Z3SolverAdapter()
        solver = adapter.create_solver()
        assert solver is not None

    def test_check_sat_unsat(self):
        adapter = Z3SolverAdapter()
        solver = adapter.create_solver()
        # Add unsat constraint
        adapter.assert_constraint(solver, adapter.mk_bool_val(False))
        result = adapter.check_sat(solver)
        assert result == SatResult.UNSAT
```

### Integration Tests

**Equivalence Validation**:
- File: `Code/tests/integration/test_solver_equivalence.py`
- Purpose: Ensure Z3 and CVC5 produce equivalent results
- Approach: Run all examples with both solvers, compare sat/unsat and model semantics

**Performance Benchmarks**:
- File: `Code/scripts/benchmark_solvers.py`
- Purpose: Track performance differences
- Metrics: Solve time, memory usage, determinism

### Regression Tests

**Z3 Regression Prevention**:
- Run existing test suite with Z3 adapter
- Expected: 100% pass rate (no behavior change)
- Validates: Abstraction doesn't break existing functionality

**CVC5 Performance Validation**:
- Run BM_CM_1, BM_CM_2, TN_CM_2 with CVC5
- Expected: <10ms solve time (maintain Report 012 performance)
- Validates: Abstraction doesn't add overhead

### Test Commands

```bash
# Unit tests per phase
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/ -v

# Theory tests with specific solver
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/bimodal/tests/ -v
PYTHONPATH=Code/src SMT_SOLVER=cvc5 pytest Code/src/model_checker/theory_lib/bimodal/tests/ -v

# Integration tests (both solvers)
PYTHONPATH=Code/src pytest Code/tests/integration/ -v

# Full suite
PYTHONPATH=Code/src pytest Code/tests/ -v --cov=model_checker --cov-report=term-missing

# Benchmarks
PYTHONPATH=Code/src python3 Code/scripts/benchmark_solvers.py
```

## Documentation Requirements

### Technical Documentation

1. **Solver Abstraction Architecture** (`Code/docs/architecture/SOLVER_ABSTRACTION.md`):
   - Architecture diagram
   - Component responsibilities
   - Design rationale
   - Adding new solvers

2. **Solver Migration Guide** (`Code/docs/development/SOLVER_MIGRATION_GUIDE.md`):
   - How to use SolverInterface in theory code
   - Common patterns
   - Troubleshooting

3. **CVC5 Configuration** (`Code/docs/development/CVC5_CONFIGURATION.md`):
   - Required options (MBQI+enum-inst)
   - Performance tuning
   - Debugging tips

### API Documentation

- Docstrings for all SolverInterface methods
- Docstrings for Z3SolverAdapter, CVC5SolverAdapter
- Type hints throughout

### User Documentation

- **README.md**: Add solver selection section
- **Theory READMEs**: Solver compatibility notes
- **CLAUDE.md**: Update for multi-solver support

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

**Must be abstraction-compatible**:
- `builder/z3_utils.py` → Migrate to `solver_utils.py`
- `utils/z3_helpers.py` → Migrate to `solver_helpers.py`
- `iterate/base.py` → Update solver creation
- `models/structure.py` → Update model extraction

**Theory implementations**:
- `theory_lib/bimodal/` → Migrate first (pilot validated)
- `theory_lib/exclusion/` → Migrate second
- `theory_lib/imposition/` → Migrate third
- `theory_lib/logos/` → Migrate last (simplest)

## Risks and Mitigation

### Risk 1: CVC5 Performance Regression on Simple Cases

**Risk**: CVC5 might be slower than Z3 on cases Z3 handles well

**Likelihood**: Medium

**Impact**: Medium (user experience, benchmarks)

**Mitigation**:
- Phase 0: Benchmark simple cases with CVC5 before full migration
- If regression >10%: Allow per-theory solver configuration
- Fallback: Keep Z3 as default, CVC5 opt-in for witness predicates

### Risk 2: Abstraction Overhead

**Risk**: Abstraction layer adds significant performance overhead

**Likelihood**: Low (thin wrapper design)

**Impact**: Medium (defeats purpose if too slow)

**Mitigation**:
- Measure overhead in Phase 2 tests (<5% acceptable)
- Allow performance-critical paths to bypass abstraction if needed
- Profile and optimize hot paths

### Risk 3: Solver API Incompatibilities

**Risk**: Z3 and CVC5 APIs differ more than expected, abstraction too complex

**Likelihood**: Low (pilot validates translation)

**Impact**: High (could require redesign)

**Mitigation**:
- Phase 1 pilot identifies issues early
- Report 011 translation reference already comprehensive
- If blockers: Solver-specific implementations in theories (less abstraction)

### Risk 4: CVC5 Solver Bugs

**Risk**: CVC5 has bugs on edge cases not in pilot

**Likelihood**: Medium (new solver for us)

**Impact**: High (incorrect results)

**Mitigation**:
- Extensive parallel testing (Phase 3-7)
- Compare Z3 vs CVC5 results on all examples
- Document any known issues in theory READMEs
- Keep Z3 as fallback option

### Risk 5: Test Suite Not Comprehensive Enough

**Risk**: Tests pass but real usage breaks

**Likelihood**: Low (existing test coverage >85%)

**Impact**: High (production issues)

**Mitigation**:
- Run all existing tests with both solvers
- Add integration tests comparing solver outputs
- Manual testing on complex examples
- Phased rollout allows early issue detection

## Notes

### CVC5 Configuration Requirements

**Critical for witness predicates**:
```python
solver.setOption("mbqi", "true")        # Model-based quantifier instantiation
solver.setOption("enum-inst", "true")   # Enumerative instantiation
```

Without these options, CVC5 returns "unknown" on witness predicate examples (Report 012 finding).

**Standard setup** for all theories using quantifiers:
```python
solver.setLogic("ALL")
solver.setOption("produce-models", "true")
solver.setOption("mbqi", "true")
solver.setOption("enum-inst", "true")
```

### API Translation Reference

See **Report 011** (`specs/reports/011_z3_to_cvc5_api_translation.md`) for comprehensive Z3→CVC5 API mapping.

**Key differences**:
- No operator overloading in CVC5 (use `mkTerm(Kind.ADD, x, y)`)
- Explicit variable types (`mkVar()` vs `mkConst()`)
- Quantifiers require `Kind.VARIABLE_LIST` term
- Function application needs `Kind.APPLY_UF`

### Performance Expectations

Based on Report 012:

**CVC5 advantages**:
- Witness predicates: 850× faster (6ms vs 5000ms+ timeout)
- Deterministic results (vs Z3 non-determinism)
- Complex quantifier patterns

**Z3 advantages** (potential):
- Simple propositional cases (may be faster)
- Mature optimizations
- Better documentation

**Acceptable overhead**:
- <5% from abstraction layer
- <10% on simple cases if CVC5 slower

### Maintenance Considerations

**Adding future solvers**:
1. Implement new `SolverAdapter` class
2. Register in `SolverFactory`
3. Define capability matrix
4. Test against existing theories
5. Document in architecture docs

**Solver-specific features**:
- Expose via adapter methods (e.g., `set_quantifier_strategy()`)
- Document in capability matrix
- Theory code checks capabilities before using

**Deprecation path**:
- Keep Z3 as default for backward compatibility
- Recommend CVC5 for new projects (performance)
- May deprecate Z3 in future if CVC5 universally superior

## References

### Research Reports
- [Report 012: CVC5 Feasibility Results](../reports/012_cvc5_feasibility_results.md) - **Critical**: CVC5 success validation
- [Report 010: Z3 to CVC5 Refactoring Effort Assessment](../reports/010_z3_to_cvc5_refactoring_effort_assessment.md) - Initial effort estimate
- [Report 011: Z3 to CVC5 API Translation](../reports/011_z3_to_cvc5_api_translation.md) - API mapping reference
- [Report 009: Alternative SMT Solvers Evaluation](../reports/009_alternative_smt_solvers_evaluation.md) - Solver comparison background

### Plans
- [Plan 104: CVC5 Feasibility Test](104_cvc5_feasibility_test.md) - Test that validated CVC5
- [Plan 103: Quantifier-Free Witness Encoding](103_quantifier_free_witness_encoding.md) - Failed approach (context)

### External Resources
- CVC5 Documentation: https://cvc5.github.io/
- CVC5 Python API: https://cvc5.github.io/docs/cvc5-1.0.2/api/python/pythonic/pythonic.html
- PySMT (reference): https://github.com/pysmt/pysmt
- SMT-LIB Standard: http://smtlib.cs.uiowa.edu/

### Code References
- Current Z3 integration: `Code/src/model_checker/builder/z3_utils.py`, `Code/src/model_checker/utils/z3_helpers.py`
- Bimodal theory: `Code/src/model_checker/theory_lib/bimodal/` (pilot target)
- Test infrastructure: `Code/tests/`, theory-specific `tests/unit/`, `tests/integration/`
