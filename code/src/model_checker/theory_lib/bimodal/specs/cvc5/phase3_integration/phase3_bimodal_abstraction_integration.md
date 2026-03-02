# Phase 3: Bimodal Theory Abstraction Integration

## Metadata
- **Date**: 2025-10-02
- **Phase**: 3 of 3 (SMT Solver Abstraction Implementation)
- **Parent Plan**: [specs/plans/105_smt_solver_abstraction_REVISED.md](../../../../../specs/plans/105_smt_solver_abstraction_REVISED.md)
- **Prerequisites**:
  - Phase 1: Bimodal Theory CVC5 Pilot (MUST be complete)
  - Phase 2: Abstraction Layer Design (MUST be complete)
- **Objective**: Migrate bimodal theory from direct CVC5 usage to SolverInterface abstraction
- **Complexity**: Medium
- **Estimated Duration**: 4-5 days
- **Branch**: `feature/bimodal-solver-interface`
- **Standards**:
  - [CODE_STANDARDS.md](../../../../../docs/core/CODE_STANDARDS.md)
  - [TESTING.md](../../../../../docs/core/TESTING.md)
  - [ARCHITECTURE.md](../../../../../docs/core/ARCHITECTURE.md)

## Overview

### Strategic Context

**Phase 1 Output** (Direct CVC5 implementation):
- Bimodal theory fully migrated to CVC5 API
- 6 critical examples validated (~6ms performance)
- API translation patterns documented
- Pain points identified

**Phase 2 Output** (Abstraction layer):
- SolverInterface with ~35 methods
- Z3SolverAdapter (backward compatible)
- CVC5SolverAdapter (using Phase 1 patterns)
- SolverFactory for runtime selection
- Settings integration (smt_solver config)
- >90% test coverage on abstraction

**Phase 3 Goal**: Migrate bimodal theory to use SolverInterface, enabling:
1. Dual-solver support (Z3 and CVC5 through same interface)
2. Runtime solver selection via settings
3. 100% backward compatibility with Z3
4. Maintained CVC5 performance gains (850× on witness predicates)
5. Proven abstraction layer with real theory usage

### Migration Strategy

**3-Layer Integration Approach**:

1. **Interface Integration**: Replace direct CVC5 imports with SolverInterface
2. **Solver Injection**: Pass solver adapter through theory initialization
3. **API Translation**: Convert direct API calls to adapter methods

**Files to Migrate** (from Phase 1 research):
- `semantic.py` (2,593 lines): Core semantics
- `operators.py` (1,083 lines): Modal/temporal operators
- `witness_constraints.py` (257 lines): Witness predicates (CRITICAL)
- `witness_registry.py` (177 lines): Witness tracking
- `examples.py` (671 lines): Entry point and solver setup
- `iterate.py` (602 lines): Model iteration

**TDD Approach**:
1. Write integration tests FIRST (using SolverInterface)
2. Verify RED state (tests fail with direct CVC5 code)
3. Migrate to abstraction (minimal changes)
4. Verify GREEN state (tests pass)
5. Test with both solvers (Z3 and CVC5)
6. Validate equivalence and performance

### Dual-Solver Validation Strategy

**Z3 Backend** (Regression Testing):
- Settings: `smt_solver = "z3"`
- Expected: Identical behavior to pre-abstraction
- Validation: All existing tests pass
- Purpose: Ensure no regressions

**CVC5 Backend** (Performance Validation):
- Settings: `smt_solver = "cvc5"`
- Expected: Maintain Phase 1 performance (~6ms)
- Validation: 6 critical examples solve fast
- Purpose: Ensure abstraction overhead <5%

**Equivalence Testing**:
- Run all examples with both solvers
- Compare: sat/unsat results
- Validate: Semantic equivalence of models
- Document: Expected differences (if any)

## Success Criteria

### Functional Requirements
- [ ] Bimodal theory works with SolverInterface (no direct CVC5)
- [ ] Z3 backend passes all existing tests (regression)
- [ ] CVC5 backend maintains performance (~6ms on BM_CM_*)
- [ ] Runtime solver selection via settings works
- [ ] All 22 examples work with both solvers

### Quality Requirements (Per TESTING.md)
- [ ] **TDD Compliance**: All tests written BEFORE migration
- [ ] Integration tests validate both solvers
- [ ] Equivalence tests compare Z3 vs CVC5 results
- [ ] Test coverage >85% maintained for bimodal
- [ ] Witness predicate coverage >90% maintained

### Performance Requirements
- [ ] Abstraction overhead <5% (both solvers)
- [ ] CVC5 performance maintained: BM_CM_* ~6ms
- [ ] Z3 performance unchanged from baseline
- [ ] No memory leaks or resource issues

### Documentation Requirements
- [ ] Bimodal README updated with solver selection
- [ ] Migration patterns documented for other theories
- [ ] Equivalence test results documented
- [ ] No historical references in docs

## Technical Design

### Solver Injection Pattern

**Current** (Phase 1 - Direct CVC5):
```python
# examples.py
import cvc5

solver = cvc5.Solver()
solver.setLogic("ALL")
solver.setOption("mbqi", "true")
solver.setOption("enum-inst", "true")

# semantic.py
import cvc5
from cvc5 import Kind

def define_semantics(solver):
    bool_sort = solver.getBooleanSort()
    # ... direct CVC5 API calls
```

**Target** (Phase 3 - SolverInterface):
```python
# examples.py
from model_checker.solver import SolverFactory
from model_checker.settings import settings

factory = SolverFactory()
adapter = factory.create(settings.smt_solver)  # "z3" or "cvc5"
solver = adapter.create_solver()

# semantic.py
from ..solver import SolverInterface  # Relative import

def define_semantics(adapter: SolverInterface):
    solver = adapter.create_solver()
    bool_sort = adapter.mk_bool_sort()
    # ... adapter method calls
```

### API Translation Mapping

**From Phase 1** (direct CVC5) **→ To Phase 3** (SolverInterface):

| Phase 1 CVC5 | Phase 3 Interface |
|--------------|-------------------|
| `solver.getBooleanSort()` | `adapter.mk_bool_sort()` |
| `solver.getIntegerSort()` | `adapter.mk_int_sort()` |
| `solver.mkBitVectorSort(N)` | `adapter.mk_bitvec_sort(N)` |
| `solver.mkFunctionSort([args], ret)` + `mkConst()` | `adapter.mk_function(name, [args], ret)` |
| `solver.mkTerm(Kind.AND, a, b)` | `adapter.mk_and(a, b)` |
| `solver.mkTerm(Kind.OR, a, b)` | `adapter.mk_or(a, b)` |
| `solver.mkTerm(Kind.IMPLIES, a, b)` | `adapter.mk_implies(a, b)` |
| `solver.mkVar(sort, name)` | `adapter.mk_var(sort, name)` |
| `solver.mkConst(sort, name)` | `adapter.mk_const(sort, name)` |
| `solver.mkTerm(Kind.FORALL, var_list, body)` | `adapter.mk_forall(vars, body)` |
| `solver.mkTerm(Kind.SELECT, array, idx)` | `adapter.mk_select(array, idx)` |
| `solver.assertFormula(constraint)` | `adapter.assert_constraint(solver, constraint)` |
| `solver.checkSat()` | `adapter.check_sat(solver)` |

**Key Simplifications**:
- No more explicit `Kind.*` constants
- No more `mkTerm()` verbosity
- No manual `VARIABLE_LIST` creation for ForAll
- Solver-agnostic API surface

### File Migration Details

#### 1. semantic.py Migration

**Current Structure** (Phase 1):
```python
import cvc5
from cvc5 import Kind

def define_bimodal_semantics(solver):
    bool_sort = solver.getBooleanSort()
    int_sort = solver.getIntegerSort()

    # Function declarations
    f_sort = solver.mkFunctionSort([bool_sort], bool_sort)
    f = solver.mkConst(f_sort, "f")

    # Quantifiers
    x_var = solver.mkVar(bool_sort, "x")
    var_list = solver.mkTerm(Kind.VARIABLE_LIST, x_var)
    body = solver.mkTerm(Kind.IMPLIES, ...)
    forall = solver.mkTerm(Kind.FORALL, var_list, body)

    # Operators
    constraint = solver.mkTerm(Kind.AND, ...)
```

**Target Structure** (Phase 3):
```python
from typing import Any
# Relative import for solver interface
from model_checker.solver import SolverInterface

def define_bimodal_semantics(adapter: SolverInterface):
    solver = adapter.create_solver()
    bool_sort = adapter.mk_bool_sort()
    int_sort = adapter.mk_int_sort()

    # Function declarations (simplified!)
    f = adapter.mk_function("f", [bool_sort], bool_sort)

    # Quantifiers (simplified!)
    x_var = adapter.mk_var(bool_sort, "x")
    body = adapter.mk_implies(...)
    forall = adapter.mk_forall([x_var], body)

    # Operators (simplified!)
    constraint = adapter.mk_and(...)
```

**Migration Tasks**:
- Replace `import cvc5` with `from model_checker.solver import SolverInterface`
- Change function signature: `(solver)` → `(adapter: SolverInterface)`
- Replace `solver.get*Sort()` with `adapter.mk_*_sort()`
- Replace `solver.mkConst(mkFunctionSort(...))` with `adapter.mk_function(...)`
- Replace `solver.mkTerm(Kind.*, ...)` with `adapter.mk_*(...)`
- Remove `Kind.VARIABLE_LIST` creation (adapter handles it)

#### 2. operators.py Migration

**Critical**: Modal/temporal operators using witness predicates

**Current** (Phase 1):
```python
import cvc5
from cvc5 import Kind

def Box(solver, formula, world):
    # Witness predicate with ForAll
    w_var = solver.mkVar(world_sort, "w")
    var_list = solver.mkTerm(Kind.VARIABLE_LIST, w_var)
    body = solver.mkTerm(Kind.IMPLIES,
        accessible(world, w_var),
        formula_at(formula, w_var)
    )
    return solver.mkTerm(Kind.FORALL, var_list, body)
```

**Target** (Phase 3):
```python
from model_checker.solver import SolverInterface

def Box(adapter: SolverInterface, formula, world, world_sort):
    # Witness predicate with ForAll (abstracted)
    w_var = adapter.mk_var(world_sort, "w")
    body = adapter.mk_implies(
        accessible(world, w_var),
        formula_at(formula, w_var)
    )
    return adapter.mk_forall([w_var], body)  # No patterns parameter
```

**Migration Tasks**:
- Update imports: `from model_checker.solver import SolverInterface`
- Add adapter parameter to all operator functions
- Replace quantifier creation with adapter methods
- Remove pattern hints (abstraction handles Z3 vs CVC5)

#### 3. witness_constraints.py Migration

**CRITICAL**: Witness predicate system

**Current** (Phase 1):
```python
import cvc5
from cvc5 import Kind

def create_witness_constraints(solver, witness_predicates):
    constraints = []
    for wp in witness_predicates:
        # Complex nested ForAll
        x_var = solver.mkVar(x_sort, "x")
        y_var = solver.mkVar(y_sort, "y")
        var_list = solver.mkTerm(Kind.VARIABLE_LIST, x_var, y_var)
        body = ...
        forall = solver.mkTerm(Kind.FORALL, var_list, body)
        constraints.append(forall)
    return solver.mkTerm(Kind.AND, *constraints)
```

**Target** (Phase 3):
```python
from model_checker.solver import SolverInterface

def create_witness_constraints(adapter: SolverInterface, witness_predicates, sorts):
    constraints = []
    solver = adapter.create_solver()

    for wp in witness_predicates:
        # Nested ForAll (simplified)
        x_var = adapter.mk_var(sorts['x'], "x")
        y_var = adapter.mk_var(sorts['y'], "y")
        body = ...
        forall = adapter.mk_forall([x_var, y_var], body)
        constraints.append(forall)

    return adapter.mk_and(*constraints)
```

**Migration Tasks**:
- Replace CVC5 imports with SolverInterface
- Update function signatures with adapter parameter
- Simplify ForAll creation (no VARIABLE_LIST)
- Ensure MBQI+enum-inst configured (adapter responsibility)

#### 4. examples.py Migration

**Current** (Phase 1 - Direct CVC5):
```python
import cvc5

def run_examples():
    solver = cvc5.Solver()
    solver.setLogic("ALL")
    solver.setOption("produce-models", "true")
    solver.setOption("mbqi", "true")  # Critical
    solver.setOption("enum-inst", "true")  # Critical

    # Run examples
    for example in examples:
        # ... use solver directly
```

**Target** (Phase 3 - Abstraction):
```python
from model_checker.solver import SolverFactory
from model_checker.settings import settings

def run_examples():
    factory = SolverFactory()
    adapter = factory.create(settings.smt_solver)  # "z3" or "cvc5"
    solver = adapter.create_solver()
    # Adapter handles MBQI+enum-inst for CVC5 automatically

    # Run examples
    for example in examples:
        # ... use adapter methods
```

**Migration Tasks**:
- Replace CVC5 import with SolverFactory
- Load settings for solver selection
- Create adapter via factory
- Remove explicit MBQI+enum-inst (adapter handles)
- Update all solver operations to use adapter

#### 5. iterate.py Migration

**Current** (Phase 1):
```python
import cvc5

def iterate_models(solver):
    result = solver.checkSat()
    if result.isSat():
        model = solver.getModel()
        # Extract values...
```

**Target** (Phase 3):
```python
from model_checker.solver import SolverInterface

def iterate_models(adapter: SolverInterface, solver):
    result = adapter.check_sat(solver)
    if result == "sat":
        model = adapter.get_model(solver)
        # Extract values using adapter...
```

**Migration Tasks**:
- Add adapter parameter
- Replace solver methods with adapter methods
- Update result checking: `isSat()` → `== "sat"`

## Implementation Phases

### Sub-Phase 3.1: Integration Test Setup (1 day)

**Objective**: Write integration tests BEFORE migration (TDD)

#### Tasks
- [ ] **[TDD] Write test_bimodal_solver_interface.py** (RED first)
  - File: `tests/integration/test_bimodal_solver_interface.py`
  - Test: Bimodal with SolverInterface (before migration)
  - Expected: FAIL (bimodal uses direct CVC5, not interface)
  - Coverage: All 6 critical examples with both solvers

- [ ] **[TDD] Write test_solver_equivalence.py** (RED first)
  - File: `code/tests/integration/test_solver_equivalence.py`
  - Test: Z3 vs CVC5 equivalence on bimodal examples
  - Expected: FAIL (bimodal not using abstraction yet)
  - Coverage: All 22 examples, sat/unsat agreement

- [ ] **[TDD] Write test_performance_validation.py** (RED first)
  - File: `tests/integration/test_performance_validation.py`
  - Test: CVC5 performance maintained (~6ms)
  - Expected: FAIL (no abstraction yet)
  - Coverage: 6 critical examples, timing validation

- [ ] **Create test fixtures for dual-solver testing**
  - Fixtures: Z3 adapter, CVC5 adapter, example data
  - Utilities: Result comparison, performance measurement

#### Testing
```bash
# TDD - verify tests FAIL before migration
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_bimodal_solver_interface.py -v
# Expected: FAIL (bimodal doesn't use SolverInterface yet)

PYTHONPATH=code/src pytest code/tests/integration/test_solver_equivalence.py -v
# Expected: FAIL (bimodal not migrated)
```

**Success Criteria**:
- All integration tests written BEFORE migration
- Tests fail as expected (RED state verified)
- Test fixtures ready for dual-solver validation
- Performance baselines established

### Sub-Phase 3.2: Semantic Core Migration (1 day)

**Objective**: Migrate semantic.py to use SolverInterface

#### Tasks
- [ ] **Update semantic.py imports**
  - Remove: `import cvc5`, `from cvc5 import Kind`
  - Add: `from model_checker.solver import SolverInterface`
  - Verify: Relative imports for local modules

- [ ] **Update define_bimodal_semantics() signature**
  - Change: `(solver)` → `(adapter: SolverInterface)`
  - Add: `solver = adapter.create_solver()` at start

- [ ] **Migrate type constructors**
  - Replace: `solver.getBooleanSort()` → `adapter.mk_bool_sort()`
  - Replace: `solver.getIntegerSort()` → `adapter.mk_int_sort()`
  - Replace: `solver.mkBitVectorSort(N)` → `adapter.mk_bitvec_sort(N)`

- [ ] **Migrate function declarations**
  - Replace: `solver.mkFunctionSort() + mkConst()` → `adapter.mk_function()`
  - Simplify: Remove intermediate sort variables

- [ ] **Migrate logical operators**
  - Replace: `solver.mkTerm(Kind.AND, ...)` → `adapter.mk_and(...)`
  - Replace: `solver.mkTerm(Kind.OR, ...)` → `adapter.mk_or(...)`
  - Replace: `solver.mkTerm(Kind.IMPLIES, ...)` → `adapter.mk_implies(...)`

- [ ] **Migrate quantifiers**
  - Replace: `mkVar() + VARIABLE_LIST + mkTerm(FORALL)` → `adapter.mk_forall([vars], body)`
  - Simplify: Remove Kind.VARIABLE_LIST creation

- [ ] **Run semantic tests**
  - Test: `test_semantic_cvc5.py` (from Phase 1)
  - Expected: PASS (functionality preserved)

#### Testing
```bash
# Test semantic core migration
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantic_cvc5.py -v

# Test with integration suite (should start passing)
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_bimodal_solver_interface.py -v
```

**Success Criteria**:
- semantic.py uses SolverInterface only
- All imports updated (no direct CVC5)
- Unit tests pass
- Integration tests start passing

### Sub-Phase 3.3: Operators and Witness Migration (1 day)

**Objective**: Migrate operators and witness system to SolverInterface

#### Tasks
- [ ] **Migrate operators.py**
  - Update: Imports to SolverInterface
  - Update: Function signatures with adapter parameter
  - Replace: CVC5 API calls with adapter methods
  - Critical: Box, Diamond, Future, Past operators

- [ ] **Migrate witness_constraints.py** (CRITICAL)
  - Update: Imports to SolverInterface
  - Update: create_witness_constraints() signature
  - Replace: Nested ForAll creation with adapter methods
  - Verify: MBQI+enum-inst handled by adapter

- [ ] **Migrate witness_registry.py**
  - Update: Imports to SolverInterface
  - Update: Witness tracking to use adapter
  - Verify: Registration semantics preserved

- [ ] **Run operator tests**
  - Test: `test_operators_cvc5.py` (from Phase 1)
  - Expected: PASS

- [ ] **Run witness tests** (>90% coverage required)
  - Test: `test_witness_cvc5.py` (from Phase 1)
  - Expected: PASS
  - Verify: Coverage >90% maintained

#### Testing
```bash
# Operator tests
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_operators_cvc5.py -v

# Witness tests (critical path - >90% coverage)
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_witness_cvc5.py -v --cov=model_checker.theory_lib.bimodal.semantic.witness_constraints --cov=model_checker.theory_lib.bimodal.semantic.witness_registry --cov-fail-under=90
```

**Success Criteria**:
- operators.py uses SolverInterface
- Witness system uses SolverInterface
- All unit tests pass
- Coverage >90% for witness system maintained

### Sub-Phase 3.4: Examples and Iteration Migration (0.5 days)

**Objective**: Complete bimodal migration with examples.py and iterate.py

#### Tasks
- [ ] **Migrate examples.py**
  - Replace: `import cvc5` with `from model_checker.solver import SolverFactory`
  - Add: `from model_checker.settings import settings`
  - Update: Solver creation via factory
  - Remove: Direct MBQI+enum-inst configuration (adapter handles)
  - Update: All solver operations to use adapter

- [ ] **Migrate iterate.py**
  - Add: Adapter parameter to functions
  - Replace: Solver methods with adapter methods
  - Update: Result checking (`isSat()` → `== "sat"`)

- [ ] **Update settings for testing**
  - Default: `settings.smt_solver = "cvc5"` (for Phase 3)
  - Test: Easy switching between "z3" and "cvc5"

- [ ] **Run all bimodal examples**
  - Execute: `./dev_cli.py bimodal/examples.py`
  - Verify: All 22 examples work
  - Validate: 6 critical examples solve correctly

#### Testing
```bash
# Run all examples with CVC5
cd Code
PYTHONPATH=src SMT_SOLVER=cvc5 ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py

# Run all examples with Z3 (regression)
PYTHONPATH=src SMT_SOLVER=z3 ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py
```

**Success Criteria**:
- examples.py uses SolverFactory
- iterate.py uses SolverInterface
- All 22 examples work with both solvers
- Solver selection via settings works

### Sub-Phase 3.5: Dual-Solver Validation (1 day)

**Objective**: Validate both Z3 and CVC5 backends through abstraction

#### Tasks
- [ ] **Run Z3 regression tests**
  - Settings: `smt_solver = "z3"`
  - Execute: Full bimodal test suite
  - Expected: All tests pass (backward compatibility)
  - Validate: No behavior changes from pre-abstraction

- [ ] **Run CVC5 performance tests**
  - Settings: `smt_solver = "cvc5"`
  - Execute: Performance validation suite
  - Expected: BM_CM_* examples ~6ms (Phase 1 performance maintained)
  - Validate: Abstraction overhead <5%

- [ ] **Run equivalence test suite**
  - Test: `test_solver_equivalence.py`
  - Execute: All 22 examples with both solvers
  - Compare: sat/unsat results
  - Validate: Semantic equivalence
  - Document: Any expected differences

- [ ] **Performance benchmarking**
  - Benchmark: 6 critical examples with both solvers
  - Measure: Abstraction overhead (compare to Phase 1 direct CVC5)
  - Target: <5% overhead
  - Document: Results in Phase 3 report

- [ ] **Memory and resource validation**
  - Check: No memory leaks
  - Verify: Resource cleanup
  - Test: Long-running examples

#### Testing
```bash
# Z3 regression (all tests with Z3)
PYTHONPATH=code/src SMT_SOLVER=z3 pytest code/src/model_checker/theory_lib/bimodal/tests/ -v

# CVC5 validation (all tests with CVC5)
PYTHONPATH=code/src SMT_SOLVER=cvc5 pytest code/src/model_checker/theory_lib/bimodal/tests/ -v

# Equivalence testing
PYTHONPATH=code/src pytest code/tests/integration/test_solver_equivalence.py -v

# Performance benchmarking
cd Code
nix-shell ../shell.nix --run "PYTHONPATH=src python3 benchmark_abstraction_overhead.py"
```

**Success Criteria**:
- Z3 backend: All regression tests pass
- CVC5 backend: Performance maintained (~6ms)
- Equivalence: Z3 and CVC5 produce same sat/unsat results
- Overhead: <5% abstraction overhead measured
- No resource leaks

### Sub-Phase 3.6: Documentation and Reporting (0.5 days)

**Objective**: Document migration and create Phase 3 report

#### Tasks
- [ ] **Update bimodal README**
  - File: `code/src/model_checker/theory_lib/bimodal/README.md`
  - Add: Solver selection instructions
  - Document: How to configure `settings.smt_solver`
  - Note: CVC5 recommended for witness predicates
  - Standards: No historical references

- [ ] **Create migration guide for theory developers**
  - File: `code/docs/development/THEORY_SOLVER_MIGRATION.md`
  - Content:
    - Step-by-step migration from direct solver to abstraction
    - API translation patterns
    - Common pitfalls and solutions
    - Testing strategy for dual-solver support
  - No historical references

- [ ] **Create Phase 3 results report**
  - File: `specs/reports/016_bimodal_abstraction_integration_results.md`
  - Content:
    - Migration summary (files changed, LOC)
    - Dual-solver validation results
    - Equivalence test results
    - Performance comparison (abstraction overhead)
    - Lessons learned for rollout to other theories

- [ ] **Update abstraction architecture docs**
  - File: `code/docs/architecture/SOLVER_ABSTRACTION.md`
  - Add: Real-world usage example (bimodal)
  - Document: Performance characteristics
  - Show: Migration patterns

- [ ] **Create final implementation summary**
  - File: `code/src/model_checker/theory_lib/bimodal/specs/cvc5/implementation_summary.md`
  - Content:
    - Complete Phase 1-3 journey
    - What was learned at each phase
    - Final architecture state
    - Recommendations for future work

#### Documentation Standards
- No historical references
- Clear examples with both Z3 and CVC5
- Performance characteristics documented
- Migration patterns explicit

**Success Criteria**:
- All documentation updated
- Migration guide complete for other theories
- Phase 3 results report written
- Implementation summary created

## Risk Mitigation

### Risk 1: Adapter Injection Complexity
**Risk**: Passing adapter through all functions increases complexity
**Impact**: Code verbosity, potential errors
**Mitigation**: Clear patterns, comprehensive tests
**Fallback**: Global adapter configuration (less flexible)

### Risk 2: Performance Degradation
**Risk**: Abstraction overhead >5%
**Impact**: Slower than Phase 1 direct CVC5
**Mitigation**: Profile and optimize hot paths
**Fallback**: Provide bypass mechanism for critical code

### Risk 3: Z3/CVC5 Result Differences
**Risk**: Solvers produce different sat/unsat on same formula
**Impact**: Equivalence tests fail
**Mitigation**: Document expected differences, validate semantics
**Fallback**: Restrict certain examples to specific solver

### Risk 4: Witness Predicate Issues
**Risk**: MBQI+enum-inst not configured correctly through abstraction
**Impact**: CVC5 returns "unknown" on witness predicates
**Mitigation**: Validate adapter configuration, explicit tests
**Fallback**: Manual configuration option in settings

### Risk 5: Import Complexity
**Risk**: Relative imports break or are confusing
**Impact**: Import errors, maintenance burden
**Mitigation**: Clear import standards, comprehensive examples
**Fallback**: Use absolute imports (less preferred)

## Dependencies

### External Dependencies
- **Z3**: Already installed and tested
- **CVC5**: Installed and validated in Phase 0
- **pytest**: Testing framework

### Internal Dependencies
- **Phase 1**: MUST be complete (bimodal CVC5 implementation)
- **Phase 2**: MUST be complete (abstraction layer with >90% coverage)
- **Phase 1 deliverables**: CVC5 patterns documented
- **Phase 2 deliverables**: SolverInterface, adapters, factory, settings

### Branch Dependencies
- **Base branch**: `feature/solver-abstraction` (Phase 2 complete)
- **New branch**: `feature/bimodal-solver-interface`
- **Merge target**: Main branch after Phase 3 validation

## Progress Tracking

### Completion Checklist

#### Sub-Phase 3.1: Integration Test Setup ☐
- [ ] test_bimodal_solver_interface.py written (RED)
- [ ] test_solver_equivalence.py written (RED)
- [ ] test_performance_validation.py written (RED)
- [ ] Test fixtures created
- [ ] Baselines established

#### Sub-Phase 3.2: Semantic Core ☐
- [ ] semantic.py imports updated
- [ ] Function signatures updated
- [ ] Type constructors migrated
- [ ] Logical operators migrated
- [ ] Quantifiers migrated
- [ ] Tests pass (GREEN)

#### Sub-Phase 3.3: Operators & Witness ☐
- [ ] operators.py migrated
- [ ] witness_constraints.py migrated
- [ ] witness_registry.py migrated
- [ ] Operator tests pass
- [ ] Witness tests pass (>90% coverage)

#### Sub-Phase 3.4: Examples & Iteration ☐
- [ ] examples.py migrated (factory)
- [ ] iterate.py migrated
- [ ] Settings integration works
- [ ] All 22 examples work

#### Sub-Phase 3.5: Dual-Solver Validation ☐
- [ ] Z3 regression tests pass
- [ ] CVC5 performance validated (~6ms)
- [ ] Equivalence tests pass
- [ ] Overhead <5% measured
- [ ] No resource leaks

#### Sub-Phase 3.6: Documentation ☐
- [ ] Bimodal README updated
- [ ] Migration guide created
- [ ] Phase 3 report written
- [ ] Architecture docs updated
- [ ] Implementation summary created

### Performance Metrics

| Example | Z3 Baseline | CVC5 Phase 1 | CVC5 Phase 3 | Overhead | Status |
|---------|-------------|--------------|--------------|----------|--------|
| BM_CM_1 | 5000ms+ | ~6ms | TBD | TBD | ☐ |
| BM_CM_2 | 5000ms+ | ~6ms | TBD | TBD | ☐ |
| TN_CM_1 | Timeout | ~0.2ms | TBD | TBD | ☐ |
| TN_CM_2 | Timeout | ~0.2ms | TBD | TBD | ☐ |
| MD_CM_1 | TBD | TBD | TBD | TBD | ☐ |
| MD_CM_2 | TBD | TBD | TBD | TBD | ☐ |

**Target**: Overhead <5% (CVC5 Phase 3 vs Phase 1)

### Equivalence Test Results

| Example | Z3 Result | CVC5 Result | Agreement | Status |
|---------|-----------|-------------|-----------|--------|
| BM_CM_1 | TBD | TBD | TBD | ☐ |
| BM_CM_2 | TBD | TBD | TBD | ☐ |
| ... (all 22) | | | | |

**Target**: 100% sat/unsat agreement (or documented differences)

### Test Coverage Metrics

| Component | Phase 1 | Phase 3 Target | Current | Status |
|-----------|---------|----------------|---------|--------|
| semantic.py | >85% | >85% | - | ☐ |
| operators.py | >85% | >85% | - | ☐ |
| witness_constraints.py | >90% | >90% | - | ☐ |
| witness_registry.py | >90% | >90% | - | ☐ |
| examples.py | >85% | >85% | - | ☐ |
| iterate.py | >85% | >85% | - | ☐ |
| **Overall** | **>85%** | **>85%** | - | ☐ |

## Next Steps

**Upon Phase 3 Completion**:
1. ✓ Create Phase 3 results report
2. ✓ Update master plan with final integration results
3. → **Rollout to Other Theories**: Apply patterns to exclusion, imposition, logos
4. Use bimodal as reference implementation
5. Systematic migration across all theories

**Theory Rollout Preview** (Future Phases 4-7):
- **Exclusion theory**: Apply same migration pattern
- **Imposition theory**: Apply same migration pattern
- **Logos theory**: Apply same migration pattern
- **Core infrastructure**: Migrate iterate, builder, models packages
- **Documentation**: Complete project-wide docs

**Deliverables from Phase 3**:
- Bimodal theory using SolverInterface (reference implementation)
- Dual-solver validation (Z3 and CVC5 equivalence proven)
- Performance overhead analysis (<5% validated)
- Migration guide for theory developers
- Comprehensive test suite (>85% coverage maintained)
- Complete Phase 1-3 implementation summary

**Success Indicators**:
- Abstraction layer proven with real theory
- Both solvers work transparently
- Performance goals achieved
- Migration patterns clear for rollout
- No regressions in existing functionality
