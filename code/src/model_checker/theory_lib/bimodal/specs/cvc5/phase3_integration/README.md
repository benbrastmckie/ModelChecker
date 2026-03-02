# Phase 3: Bimodal Theory Abstraction Integration

## Overview

Phase 3 migrates the bimodal theory from direct CVC5 usage to the SolverInterface abstraction layer, enabling dual Z3/CVC5 support with runtime solver selection.

**Objective**: Prove the abstraction layer works with real theory code while maintaining performance and enabling solver flexibility.

**Duration**: 5 days (6 stages)

**Status**: 🚀 Ready to Start

## Prerequisites

✅ **Phase 1 Complete**: Bimodal theory migrated to CVC5
- 6 critical examples validated (~6ms performance)
- API translation patterns documented
- Witness predicate system working with MBQI+enum-inst

✅ **Phase 2 Complete**: Abstraction layer implemented
- SolverInterface with ~35 methods
- Z3SolverAdapter and CVC5SolverAdapter
- SolverFactory for runtime selection
- >90% test coverage on abstraction layer

✅ **Solver Package Ready**:
- Z3 adapter (backward compatible)
- CVC5 adapter (Phase 1 patterns applied)
- Runtime solver selection via factory

## Stages

### [Stage 1: Integration Test Setup](stage01_integration_test_setup.md) (1 day)
**Objective**: Write integration tests BEFORE migration (TDD-RED)

- Write test_bimodal_solver_interface.py (tests FAIL initially)
- Write test_solver_equivalence.py (Z3 vs CVC5)
- Write test_performance_validation.py (maintain ~6ms)
- Create test fixtures for dual-solver testing

**Success**: All tests written and failing as expected (RED state verified)

### [Stage 2: Semantic Core Migration](stage02_semantic_core_migration.md) (1 day)
**Objective**: Migrate semantic.py to SolverInterface

- Update imports (remove `import cvc5`)
- Change function signatures to accept `adapter: SolverInterface`
- Migrate type constructors, operators, quantifiers
- Simplify ForAll creation (no manual VARIABLE_LIST)

**Success**: semantic.py uses SolverInterface, unit tests pass

### [Stage 3: Operators and Witness Migration](stage03_operators_witness_migration.md) (1 day)
**Objective**: Migrate operators and witness system (CRITICAL)

- Migrate operators.py (Box, Diamond, Future, Past)
- Migrate witness_constraints.py (>90% coverage required)
- Migrate witness_registry.py
- Validate MBQI+enum-inst configuration through adapter

**Success**: Operators and witness system use SolverInterface, >90% coverage

### [Stage 4: Examples and Iteration Migration](stage04_examples_iteration_migration.md) (0.5 days)
**Objective**: Complete migration with examples.py and iterate.py

- Migrate examples.py to SolverFactory
- Update iterate.py with adapter parameter
- Configure runtime solver selection via settings
- All 22 examples work with both solvers

**Success**: Solver selection works, all examples run with Z3 and CVC5

### [Stage 5: Dual-Solver Validation](stage05_dual_solver_validation.md) (1 day)
**Objective**: Validate both Z3 and CVC5 backends

- Z3 regression testing (all tests pass)
- CVC5 performance validation (~6ms maintained)
- Equivalence testing (Z3/CVC5 agreement)
- Performance benchmarking (<5% overhead)

**Success**: Both solvers validated, performance targets met

### [Stage 6: Documentation and Reporting](stage06_documentation_reporting.md) (0.5 days)
**Objective**: Document migration and create Phase 3 report

- Update bimodal README with solver selection
- Create migration guide for theory developers
- Write Phase 3 results report
- Update architecture documentation

**Success**: All documentation complete, migration patterns documented

## Quick Start

### 1. Verify Prerequisites
```bash
# Check Phase 2 abstraction layer
PYTHONPATH=code/src python -c "from model_checker.solver import SolverFactory; print('✅ Abstraction layer ready')"

# Check adapters available
PYTHONPATH=code/src python -c "from model_checker.solver import SolverFactory; f = SolverFactory(); print(f._ADAPTERS.keys())"
# Expected: dict_keys(['z3', 'cvc5'])
```

### 2. Start with Stage 1 (TDD-RED)
```bash
# Begin implementation
cd code/src/model_checker/theory_lib/bimodal/specs/cvc5/phase3_integration
# Read stage01_integration_test_setup.md
# Write integration tests (they will FAIL - this is expected!)
```

### 3. Progress Through Stages
```bash
# Stage 2: Migrate semantic.py
# Stage 3: Migrate operators & witness
# Stage 4: Migrate examples & iterate
# Stage 5: Validate both solvers
# Stage 6: Document everything
```

### 4. Verify Completion
```bash
# All integration tests should PASS
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/ -v

# Run examples with both solvers
PYTHONPATH=code/src SMT_SOLVER=z3 ./dev_cli.py bimodal/examples.py
PYTHONPATH=code/src SMT_SOLVER=cvc5 ./dev_cli.py bimodal/examples.py
```

## Key Success Criteria

### Functional
- [ ] Bimodal theory works with SolverInterface (no direct CVC5)
- [ ] Z3 backend passes all existing tests (regression)
- [ ] CVC5 backend maintains performance (~6ms on BM_CM_*)
- [ ] Runtime solver selection via settings works
- [ ] All 22 examples work with both solvers

### Quality
- [ ] TDD compliance: Tests written BEFORE migration
- [ ] Test coverage >85% maintained for bimodal
- [ ] Witness predicate coverage >90% maintained
- [ ] Integration tests validate both solvers
- [ ] Equivalence tests compare Z3 vs CVC5 results

### Performance
- [ ] Abstraction overhead <5% (both solvers)
- [ ] CVC5 performance: BM_CM_* ~6ms
- [ ] Z3 performance unchanged from baseline
- [ ] No memory leaks or resource issues

## Testing Strategy

### TDD Workflow
1. **RED**: Stage 1 writes tests that FAIL (bimodal not using abstraction)
2. **GREEN**: Stages 2-4 migrate code, tests start passing
3. **REFACTOR**: Clean up while keeping tests GREEN
4. **VALIDATE**: Stage 5 comprehensive dual-solver testing

### Test Layers
- **Unit Tests**: Verify each component uses SolverInterface
- **Integration Tests**: Validate examples work with both solvers
- **Equivalence Tests**: Ensure Z3/CVC5 produce same results
- **Performance Tests**: Measure abstraction overhead

## Migration Patterns

### Import Changes
```python
# Before (Phase 1 - Direct CVC5)
import cvc5
from cvc5 import Kind

# After (Phase 3 - Abstraction)
from model_checker.solver import SolverInterface
```

### Function Signature Changes
```python
# Before
def define_semantics(solver):
    bool_sort = solver.getBooleanSort()
    # ...

# After
def define_semantics(adapter: SolverInterface):
    solver = adapter.create_solver()
    bool_sort = adapter.mk_bool_sort()
    # ...
```

### API Translation
```python
# Before: CVC5 API
solver.mkTerm(Kind.AND, a, b)

# After: SolverInterface
adapter.mk_and(a, b)
```

## Performance Targets

| Metric | Target | Measurement |
|--------|--------|-------------|
| Abstraction Overhead | <5% | Compare Phase 3 to Phase 1 times |
| CVC5 BM_CM_1 | ~6ms | Should match Phase 1 performance |
| CVC5 BM_CM_2 | ~6ms | Should match Phase 1 performance |
| Z3 Regression | No change | Compare to pre-Phase 1 baseline |

## Navigation

### Stage Files
- [STAGE_INDEX.md](STAGE_INDEX.md) - Progress tracking and metrics
- [stage01_integration_test_setup.md](stage01_integration_test_setup.md)
- [stage02_semantic_core_migration.md](stage02_semantic_core_migration.md)
- [stage03_operators_witness_migration.md](stage03_operators_witness_migration.md)
- [stage04_examples_iteration_migration.md](stage04_examples_iteration_migration.md)
- [stage05_dual_solver_validation.md](stage05_dual_solver_validation.md)
- [stage06_documentation_reporting.md](stage06_documentation_reporting.md)

### Phase Documents
- [Phase 3 Main Plan](phase3_bimodal_abstraction_integration.md) - Comprehensive plan
- [Back to MASTER_PLAN](../MASTER_PLAN.md) - Overall project tracking
- [Phase 1 Index](../phase1_pilot/STAGE_INDEX.md) - CVC5 pilot reference
- [Phase 2 Index](../phase2_abstraction/STAGE_INDEX.md) - Abstraction layer reference

### Related Documentation
- [Solver Abstraction Architecture](../../../../../../docs/architecture/SOLVER_ABSTRACTION.md)
- [Phase 2 Report 015](../../../../../../../specs/reports/015_abstraction_layer_results.md)
- [CODE_STANDARDS.md](../../../../../../docs/core/CODE_STANDARDS.md)
- [TESTING.md](../../../../../../docs/core/TESTING.md)

## Support

### Common Issues
See individual stage files for Common Issues & Solutions sections.

### Debugging
- Verify adapter injection at each level
- Check MBQI+enum-inst configuration (CVC5 only)
- Compare to Phase 1 direct CVC5 implementation
- Use equivalence tests to isolate solver-specific issues

### References
- Phase 1 patterns: Direct CVC5 usage for comparison
- Phase 2 examples: SolverInterface usage patterns
- Integration tests: Dual-solver validation approach

---

**Version**: 1.0
**Created**: 2025-10-03
**Status**: Ready for Implementation
**Next**: Begin with [Stage 1: Integration Test Setup](stage01_integration_test_setup.md)
