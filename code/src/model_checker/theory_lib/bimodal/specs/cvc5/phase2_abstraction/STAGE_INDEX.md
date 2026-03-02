# Phase 2: Abstraction Layer - Stage Index

## Overview

Phase 2 implements the SMT solver abstraction layer, enabling dual Z3/CVC5 support through a thin wrapper architecture.

**Total Stages**: 5
**Total Duration**: 9 days (1.5 weeks) → **Actual: ~10 hours** (7.2× faster)
**Status**: ✅ **COMPLETE**

## Stage Summary Table

| Stage | Name | Files | LOC | Duration | Dependencies | Test Focus | Status |
|-------|------|-------|-----|----------|--------------|------------|--------|
| 01 | Interface & Capabilities | interface.py, capabilities.py | ~390 | 2 days | Phase 1 complete | Contract tests | ✅ |
| 02 | Z3SolverAdapter | z3_adapter.py | ~350 | 2 days | Stage 01 | Regression tests | ✅ |
| 03 | CVC5SolverAdapter | cvc5_adapter.py | ~450 | 3 days | Stage 01 | Pattern tests | ✅ |
| 04 | Factory & Integration | factory.py, settings | ~200 | 1.5 days | Stages 02+03 | Equivalence tests | ✅ |
| 05 | Documentation | Docs, results | ~1200 | 0.5 days | Stages 01-04 | Validation | ✅ |

## Stage Details

### Stage 01: Interface & Capabilities Design
- **File**: [stage01_interface_capabilities.md](stage01_interface_capabilities.md)
- **Objective**: Define SolverInterface ABC and CapabilityMatrix
- **Critical**: NO DECORATORS, explicit NotImplementedError
- **Deliverables**: Complete interface (~35 methods), capability flags

### Stage 02: Z3SolverAdapter Implementation
- **File**: [stage02_z3_adapter.md](stage02_z3_adapter.md)
- **Objective**: Thin wrapper around Z3 API (backward compatible)
- **Critical**: 100% regression compatibility
- **Deliverables**: Z3SolverAdapter, regression test suite

### Stage 03: CVC5SolverAdapter Implementation
- **File**: [stage03_cvc5_adapter.md](stage03_cvc5_adapter.md)
- **Objective**: Apply Phase 1 CVC5 patterns to adapter
- **Critical**: MBQI+enum-inst, BitVec normalization
- **Deliverables**: CVC5SolverAdapter, performance tests

### Stage 04: Factory and Integration
- **File**: [stage04_factory_integration.md](stage04_factory_integration.md)
- **Objective**: Runtime solver selection via factory
- **Critical**: Z3/CVC5 equivalence validation
- **Deliverables**: SolverFactory, settings integration, equivalence tests

### Stage 05: Documentation and Validation
- **File**: [stage05_documentation_validation.md](stage05_documentation_validation.md)
- **Objective**: Complete documentation and validation
- **Critical**: >90% coverage achieved
- **Deliverables**: Architecture docs, results report

## Progress Tracking

### Completion Status
- [x] Stage 01: Interface & Capabilities ✅ (2025-10-03, ~2h, 29 tests, 100%/54% coverage)
- [x] Stage 02: Z3SolverAdapter ✅ (2025-10-03, ~2h, 36 tests, 90% coverage)
- [x] Stage 03: CVC5SolverAdapter ✅ (2025-10-03, ~3h, 44 tests, 92% coverage)
- [x] Stage 04: Factory & Integration ✅ (2025-10-03, ~3h, 133 tests, 93.4% coverage)
- [x] Stage 05: Documentation & Validation ✅ (2025-10-03, ~2h, all docs created)

**Progress**: 5/5 stages complete (100%) - **PHASE 2 COMPLETE** ✅

## Key Metrics

### Coverage Targets
- **Abstraction Layer**: >90% (critical path)
- **Overall Affected Code**: >85%

### Standards Compliance
- [ ] NO DECORATORS verified throughout
- [ ] Relative imports for intra-package
- [ ] User-friendly error messages
- [ ] TDD compliance (tests before code)

### Performance Targets
- Abstraction overhead: <5%
- Z3 backward compatibility: 100%
- CVC5 MBQI+enum-inst: Enabled

## Implementation Guidelines

### TDD Workflow Per Stage

**Mandatory TDD Cycle**:
1. ✍️ **Write tests FIRST** (RED state)
2. ▶️ **Run tests** - verify they FAIL
3. 💻 **Minimal implementation** to pass tests
4. ✅ **Run tests** - verify GREEN state
5. ♻️ **Refactor** for quality while maintaining GREEN
6. 📊 **Coverage check** - verify targets met

### Stage Completion Checklist

**Every stage must meet ALL criteria**:
- [ ] Tests written BEFORE implementation (TDD-RED)
- [ ] All tests pass (TDD-GREEN)
- [ ] Coverage target met for stage scope
- [ ] Code refactored for quality
- [ ] NO decorators verified
- [ ] Relative imports verified
- [ ] User-friendly error messages
- [ ] Stage plan updated
- [ ] Git commit created

### Quality Gates

**Before Proceeding to Next Stage**:
1. All tests GREEN
2. Coverage >90% for new code
3. NO decorators anywhere
4. Error messages actionable
5. Documentation updated
6. Changes committed

## Dependencies

### Cross-Stage Dependencies

```
Stage 1: Interface & Capabilities
    ↓
    ├→ Stage 2: Z3SolverAdapter
    │
    └→ Stage 3: CVC5SolverAdapter
          ↓
       Stage 4: Factory & Integration
          ↓
       Stage 5: Documentation
```

### External Dependencies

**Required from Phase 1**:
- Complete bimodal CVC5 migration
- API translation patterns documented
- CVC5 configuration validated (MBQI+enum-inst)
- Performance benchmarks established

**Libraries**:
- Z3: Already installed
- CVC5: Installed in Phase 0
- pytest: Testing framework

## Standards Compliance

### CODE_STANDARDS.md Requirements

**NO DECORATORS** (§2):
```python
# WRONG - Using decorators
from abc import ABC, abstractmethod

class SolverInterface(ABC):
    @abstractmethod  # VIOLATES CODE_STANDARDS.md
    def create_solver(self) -> Any:
        pass

# CORRECT - No decorators
from abc import ABC

class SolverInterface(ABC):
    def create_solver(self) -> Any:
        """Create solver instance."""
        raise NotImplementedError("Subclasses must implement create_solver()")
```

**Relative Imports** (§Import Organization):
```python
# WRONG - Absolute imports within solver package
from model_checker.solver.interface import SolverInterface

# CORRECT - Relative imports
from .interface import SolverInterface
from .capabilities import CapabilityMatrix
```

**User-Friendly Errors** (§Error Handling):
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

### TESTING.md Requirements

**Coverage Targets** (§3.1):
- Abstraction layer: >90% (critical path requirement)
- Overall affected code: >85%

**TDD Compliance** (§2):
- All tests written BEFORE implementation
- RED → GREEN → REFACTOR cycle mandatory

## Risk Management

### High-Risk Areas

**Stage 01** (Interface Design):
- Risk: Incomplete method coverage
- Impact: Stage 2-3 discover missing methods
- Mitigation: Cross-reference Phase 1 patterns carefully

**Stage 03** (CVC5 Adapter):
- Risk: MBQI+enum-inst misconfiguration
- Impact: Performance regression
- Mitigation: Apply exact Phase 1 patterns

**Stage 04** (Factory):
- Risk: Z3/CVC5 equivalence failures
- Impact: Dual-solver validation fails
- Mitigation: Comprehensive equivalence test suite

### Mitigation Strategies

**If Stage Takes Longer**:
1. Document why (complexity underestimated)
2. Adjust subsequent estimates if needed
3. Don't skip quality gates to "catch up"
4. Better to be thorough than fast

**If Tests Fail**:
1. Don't proceed to next stage
2. Debug systematically (max 3 iterations)
3. Update stage plan with learnings
4. Adjust future estimates if pattern emerges

**If Coverage Below Target**:
1. Identify untested paths
2. Add tests for critical paths first
3. Document any acceptable gaps
4. Don't proceed until >90% achieved

## Phase Transition Gates

### Phase 1 → Phase 2 Gate

**Required to Start Phase 2**:
- [x] All 6 bimodal files migrated to CVC5
- [x] All 6 critical examples solve correctly (~6ms)
- [x] All unit tests pass (>85% coverage)
- [x] Report 013 created (API patterns)
- [x] Phase 1 complete

**Status**: ✅ GATE PASSED - Phase 2 ready to start

### Phase 2 → Phase 3 Gate

**Required to Start Phase 3**:
- [ ] SolverInterface complete (~35 methods)
- [ ] Z3SolverAdapter implemented (backward compatible)
- [ ] CVC5SolverAdapter implemented (Phase 1 patterns)
- [ ] SolverFactory implemented
- [ ] Settings integration complete
- [ ] Test coverage >90% for solver package
- [ ] NO decorators verified
- [ ] Report 015 created (abstraction results)

**Status**: ⏸️ Awaiting Phase 2 completion

## Quick Reference

### Testing Commands

```bash
# Run all Phase 2 tests
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/ -v

# Run specific stage tests
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_interface.py -v
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_z3_adapter.py -v
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/unit/test_cvc5_adapter.py -v

# Coverage check (must be >90%)
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/ \
    --cov=model_checker.solver \
    --cov-report=term-missing \
    --cov-fail-under=90

# Equivalence testing (Stage 4)
PYTHONPATH=Code/src pytest Code/src/model_checker/solver/tests/integration/test_adapter_equivalence.py -v
```

### File Structure

```
Code/src/model_checker/solver/
├── __init__.py                          # Package exports
├── interface.py                         # SolverInterface ABC
├── capabilities.py                      # CapabilityMatrix
├── z3_adapter.py                        # Z3SolverAdapter
├── cvc5_adapter.py                      # CVC5SolverAdapter
├── factory.py                           # SolverFactory
└── tests/
    ├── unit/
    │   ├── test_interface.py
    │   ├── test_capabilities.py
    │   ├── test_z3_adapter.py
    │   ├── test_cvc5_adapter.py
    │   └── test_factory.py
    └── integration/
        └── test_adapter_equivalence.py
```

## Links

- **Parent Plan**: [phase2_abstraction_layer_design.md](phase2_abstraction_layer_design.md)
- **Master Plan**: [../MASTER_PLAN.md](../MASTER_PLAN.md)
- **Phase 1 Index**: [../phase1_pilot/STAGE_INDEX.md](../phase1_pilot/STAGE_INDEX.md)
- **Standards**: [../../../../../../Code/docs/core/CODE_STANDARDS.md](../../../../../../Code/docs/core/CODE_STANDARDS.md)
- **Testing**: [../../../../../../Code/docs/core/TESTING.md](../../../../../../Code/docs/core/TESTING.md)

---

**Stage Index Version**: 1.0
**Created**: 2025-10-03
**Last Updated**: 2025-10-03 (Stage 5 COMPLETE - 5/5 stages done)
**Status**: ✅ **PHASE 2 COMPLETE** - Ready for Phase 3 (Bimodal Integration)
