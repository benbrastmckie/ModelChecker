# Phase 2: Abstraction Layer Implementation

## Overview

Phase 2 creates a thin abstraction layer enabling dual Z3/CVC5 support through pluggable solver adapters. This phase builds on patterns learned from Phase 1's bimodal CVC5 pilot migration.

**Duration**: 1.5 weeks (9 days)
**Stages**: 5
**Status**: 🚀 READY TO START

## Quick Navigation

### Stage Plans
- [Stage 01: Interface & Capabilities](stage01_interface_capabilities.md) - 2 days
- [Stage 02: Z3SolverAdapter](stage02_z3_adapter.md) - 2 days
- [Stage 03: CVC5SolverAdapter](stage03_cvc5_adapter.md) - 3 days
- [Stage 04: Factory & Integration](stage04_factory_integration.md) - 1.5 days
- [Stage 05: Documentation & Validation](stage05_documentation_validation.md) - 0.5 days

### Progress Tracking
- [Stage Index](STAGE_INDEX.md) - Complete stage breakdown and progress tracking
- [Phase 2 Design Document](phase2_abstraction_layer_design.md) - Full technical design

### Related Documents
- [Master Plan](../MASTER_PLAN.md) - Overall 3-phase roadmap
- [Phase 1 Index](../phase1_pilot/STAGE_INDEX.md) - Completed bimodal CVC5 pilot

## Objectives

### Primary Goals
1. **SolverInterface**: Define complete solver-agnostic API (~35 methods)
2. **Dual Adapters**: Implement Z3 and CVC5 adapters
3. **Runtime Selection**: Enable solver choice via settings
4. **Performance**: Maintain <5% abstraction overhead
5. **Standards**: NO decorators, >90% coverage

### Success Criteria
- [ ] SolverInterface defines complete API
- [ ] Z3SolverAdapter backward compatible (100%)
- [ ] CVC5SolverAdapter uses Phase 1 patterns
- [ ] SolverFactory enables runtime selection
- [ ] Test coverage >90% for abstraction layer
- [ ] NO decorators anywhere in solver package

## Key Design Principles

1. **Thin Wrapper**: Direct API access for performance, minimal abstraction
2. **Explicit Capabilities**: Declare solver features upfront (quantifiers, MBQI, patterns)
3. **Adapter Pattern**: Separate formula representation from solver interaction
4. **NO Decorators**: Follow CODE_STANDARDS.md - explicit methods only
5. **TDD-First**: All code has tests written before implementation

## Implementation Approach

### Stage Progression

```
Phase 1 Learnings
    ↓
Stage 1: Interface & Capabilities (2 days)
    ↓
    ├→ Stage 2: Z3SolverAdapter (2 days)
    │
    └→ Stage 3: CVC5SolverAdapter (3 days)
          ↓
       Stage 4: Factory & Integration (1.5 days)
          ↓
       Stage 5: Documentation (0.5 days)
          ↓
       Phase 3: Bimodal Integration
```

### TDD Workflow

**Every Stage Follows**:
1. Write tests FIRST (RED)
2. Implement to pass tests (GREEN)
3. Refactor for quality (maintain GREEN)
4. Verify coverage >90%
5. Commit changes

## File Structure

### New Files Created

```
code/src/model_checker/solver/
├── interface.py              (~250 LOC)  # SolverInterface ABC
├── capabilities.py           (~140 LOC)  # CapabilityMatrix
├── z3_adapter.py            (~350 LOC)  # Z3 implementation
├── cvc5_adapter.py          (~450 LOC)  # CVC5 implementation
├── factory.py               (~100 LOC)  # SolverFactory
├── __init__.py              (~20 LOC)   # Package exports
└── tests/
    ├── unit/
    │   ├── test_interface.py         (~200 LOC)
    │   ├── test_capabilities.py      (~150 LOC)
    │   ├── test_z3_adapter.py        (~300 LOC)
    │   ├── test_cvc5_adapter.py      (~350 LOC)
    │   └── test_factory.py           (~150 LOC)
    └── integration/
        └── test_adapter_equivalence.py  (~200 LOC)
```

**Total**: ~2,660 LOC across 12 files

### Modified Files

- `code/src/model_checker/settings/settings.py` - Add smt_solver configuration

## Critical Standards

### NO DECORATORS (CODE_STANDARDS.md)

```python
# CORRECT - No decorators
from abc import ABC

class SolverInterface(ABC):
    def create_solver(self) -> Any:
        """Create solver instance."""
        raise NotImplementedError("Subclasses must implement create_solver()")
```

### Relative Imports

```python
# Within solver package
from .interface import SolverInterface
from .capabilities import CapabilityMatrix
```

### User-Friendly Errors

```python
raise ValueError(
    f"Unknown solver: '{solver_name}'. "
    f"Available solvers: z3, cvc5\n"
    f"To add a solver, see code/docs/architecture/SOLVER_ABSTRACTION.md"
)
```

## Testing Strategy

### Coverage Targets
- **Abstraction Layer**: >90% (critical path requirement)
- **Overall Affected Code**: >85%

### Test Commands

```bash
# Run all Phase 2 tests
PYTHONPATH=code/src pytest code/src/model_checker/solver/tests/ -v

# Coverage check (required >90%)
PYTHONPATH=code/src pytest code/src/model_checker/solver/tests/ \
    --cov=model_checker.solver \
    --cov-report=term-missing \
    --cov-fail-under=90
```

## Deliverables

### Code Deliverables
- [x] Complete abstraction layer (6 source files)
- [x] Comprehensive test suite (6 test files)
- [x] Settings integration

### Documentation Deliverables
- [ ] Solver package README
- [ ] Architecture documentation (SOLVER_ABSTRACTION.md)
- [ ] Phase 2 results report (specs/reports/015_abstraction_layer_results.md)

## Next Steps

**To Begin Phase 2**:
1. Review [Phase 2 Design Document](phase2_abstraction_layer_design.md)
2. Read [Stage 01 Plan](stage01_interface_capabilities.md)
3. Create branch: `git checkout -b feature/solver-abstraction`
4. Start Stage 1 TDD cycle

**After Phase 2 Completion**:
- Proceed to Phase 3: Bimodal Abstraction Integration
- Migrate bimodal theory to use SolverInterface
- Validate dual-solver support

## Resources

### Documentation
- [CODE_STANDARDS.md](../../../../../../code/docs/core/CODE_STANDARDS.md)
- [TESTING.md](../../../../../../code/docs/core/TESTING.md)
- [ARCHITECTURE.md](../../../../../../code/docs/core/ARCHITECTURE.md)

### Reports
- Report 011: Z3→CVC5 API Translation Patterns
- Report 012: CVC5 Feasibility Results
- Report 013: Phase 1 API Patterns (to be created)
- Report 015: Phase 2 Results (to be created)

---

**Phase 2 Version**: 1.0
**Created**: 2025-10-03
**Status**: Ready to start
