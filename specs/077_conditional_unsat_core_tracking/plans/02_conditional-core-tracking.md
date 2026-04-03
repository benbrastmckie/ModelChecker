# Implementation Plan: Conditional Unsat Core Tracking

- **Task**: 77 - conditional_unsat_core_tracking
- **Status**: [NOT STARTED]
- **Effort**: 3.5 hours
- **Dependencies**: Task 79 (CVC5 solver options tuning) for performance optimizations
- **Research Inputs**:
  - reports/01_unsat-core-overhead.md (overhead benchmarks)
  - reports/02_conditional-design.md (design recommendation)
- **Artifacts**: plans/02_conditional-core-tracking.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md, tasks.md
- **Type**: z3

## Overview

Implement conditional unsat core tracking for CVC5 solver to improve performance on UNSAT examples. Research found that the combination of `produce-unsat-cores=true` with tracked assertions creates 4-5x overhead (not the option alone). By auto-detecting whether cores are needed from existing print settings, we can bundle Task 79 optimizations (`decision=stoponly`, `bv-eager-eval=true`) into a "performance mode" that reduces CVC5's performance gap from 8.9x to 1.65x slower than Z3.

### Research Integration

- **Round 1** (01_unsat-core-overhead.md): Measured unsat core overhead at 10-30% (~0.1ms), but this alone does not explain 25-35x slowdown. Identified all code paths calling `solver.unsat_core()`.
- **Round 2** (02_conditional-design.md): Discovered that the combination of tracked assertions with proof production creates the major overhead. Designed settings-based auto-detection mechanism using `print_constraints` and `print_z3` flags.

## Goals & Non-Goals

**Goals**:
- Add `need_unsat_cores` parameter to `CVC5SolverAdapter.__init__()`
- Implement diagnostic mode (cores enabled) and performance mode (cores disabled with optimizations)
- Auto-detect mode from existing settings in `create_solver()`
- Handle empty unsat cores gracefully in consuming code paths
- Achieve ~5x speedup on CVC5 UNSAT examples

**Non-Goals**:
- Changing Z3 adapter behavior (overhead is negligible)
- Adding new user-facing settings (use existing `print_constraints`/`print_z3`)
- Modifying the iteration system (it does not use unsat cores)
- Investigating other CVC5 performance issues (separate tasks 78-80)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Silent loss of core data when user expects it | High | Low | Auto-detection from print settings ensures cores available when needed |
| Regression in constraint printing | High | Low | Test `print_constraints=True` path explicitly |
| CVC5 option compatibility issues | Medium | Low | Test both modes with CVC5 version in use |
| Empty core confuses downstream code | Medium | Medium | Update `_get_relevant_constraints()` to handle gracefully |

## Implementation Phases

### Phase 1: CVC5 Adapter Mode Configuration [NOT STARTED]

**Goal**: Add diagnostic/performance mode switching to CVC5SolverAdapter

**Tasks**:
- [ ] Add `need_unsat_cores: bool = True` parameter to `CVC5SolverAdapter.__init__()`
- [ ] Add `self._need_unsat_cores` instance variable
- [ ] Create `_configure_diagnostic_mode()` method that sets `produce-unsat-cores=true`
- [ ] Create `_configure_performance_mode()` method that sets `decision=stoponly` and `bv-eager-eval=true`
- [ ] Update constructor to call appropriate mode configuration
- [ ] Update `unsat_core()` method to return empty list when `_need_unsat_cores=False`
- [ ] Verify `reset()` preserves mode configuration

**Timing**: 1 hour

**Files to modify**:
- `code/src/model_checker/solver/cvc5_adapter.py` - Main adapter changes

**Verification**:
- Unit test: Adapter initializes with correct mode based on parameter
- Unit test: `unsat_core()` returns empty list when disabled
- Unit test: `reset()` preserves mode

---

### Phase 2: Registry Integration [NOT STARTED]

**Goal**: Auto-detect core requirement from settings in solver factory

**Tasks**:
- [ ] Update `create_solver()` signature to accept `settings: Optional[Dict[str, Any]] = None`
- [ ] Add logic to detect if cores needed: `settings.get('print_constraints', False) or settings.get('print_z3', False)`
- [ ] Pass `need_unsat_cores` parameter to `CVC5SolverAdapter` constructor
- [ ] Keep Z3 adapter unchanged (always track cores, negligible overhead)
- [ ] Update type hints for settings parameter

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/solver/registry.py` - Factory function update

**Verification**:
- Unit test: `create_solver()` passes correct mode to CVC5 adapter
- Unit test: Settings with `print_constraints=True` enables cores
- Unit test: Default settings (no print flags) disables cores

---

### Phase 3: Structure.py Safety Updates [NOT STARTED]

**Goal**: Handle empty unsat cores gracefully in consuming code paths

**Tasks**:
- [ ] Update `_get_relevant_constraints()` to check `len(self.unsat_core) > 0`
- [ ] Add informative message "UNSATISFIABLE (core not available)" when core is empty
- [ ] Return all constraints when core unavailable (fallback behavior)
- [ ] Verify `print_grouped_constraints()` handles empty core
- [ ] Check `print_model()` behavior with empty core

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/models/structure.py` - Core consumer safety

**Verification**:
- Test: UNSAT without print flags shows clean output (no error)
- Test: UNSAT with `print_constraints=True` shows core constraints
- Manual verification of output formatting

---

### Phase 4: Testing and Verification [NOT STARTED]

**Goal**: Comprehensive testing of both modes and performance validation

**Tasks**:
- [ ] Write unit tests for CVC5 adapter mode switching
- [ ] Write integration tests verifying correct mode selection from settings
- [ ] Run existing test suite to catch regressions
- [ ] Benchmark UNSAT examples with both modes to verify speedup
- [ ] Test `print_constraints=True` path end-to-end
- [ ] Test `print_z3=True` path end-to-end
- [ ] Document performance improvement in task summary

**Timing**: 1.25 hours

**Files to modify/create**:
- `code/tests/test_solver/test_cvc5_adapter.py` - New/extended tests
- `code/tests/test_solver/test_registry.py` - Factory tests

**Verification**:
- All tests pass
- Performance benchmark shows expected ~5x improvement on CVC5 UNSAT
- No regressions in print_constraints functionality

## Testing & Validation

- [ ] Unit tests for CVC5 adapter constructor with both mode values
- [ ] Unit tests for `unsat_core()` returning empty list when disabled
- [ ] Unit tests for registry `create_solver()` settings detection
- [ ] Integration test: full solve with `print_constraints=False` (performance mode)
- [ ] Integration test: full solve with `print_constraints=True` (diagnostic mode)
- [ ] Regression test: curated UNSAT examples produce correct output with cores enabled
- [ ] Performance test: measure time improvement on UNSAT examples

## Artifacts & Outputs

- `code/src/model_checker/solver/cvc5_adapter.py` - Modified adapter with mode switching
- `code/src/model_checker/solver/registry.py` - Modified factory with settings detection
- `code/src/model_checker/models/structure.py` - Modified consumer with empty core handling
- `code/tests/test_solver/test_cvc5_adapter.py` - New adapter tests
- `specs/077_conditional_unsat_core_tracking/summaries/02_conditional-core-tracking-summary.md` - Implementation summary

## Rollback/Contingency

If implementation causes issues:

1. **Revert to diagnostic mode only**: Change `need_unsat_cores` default to `True` and skip settings detection - this preserves current behavior
2. **Git revert**: All changes are in three files plus tests; clean revert is straightforward
3. **Feature flag**: Could add explicit `diagnostic_mode` setting as override if auto-detection proves insufficient

The implementation is designed for safe rollback since diagnostic mode (cores enabled) matches current behavior exactly.
