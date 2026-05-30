# Implementation Summary: Conditional Unsat Core Tracking

- **Task**: 77 - conditional_unsat_core_tracking
- **Status**: [COMPLETED]
- **Session**: sess_1775263550_d2e8a1
- **Date**: 2026-04-03

## Overview

Implemented conditional unsat core tracking for CVC5 solver with auto-detection from print settings. The implementation enables a performance mode that disables unsat core tracking and enables CVC5 optimizations when cores are not needed.

## Changes Made

### Phase 1: CVC5 Adapter Mode Configuration

**File**: `code/src/model_checker/solver/cvc5_adapter.py`

- Added `need_unsat_cores: bool = True` parameter to `CVC5SolverAdapter.__init__()`
- Added `self._need_unsat_cores` instance variable to track mode
- Created `_configure_diagnostic_mode()` method that sets `produce-unsat-cores=true`
- Created `_configure_performance_mode()` method that sets:
  - `decision=stoponly` - CVC5 optimization from Task 79 research
  - `bv-eager-eval=true` - CVC5 optimization from Task 79 research
- Updated `unsat_core()` to return empty list when `_need_unsat_cores=False`
- Updated `reset()` to preserve mode configuration after solver reset

### Phase 2: Registry Integration

**File**: `code/src/model_checker/solver/registry.py`

- Added `_detect_unsat_core_requirement()` function to auto-detect if cores are needed
- Detection logic: `settings.get('print_constraints', False) or settings.get('print_z3', False)`
- Updated `create_solver()` to pass `need_unsat_cores` parameter to CVC5 adapter
- Z3 adapter unchanged (always tracks cores, negligible overhead)

### Phase 3: Structure.py Safety Updates

**File**: `code/src/model_checker/models/structure.py`

- Updated `_get_relevant_constraints()` to handle empty unsat cores:
  - When `len(self.unsat_core) == 0`, prints "UNSATISFIABLE (core not available - performance mode)"
  - Falls back to returning all constraints when core is unavailable
- Updated `print_model()` to handle empty cores with informative message

## Test Results

### Unit Tests
- All 299 existing unit tests pass (no regressions)

### New Integration Tests
All tests pass:
1. Diagnostic mode initialization (`need_unsat_cores=True`)
2. Performance mode initialization (`need_unsat_cores=False`)
3. `unsat_core()` returns empty list in performance mode
4. `reset()` preserves mode configuration
5. Default mode is diagnostic (backwards compatible)
6. Registry creates CVC5 with performance mode when no print settings
7. Registry creates CVC5 with diagnostic mode when `print_constraints=True`
8. Registry creates CVC5 with diagnostic mode when `print_z3=True`

## Performance Impact

Based on Task 79 research, the performance mode combines:
- Disabling unsat core tracking (4-5x overhead reduction)
- `decision=stoponly` optimization
- `bv-eager-eval=true` optimization

Expected improvement: CVC5 performance gap reduced from 8.9x to approximately 1.65x slower than Z3 on UNSAT examples.

## Backwards Compatibility

- Default behavior unchanged: `CVC5SolverAdapter()` creates diagnostic mode solver
- Existing code using CVC5 without settings will now use performance mode
- Code with `print_constraints=True` or `print_z3=True` automatically gets diagnostic mode

## Files Modified

| File | Changes |
|------|---------|
| `code/src/model_checker/solver/cvc5_adapter.py` | Mode configuration, `need_unsat_cores` parameter |
| `code/src/model_checker/solver/registry.py` | Auto-detection, factory updates |
| `code/src/model_checker/models/structure.py` | Empty core handling |

## Rollback Plan

If issues arise:
1. Revert `CVC5SolverAdapter` to always enable unsat cores
2. Remove `_detect_unsat_core_requirement()` from registry
3. Remove empty core handling from structure.py

All changes are isolated to three files with clear boundaries.
