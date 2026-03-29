# Implementation Plan: Task #46 (Revised)

- **Task**: 46 - Fix z3.And() return type narrowing for custom Exists() calls
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_team-research.md
- **Artifacts**: plans/02_z3-typed-interface.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

This revision expands the scope to create a comprehensive typed z3 interface module. Rather than just wrapping `And`/`Or`, we create typed wrappers for ALL z3 functions used in the codebase, providing a uniform `z3_*` naming convention. This ensures type safety across the entire z3 interface boundary.

### Z3 Functions Currently Used (29 total)

**Logical Operations** (need typed wrappers):
- `z3.And`, `z3.Or`, `z3.Not`, `z3.Implies`, `z3.If`
- `z3.ForAll`, `z3.Exists` (z3's built-in quantifiers)

**Value Constructors** (re-export for uniformity):
- `z3.BitVec`, `z3.BitVecs`, `z3.BitVecVal`
- `z3.Bool`, `z3.BoolVal`
- `z3.Int`, `z3.IntVal`
- `z3.Real`, `z3.String`, `z3.Const`, `z3.Var`

**Sort Constructors** (re-export for uniformity):
- `z3.BitVecSort`, `z3.BoolSort`, `z3.IntSort`, `z3.ArraySort`

**Other** (re-export or keep as z3.*):
- `z3.Solver`, `z3.Context`, `z3.Function`
- `z3.Select`, `z3.Sum`, `z3.UGT`

### Revision Rationale

The original plan only addressed `z3.And`/`z3.Or` wrappers. This revision creates a complete typed interface layer for uniformity and future-proofing.

## Goals & Non-Goals

**Goals**:
- Create typed wrapper functions for ALL z3 logical operations
- Establish uniform `z3_*` naming convention
- Fix all Pyright errors related to z3 return types
- Migrate all call sites to use the new interface
- Maintain backward compatibility during transition

**Non-Goals**:
- Creating custom z3 `.pyi` stubs
- Wrapping internal z3 types (BitVecRef, BoolRef, etc.)
- Modifying z3 library source

## Implementation Phases

### Phase 1: Create z3_typed Module [NOT STARTED]

**Goal**: Create comprehensive typed wrapper module for z3 functions

**Tasks**:
- [ ] Add typed wrapper functions for logical operations:
  - `z3_and(*args: BoolRef) -> BoolRef`
  - `z3_or(*args: BoolRef) -> BoolRef`
  - `z3_not(a: BoolRef) -> BoolRef`
  - `z3_implies(a: BoolRef, b: BoolRef) -> BoolRef`
  - `z3_if(cond: BoolRef, t: ExprRef, f: ExprRef) -> ExprRef`
- [ ] Add typed re-exports for value constructors:
  - `z3_bitvec = z3.BitVec`
  - `z3_bitvecval = z3.BitVecVal`
  - `z3_bool = z3.Bool`
  - `z3_boolval = z3.BoolVal`
  - `z3_int = z3.Int`
  - `z3_intval = z3.IntVal`
- [ ] Add typed re-exports for sort constructors:
  - `z3_bitvecsort = z3.BitVecSort`
  - `z3_boolsort = z3.BoolSort`
  - `z3_intsort = z3.IntSort`
- [ ] Add `__all__` export list

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/utils/z3_helpers.py`

**Verification**:
- `pyright z3_helpers.py` reports 0 errors
- All wrapper functions have correct type signatures

---

### Phase 2: Fix ForAll/Exists Internals [NOT STARTED]

**Goal**: Update custom ForAll/Exists to use z3_and/z3_or

**Tasks**:
- [ ] Replace `And(constraints)` with `z3_and(*constraints)` in ForAll()
- [ ] Replace `Or(constraints)` with `z3_or(*constraints)` in Exists()
- [ ] Update internal z3 imports

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/utils/z3_helpers.py`

**Verification**:
- `pyright z3_helpers.py` reports 0 errors
- Existing ForAll/Exists tests pass

---

### Phase 3: Migrate first_order/operators.py [NOT STARTED]

**Goal**: Migrate all z3.* calls to z3_* wrappers

**Tasks**:
- [ ] Update imports to use z3_helpers wrappers
- [ ] Replace `z3.And(...)` with `z3_and(...)`
- [ ] Replace `z3.Or(...)` with `z3_or(...)`
- [ ] Replace `z3.Not(...)` with `z3_not(...)`
- [ ] Replace `z3.BitVec(...)` with `z3_bitvec(...)` (if applicable)
- [ ] Replace `z3.BoolVal(...)` with `z3_boolval(...)` (if applicable)

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/first_order/operators.py`

**Verification**:
- `pyright operators.py` reports 0 z3-related errors
- Tests pass

---

### Phase 4: Migrate constitutive/operators.py [NOT STARTED]

**Goal**: Migrate all z3.* calls to z3_* wrappers

**Tasks**:
- [ ] Update imports
- [ ] Replace all z3.And/Or/Not patterns
- [ ] Replace value constructors

**Timing**: 25 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py`

**Verification**:
- Pyright clean, tests pass

---

### Phase 5: Migrate Remaining Subtheory Operators [NOT STARTED]

**Goal**: Complete migration across all subtheories

**Tasks**:
- [ ] Migrate extensional/operators.py
- [ ] Migrate modal/operators.py
- [ ] Migrate counterfactual/operators.py (if exists)
- [ ] Migrate relevance/operators.py (if exists)

**Timing**: 40 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/*/operators.py`

**Verification**:
- All operator files pass pyright
- All tests pass

---

### Phase 6: Migrate Core Model Files [NOT STARTED]

**Goal**: Migrate z3.* calls in non-operator files

**Tasks**:
- [ ] Migrate `models/semantic.py` (z3.BoolVal)
- [ ] Migrate `models/structure.py` (z3.Solver)
- [ ] Migrate `iterate/models.py` (z3.Not, z3.Solver)
- [ ] Migrate `iterate/constraints.py` (z3.And, z3.Or, z3.Not, z3.BoolVal)
- [ ] Migrate bimodal modules (z3.ForAll, z3.And, z3.Implies, etc.)

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/models/semantic.py`
- `code/src/model_checker/models/structure.py`
- `code/src/model_checker/iterate/*.py`
- `code/src/model_checker/theory_lib/bimodal/**/*.py`

**Verification**:
- Pyright clean on all modified files
- Full test suite passes

---

### Phase 7: Verification and Cleanup [NOT STARTED]

**Goal**: Final verification and cleanup

**Tasks**:
- [ ] Run `pyright code/src/model_checker/` on full source tree
- [ ] Run full pytest suite
- [ ] Verify no remaining `z3.And(`, `z3.Or(`, `z3.Not(` patterns in operators
- [ ] Update any documentation referencing z3.* patterns
- [ ] Optionally: add deprecation comments to discourage direct z3.* usage

**Timing**: 20 minutes

**Verification**:
- Zero z3-related Pyright errors
- All tests pass
- `grep -r "z3\.And\|z3\.Or\|z3\.Not" --include="*.py" operators.py` returns 0 matches

## Summary of Changes

| File/Module | z3.And | z3.Or | z3.Not | z3.BoolVal | Other |
|-------------|--------|-------|--------|------------|-------|
| z3_helpers.py | wrapper | wrapper | wrapper | re-export | many |
| first_order/operators.py | ~15 | ~8 | ~3 | ~2 | BitVec |
| constitutive/operators.py | ~25 | ~8 | ~5 | ~3 | BitVec |
| extensional/operators.py | ~18 | ~5 | ~4 | ~2 | BitVec |
| modal/operators.py | ~3 | ~2 | ~1 | ~1 | - |
| iterate/*.py | ~5 | ~3 | ~4 | ~3 | Solver |
| bimodal/**/*.py | ~10 | ~3 | ~2 | ~2 | ForAll, Implies |

## Testing & Validation

- [ ] `pyright code/src/model_checker/` reports 0 z3-related errors
- [ ] `pytest` full test suite passes
- [ ] No direct `z3.And(`, `z3.Or(`, `z3.Not(` calls remain in operators

## Rollback/Contingency

If migration causes issues:
1. Revert to v01 plan (just And/Or wrappers)
2. Keep direct z3.* calls for non-logical operations
3. Fall back to per-file `# pyright: reportArgumentType=false` if needed
