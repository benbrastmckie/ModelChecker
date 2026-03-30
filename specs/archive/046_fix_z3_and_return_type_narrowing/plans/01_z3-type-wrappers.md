# Implementation Plan: Task #46

- **Task**: 46 - Fix z3.And() return type narrowing for custom Exists() calls
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_team-research.md
- **Artifacts**: plans/01_z3-type-wrappers.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

This task fixes static type errors caused by z3.And() and z3.Or() returning `Union[Unknown, Probe, BoolRef]` when the codebase expects `BoolRef`. The fix adds typed wrapper functions (`z3_and`, `z3_or`) to `z3_helpers.py` that use `cast()` to guarantee `BoolRef` returns, then migrates all call sites to use these wrappers. The Probe branch is structurally unreachable when inputs are BoolRef, making this purely a type annotation fix with zero runtime behavior change.

### Research Integration

Key findings from team research report (01_team-research.md):
- Root cause: z3 lacks type stubs, Pyright infers `Union[Unknown, Probe, BoolRef]` from source
- 4 direct Pyright errors: 2 in z3_helpers.py (lines 45, 81) + 2 in first_order/operators.py (384, 572)
- ~50+ identical patterns across operator files that would benefit from wrapper migration
- Runtime behavior is always correct -- `z3.And(BoolRef, BoolRef)` always returns BoolRef
- Recommended approach: typed wrapper functions with `cast(BoolRef, And(...))`

## Goals & Non-Goals

**Goals**:
- Eliminate all Pyright errors related to z3.And/z3.Or return types
- Add `z3_and()` and `z3_or()` typed wrapper functions to z3_helpers.py
- Fix ForAll/Exists internals to use wrappers
- Migrate call sites in operator files to use wrappers
- Ensure all existing tests pass

**Non-Goals**:
- Creating custom z3 `.pyi` stubs (disproportionately complex to maintain)
- Adding runtime assertions (Probe branch is provably unreachable)
- Modifying z3 library source or vendoring
- Widening type signatures to accept Probe (mathematically incorrect)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Missed call sites | Medium | Low | Run pyright on full subtheories directory after migration |
| Import statement changes | Low | Low | Add z3_and/z3_or to existing z3_helpers imports |
| Test failures | High | Very Low | Run full test suite before finalizing |

## Implementation Phases

### Phase 1: Add Wrapper Functions [NOT STARTED]

**Goal**: Create z3_and() and z3_or() wrapper functions in z3_helpers.py

**Tasks**:
- [ ] Add `cast` import from typing module
- [ ] Create `z3_and(*args: BoolRef) -> BoolRef` function with docstring explaining Probe branch unreachability
- [ ] Create `z3_or(*args: BoolRef) -> BoolRef` function with matching docstring
- [ ] Update module docstring to mention typed wrappers

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/utils/z3_helpers.py` - Add wrapper functions

**Verification**:
- Wrapper functions are syntactically correct
- No new pyright errors introduced in z3_helpers.py (beyond existing ones)

---

### Phase 2: Fix ForAll/Exists Internals [NOT STARTED]

**Goal**: Update ForAll() and Exists() to use z3_and/z3_or internally, fixing root Pyright errors

**Tasks**:
- [ ] Replace `And(constraints)` with `z3_and(*constraints)` on line 45 of ForAll()
- [ ] Replace `Or(constraints)` with `z3_or(*constraints)` on line 81 of Exists()
- [ ] Update imports at top of file if needed (remove direct And/Or import or keep for internal use)

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/utils/z3_helpers.py` - Fix ForAll/Exists returns

**Verification**:
- Run `pyright code/src/model_checker/utils/z3_helpers.py` -- should report 0 errors
- Run z3_helpers tests if they exist

---

### Phase 3: Migrate first_order/operators.py [NOT STARTED]

**Goal**: Fix the 2 downstream errors in first_order/operators.py and migrate all z3.And/z3.Or patterns

**Tasks**:
- [ ] Add `z3_and, z3_or` to imports from z3_helpers
- [ ] Replace `z3.And(...)` with `z3_and(...)` at line 384 (Exists call in ForAllVerifier)
- [ ] Replace `z3.And(...)` with `z3_and(...)` at line 572 (Exists call in ExistsVerifier)
- [ ] Replace remaining `z3.And(constraints)` patterns (~10 occurrences)
- [ ] Replace remaining `z3.Or(constraints)` patterns (~5 occurrences)

**Timing**: 25 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/first_order/operators.py`

**Verification**:
- Run `pyright code/src/model_checker/theory_lib/logos/subtheories/first_order/operators.py`
- Should report 0 errors related to z3.And/z3.Or

---

### Phase 4: Migrate constitutive/operators.py [NOT STARTED]

**Goal**: Migrate all ~25 z3.And/z3.Or patterns in constitutive operators

**Tasks**:
- [ ] Add `z3_and, z3_or` to imports from z3_helpers
- [ ] Replace all `z3.And(...)` patterns (~20 occurrences)
- [ ] Replace all `z3.Or(...)` patterns (~5 occurrences)

**Timing**: 20 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py`

**Verification**:
- Run pyright on file, verify no z3.And/z3.Or related errors

---

### Phase 5: Migrate Remaining Operator Files [NOT STARTED]

**Goal**: Migrate z3.And/z3.Or patterns in extensional, modal, counterfactual, and relevance operators

**Tasks**:
- [ ] Migrate extensional/operators.py (~18 occurrences)
- [ ] Migrate modal/operators.py (~3 occurrences)
- [ ] Migrate counterfactual/operators.py (~5 occurrences)
- [ ] Skip relevance/operators.py if no occurrences (verify)

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py`
- `code/src/model_checker/theory_lib/logos/subtheories/relevance/operators.py` (if applicable)

**Verification**:
- Run pyright on each file
- Verify consistent import style across all files

---

### Phase 6: Verification and Testing [NOT STARTED]

**Goal**: Ensure all type errors are resolved and no regressions introduced

**Tasks**:
- [ ] Run `pyright code/src/model_checker/` on full source tree
- [ ] Verify 0 errors related to z3.And/z3.Or return types
- [ ] Run `pytest` on test suite to verify no behavioral regressions
- [ ] Document any remaining unrelated pyright errors for separate tracking

**Timing**: 15 minutes

**Files to modify**:
- None (verification only)

**Verification**:
- Pyright reports no z3.And/z3.Or related errors
- All existing tests pass
- No runtime behavior changes

## Testing & Validation

- [ ] `pyright code/src/model_checker/utils/z3_helpers.py` reports 0 errors
- [ ] `pyright code/src/model_checker/theory_lib/logos/subtheories/` reports no z3.And/z3.Or errors
- [ ] `pytest` full test suite passes
- [ ] Manual verification: grep for `z3\.And\(` and `z3\.Or\(` in operators.py files returns 0 matches

## Artifacts & Outputs

- plans/01_z3-type-wrappers.md (this file)
- summaries/01_z3-type-wrappers-summary.md (post-implementation)

## Rollback/Contingency

If wrapper migration causes issues:
1. Revert z3_helpers.py changes (git checkout)
2. Revert operator file changes (git checkout)
3. Fall back to per-site `# type: ignore` comments if wrappers prove problematic
4. Consider alternative: inline `cast(BoolRef, z3.And(...))` at each call site
