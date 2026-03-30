# Implementation Plan: Task #46 (v3 - Narrowed Scope)

- **Task**: 46 - Fix z3.And() return type narrowing for custom Exists() calls
- **Status**: [NOT STARTED]
- **Effort**: 45 minutes
- **Dependencies**: None
- **Research Inputs**: reports/01_team-research.md
- **Artifacts**: plans/03_boolean-operators-only.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md
- **Type**: z3
- **Lean Intent**: false

## Overview

This revision narrows scope to ONLY the boolean operators (`And`, `Or`, `Not`). We create typed wrappers for these three functions and fix the ForAll/Exists quantifier implementations.

### Revision Rationale

v02 expanded scope to all 29 z3 functions (3+ hours). This revision returns to the minimal fix: typed wrappers for `And`, `Or`, `Not` only, fixing the immediate Pyright errors in z3_helpers.py.

## Goals & Non-Goals

**Goals**:
- Create typed wrappers: `z3_and`, `z3_or`, `z3_not`
- Fix ForAll/Exists to use typed wrappers
- Eliminate Pyright errors in z3_helpers.py

**Non-Goals**:
- Wrapping ALL z3 functions
- Migrating call sites in operators.py files
- Creating a comprehensive z3_* interface layer

## Implementation Phases

### Phase 1: Create Boolean Operator Wrappers [NOT STARTED]

**Goal**: Add typed wrapper functions for And, Or, Not

**Tasks**:
- [ ] Add `z3_and(*args: BoolRef) -> BoolRef` wrapper
- [ ] Add `z3_or(*args: BoolRef) -> BoolRef` wrapper
- [ ] Add `z3_not(a: BoolRef) -> BoolRef` wrapper

**Implementation**:
```python
def z3_and(*args: BoolRef) -> BoolRef:
    """Typed wrapper for z3.And that guarantees BoolRef return."""
    result = And(*args)
    assert isinstance(result, BoolRef)
    return result

def z3_or(*args: BoolRef) -> BoolRef:
    """Typed wrapper for z3.Or that guarantees BoolRef return."""
    result = Or(*args)
    assert isinstance(result, BoolRef)
    return result

def z3_not(a: BoolRef) -> BoolRef:
    """Typed wrapper for z3.Not that guarantees BoolRef return."""
    from z3 import Not
    result = Not(a)
    assert isinstance(result, BoolRef)
    return result
```

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/utils/z3_helpers.py`

**Verification**:
- Functions exist with correct type signatures
- Pyright reports no errors on wrapper functions

---

### Phase 2: Fix ForAll/Exists Implementations [NOT STARTED]

**Goal**: Update ForAll() and Exists() to use typed wrappers

**Tasks**:
- [ ] Replace `And(constraints)` with `z3_and(*constraints)` in ForAll()
- [ ] Replace `Or(constraints)` with `z3_or(*constraints)` in Exists()

**Current code** (lines 45, 81):
```python
return And(constraints)  # Returns Union type
return Or(constraints)   # Returns Union type
```

**Fixed code**:
```python
return z3_and(*constraints)  # Returns BoolRef
return z3_or(*constraints)   # Returns BoolRef
```

**Timing**: 10 minutes

**Files to modify**:
- `code/src/model_checker/utils/z3_helpers.py`

**Verification**:
- `pyright code/src/model_checker/utils/z3_helpers.py` reports 0 errors
- Existing tests pass

---

### Phase 3: Verification [NOT STARTED]

**Goal**: Confirm fix is complete

**Tasks**:
- [ ] Run pyright on z3_helpers.py
- [ ] Run tests: `pytest code/tests/ -k "z3 or helper"`
- [ ] Verify ForAll/Exists return types are BoolRef

**Timing**: 10 minutes

**Verification**:
- Zero Pyright errors on z3_helpers.py
- All tests pass

## Testing & Validation

- [ ] `pyright code/src/model_checker/utils/z3_helpers.py` reports 0 errors
- [ ] ForAll/Exists tests pass (if any exist)
- [ ] No regression in model checker functionality

## Summary

| Phase | Effort | Deliverable |
|-------|--------|-------------|
| 1 | 15 min | Boolean wrappers |
| 2 | 10 min | Fixed ForAll/Exists |
| 3 | 10 min | Verification |
| **Total** | 35 min | |

## Rollback/Contingency

If wrappers cause issues:
1. Revert to direct z3.And/Or calls
2. Add `# pyright: ignore` comments as last resort
