# Implementation Plan: Task #46 (v4 - Cast Approach)

- **Task**: 46 - Fix z3.And/Or return type narrowing across codebase
- **Status**: [IN PROGRESS]
- **Effort**: 90 minutes
- **Dependencies**: None
- **Research Inputs**: reports/01_teammate-a-findings.md
- **Artifacts**: plans/04_cast-z3-returns.md (this file)
- **Type**: z3

## Overview

Apply `cast(BoolRef, z3.And(...))` at all 51 call sites across 13 files where Pyright infers `Unknown | Probe | BoolRef` instead of `BoolRef`. This preserves the existing `z3.And`/`z3.Or`/`z3.Not` API usage while asserting the mathematically correct return type.

### Revision Rationale

v03 proposed typed wrapper functions (`z3_and`, `z3_or`, `z3_not`) requiring call site migration. The cast approach is more correct: it doesn't introduce new API surface, it documents the type invariant at each usage point, and `cast` has zero runtime overhead. The scope is expanded to cover ALL Probe-related errors (51 locations in 13 files), not just the 2 originally reported.

### Why `cast` Is Correct Here

`z3.And(*args)` always returns `BoolRef` when given `BoolRef` arguments. The `Probe` branch is only reached when z3 solver tactic `Probe` objects are passed, which never happens in this codebase. `cast` accurately tells the type checker what the runtime guarantees.

## Error Inventory

| File | Errors | Layer |
|------|--------|-------|
| `utils/z3_helpers.py` | 2 | Foundation |
| `utils/tests/unit/test_z3_helpers.py` | 2 | Foundation |
| `builder/z3_utils.py` | 1 | Foundation |
| `models/semantic.py` | 2 | Core |
| `iterate/constraints.py` | 2 | Core |
| `theory_lib/logos/iterate.py` | 2 | Logos infrastructure |
| `theory_lib/logos/semantic.py` | 10 | Logos semantic |
| `theory_lib/bimodal/semantic.py` | 2 | Bimodal semantic |
| `subtheories/extensional/operators.py` | 8 | Operators |
| `subtheories/constitutive/operators.py` | 14 | Operators |
| `subtheories/counterfactual/operators.py` | 1 | Operators |
| `subtheories/first_order/operators.py` | 2 | Operators |
| `subtheories/modal/operators.py` | 1 | Operators |
| **Total** | **51** | |

## Implementation Phases

### Phase 1: Foundation Layer [COMPLETED]

**Goal**: Fix `z3_helpers.py`, `z3_utils.py`, and tests

**Files**:
- `code/src/model_checker/utils/z3_helpers.py` (2 errors)
- `code/src/model_checker/utils/tests/unit/test_z3_helpers.py` (2 errors)
- `code/src/model_checker/builder/z3_utils.py` (1 error)

**Pattern**: Add `from typing import cast` import, wrap `And(constraints)` and `Or(constraints)` returns:
```python
from typing import cast
# ...
return cast(BoolRef, And(constraints))   # ForAll
return cast(BoolRef, Or(constraints))    # Exists
```

**Timing**: 15 minutes

**Verification**:
- `pyright code/src/model_checker/utils/z3_helpers.py` reports 0 Probe errors
- `pytest code/src/model_checker/utils/tests/` passes

---

### Phase 2: Core Layer [COMPLETED]

**Goal**: Fix `models/semantic.py` and `iterate/constraints.py`

**Files**:
- `code/src/model_checker/models/semantic.py` (2 errors)
- `code/src/model_checker/iterate/constraints.py` (2 errors)

**Timing**: 15 minutes

**Verification**:
- `pyright` on both files shows 0 Probe errors

---

### Phase 3: Logos Infrastructure [COMPLETED]

**Goal**: Fix `logos/iterate.py` and `logos/semantic.py`

**Files**:
- `code/src/model_checker/theory_lib/logos/iterate.py` (2 errors)
- `code/src/model_checker/theory_lib/logos/semantic.py` (10 errors)

**Timing**: 20 minutes

**Verification**:
- `pyright` on both files shows 0 Probe errors

---

### Phase 4: Operator Files [COMPLETED]

**Goal**: Fix all subtheory operator files and bimodal semantic

**Files**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (2 errors)
- `code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py` (8 errors)
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py` (14 errors)
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py` (1 error)
- `code/src/model_checker/theory_lib/logos/subtheories/first_order/operators.py` (2 errors)
- `code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py` (1 error)

**Timing**: 25 minutes

**Verification**:
- `pyright` on each file shows 0 Probe errors

---

### Phase 5: Verification [IN PROGRESS]

**Goal**: Confirm all Probe errors eliminated, no regressions

**Tasks**:
- [ ] `pyright code/src/model_checker/ 2>&1 | grep "Probe"` returns 0 lines
- [ ] `pytest code/tests/` passes (full test suite)
- [ ] Spot-check that `cast` imports are clean (no unused imports)

**Timing**: 15 minutes

## Testing and Validation

- [ ] Zero Probe-related Pyright errors across entire codebase
- [ ] All existing tests pass without modification
- [ ] No runtime behavior changes (cast is zero-overhead)

## Summary

| Phase | Files | Errors | Effort |
|-------|-------|--------|--------|
| 1 | 3 | 5 | 15 min |
| 2 | 2 | 4 | 15 min |
| 3 | 2 | 12 | 20 min |
| 4 | 6 | 28 | 25 min |
| 5 | - | - | 15 min |
| **Total** | **13** | **51** | **90 min** |

## Rollback/Contingency

If `cast` causes unexpected issues:
1. `git revert` the commit (all changes are purely type annotations)
2. No runtime risk since `cast()` is erased at runtime
