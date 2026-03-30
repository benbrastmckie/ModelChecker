# Implementation Plan: Fix cvc5 Sort Conversion Errors

- **Task**: 65 - fix_cvc5_sort_conversion_errors
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: None (solver abstraction layer already complete from tasks 59-63)
- **Research Inputs**: Team research (2 reports, HIGH confidence on root cause)
- **Artifacts**: plans/01_fix-atomsort-binding.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

The root cause of all 138 comparison example failures is that `syntactic/__init__.py` exports `AtomSort` as a module-level attribute that gets eagerly bound at import time. When the backend switches from z3 to cvc5, `syntactic.AtomSort` remains the stale z3 `SortRef` object, causing "Cannot convert Sort to cvc5.cvc5_python_base.Sort" errors at the 4 crash sites where semantic modules use `syntactic.AtomSort` directly.

The fix is two-fold:
1. Add `__getattr__` to `syntactic/__init__.py` so `syntactic.AtomSort` dynamically calls `get_atom_sort()`
2. Defensively update the 4 usage sites to call `get_atom_sort()` directly instead of relying on module attribute access

### Research Integration

Team research identified:
- **Primary Issue** (HIGH confidence): Eager binding of `AtomSort` in `syntactic/__init__.py`
- **Crash Sites**: 4 locations using `syntactic.AtomSort` directly
- **Secondary Issues** (MEDIUM priority): z3-specific isinstance checks and Z3Exception handling in bimodal/semantic.py

## Goals & Non-Goals

**Goals**:
- Fix the root cause by making `syntactic.AtomSort` dynamically resolve
- Update all 4 crash sites to use `get_atom_sort()` directly
- All 138 comparison examples pass with cvc5 backend
- Maintain backwards compatibility for existing code using `syntactic.AtomSort`

**Non-Goals**:
- Refactor isinstance checks (secondary issue, can be separate task)
- Refactor Z3Exception handling (secondary issue, can be separate task)
- Performance optimization of sort lookup (negligible overhead)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Breaking existing imports | High | Low | Add `__getattr__` for backwards compatibility |
| Missing crash sites | Medium | Low | Team research identified all 4; grep verification |
| Test regression | High | Low | Run full test suite before/after |
| Import cycle | Medium | Low | `get_atom_sort()` already exists in atoms.py |

## Implementation Phases

### Phase 1: Add Dynamic Resolution to syntactic/__init__.py [NOT STARTED]

**Goal**: Make `syntactic.AtomSort` dynamically call `get_atom_sort()` instead of binding at import time

**Tasks**:
- [ ] Read current `syntactic/__init__.py` implementation
- [ ] Remove `AtomSort` from direct import statement (line 9)
- [ ] Add `__getattr__` function to handle `AtomSort` attribute access dynamically
- [ ] Keep `AtomSort` in `__all__` for documentation/IDE support
- [ ] Add module-level docstring note about dynamic resolution

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/syntactic/__init__.py` - Add `__getattr__` for dynamic AtomSort resolution

**Verification**:
- `python -c "from model_checker import syntactic; print(type(syntactic.AtomSort))"` should work
- Sort should be fresh each time after `reset_atom_sort()`

---

### Phase 2: Update logos/semantic.py Usage Sites [NOT STARTED]

**Goal**: Replace `syntactic.AtomSort` with `get_atom_sort()` in logos semantic module

**Tasks**:
- [ ] Import `get_atom_sort` from `syntactic.atoms` at top of file
- [ ] Replace line 144: `syntactic.AtomSort` -> `get_atom_sort()`
- [ ] Replace line 150: `syntactic.AtomSort` -> `get_atom_sort()`
- [ ] Verify no other usages of `syntactic.AtomSort` in file

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/semantic.py` - Lines 144, 150

**Verification**:
- File parses without errors: `python -c "from model_checker.theory_lib.logos.semantic import LogosSemantics"`
- No `syntactic.AtomSort` references remain (grep check)

---

### Phase 3: Update bimodal/semantic.py Usage Sites [NOT STARTED]

**Goal**: Replace `syntactic.AtomSort` with `get_atom_sort()` in bimodal semantic module

**Tasks**:
- [ ] Import `get_atom_sort` from `syntactic.atoms` at top of file
- [ ] Replace line 178: `syntactic.AtomSort` -> `get_atom_sort()`
- [ ] Replace line 304: `syntactic.AtomSort` -> `get_atom_sort()`
- [ ] Verify no other usages of `syntactic.AtomSort` in file

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Lines 178, 304

**Verification**:
- File parses without errors: `python -c "from model_checker.theory_lib.bimodal.semantic import BimodalSemantics"`
- No `syntactic.AtomSort` references remain (grep check)

---

### Phase 4: Run Verification Tests [NOT STARTED]

**Goal**: Confirm fix resolves all 138 comparison example failures

**Tasks**:
- [ ] Run comparison tests with z3 backend (should pass - baseline)
- [ ] Run comparison tests with cvc5 backend (should now pass)
- [ ] Run full test suite to check for regressions
- [ ] Update test files if needed (integration tests in logos/tests and bimodal/tests also use syntactic.AtomSort)

**Timing**: 60 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/tests/integration/test_injection.py` - Line 110 (if needed)
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_injection.py` - Line 56 (if needed)

**Verification**:
- `pytest code/tests/integration/solver/ -v` - All comparison tests pass
- `pytest code/tests/ -v` - No regressions in full suite

## Testing & Validation

- [ ] Import verification: `python -c "from model_checker import syntactic; print(syntactic.AtomSort)"` works
- [ ] Backend switching: After `reset_atom_sort()`, `syntactic.AtomSort` returns fresh sort
- [ ] z3 backend: All 138 comparison examples pass (baseline)
- [ ] cvc5 backend: All 138 comparison examples pass (target)
- [ ] No regressions: Full test suite passes

## Artifacts & Outputs

- `plans/01_fix-atomsort-binding.md` - This plan file
- `summaries/01_fix-atomsort-binding-summary.md` - Execution summary (after implementation)

## Rollback/Contingency

If the fix introduces regressions:
1. Revert changes to `syntactic/__init__.py`
2. Revert changes to `logos/semantic.py` and `bimodal/semantic.py`
3. The solver abstraction layer itself is sound; the issue is only in Sort binding
4. Alternative: Cache AtomSort per-backend in a dict keyed by backend name
