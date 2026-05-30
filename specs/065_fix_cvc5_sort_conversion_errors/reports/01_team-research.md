# Research Report: Task #65

**Task**: Fix cvc5 Sort conversion errors in semantic modules
**Date**: 2026-03-30
**Mode**: Team Research (2 teammates)

## Summary

All 138 comparison examples fail with "Cannot convert Sort to cvc5.cvc5_python_base.Sort" due to a **stale AtomSort binding** in `syntactic/__init__.py`. The z3_shim abstraction layer works correctly for all Sort/Function calls -- the problem is that `syntactic.AtomSort` is eagerly bound as a z3 `SortRef` at import time and never updates when the backend switches to cvc5.

The fix is minimal (~5 lines): add `__getattr__` to `syntactic/__init__.py` so `syntactic.AtomSort` dynamically resolves via `get_atom_sort()`, plus defensive `get_atom_sort()` calls at usage sites.

## Key Findings

### Root Cause: Stale AtomSort Module Binding (Both Teammates - HIGH confidence)

**File**: `src/model_checker/syntactic/__init__.py` line 9

```python
from .atoms import AtomSort, AtomVal  # Binds z3 Sort to module dict at import time
```

When this runs during first import:
1. `atoms.__getattr__('AtomSort')` calls `get_atom_sort()` which calls `DeclareSort("AtomSort")` using the active backend (z3)
2. The z3 `SortRef` result is stored in `syntactic.__dict__['AtomSort']`
3. After `reset_atom_sort()` clears `atoms._atom_sort`, `syntactic.AtomSort` still holds the stale z3 object
4. When `logos/semantic.py` or `bimodal/semantic.py` calls `z3.Function("verify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())` with cvc5 active, the mixed sort types cause the error

**Verified experimentally**:
```python
# After cvc5 switch + reset_atom_sort():
type(syntactic.AtomSort)     # -> z3.z3.SortRef    (STALE!)
type(get_atom_sort())        # -> cvc5 SortRef     (CORRECT)
```

### The z3_shim Works Correctly (Both Teammates)

`z3_shim.BitVecSort(N)`, `z3_shim.IntSort()`, `z3_shim.BoolSort()`, `z3_shim.Function()` all correctly route to the active backend. No shim changes needed.

`solver/expressions.py` already exports all needed abstractions -- no new functions needed.

### Crash Sites (Teammate A)

| File | Line | Usage | Issue |
|------|------|-------|-------|
| `logos/semantic.py` | 141-146 | `z3.Function("verify", ..., syntactic.AtomSort, ...)` | Stale z3 sort |
| `logos/semantic.py` | 147-152 | `z3.Function("falsify", ..., syntactic.AtomSort, ...)` | Stale z3 sort |
| `bimodal/semantic.py` | 175-179 | `z3.Function("truth_condition", ..., syntactic.AtomSort, ...)` | Stale z3 sort |
| `bimodal/semantic.py` | 304 | `z3.Const('atom_interpretation', syntactic.AtomSort)` | Stale z3 sort |

All other Sort/Function usages in these files (BitVecSort, IntSort, BoolSort, etc.) work correctly via z3_shim.

### Secondary Issues (Both Teammates)

`bimodal/semantic.py` contains z3-specific runtime type checks that will fail with cvc5 after the primary fix:

| Lines | Code | Risk |
|-------|------|------|
| 1172 | `isinstance(time, z3.ArithRef) and time.sort() == z3.IntSort()` | Medium |
| 1184 | `isinstance(world_array, z3.ArrayRef)` | Medium |
| 1188 | `isinstance(world_array, z3.QuantifierRef)` | Medium |
| 867+ | `except z3.Z3Exception` (multiple sites) | Low (shim routes correctly) |

These are secondary to the AtomSort fix and can be addressed independently.

### witness_registry.py and witness_constraints.py (Both Teammates)

These files use `z3.IntSort()`, `z3.Function()`, etc. via `z3_shim` -- they work correctly. **No changes needed** for the core 138-example failure. Only direct z3 import cleanup is a nice-to-have.

## Synthesis

### Conflicts Resolved

No conflicts -- both teammates independently identified the same root cause and recommended the same fix approach.

### Gaps Identified

1. **Sort equality semantics**: Teammate B raised that `time.sort() == z3.IntSort()` may behave differently between z3 and cvc5 -- needs testing
2. **Test files**: 11 test files still use `import z3` directly -- secondary concern, not blocking the 138 comparison failures
3. **`from syntactic import AtomSort`**: Adding `__getattr__` fixes `syntactic.AtomSort` but code doing `from model_checker.syntactic import AtomSort` would still cache the z3 sort at import time

### Recommendations

**Primary Fix (Critical, ~5 lines)**:

1. Add `__getattr__` to `syntactic/__init__.py`:
```python
# Remove: from .atoms import AtomSort
# Keep: from .atoms import AtomVal
from .atoms import AtomVal, get_atom_sort

def __getattr__(name):
    if name == 'AtomSort':
        return get_atom_sort()
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
```

2. Defensively replace `syntactic.AtomSort` with `get_atom_sort()` at the 4 usage sites in `logos/semantic.py` (lines 144, 150) and `bimodal/semantic.py` (lines 178, 304).

**Secondary Fix (Medium priority)**:

3. Replace z3-specific isinstance checks in `bimodal/semantic.py` with duck typing or `solver.expressions` helpers (e.g., `is_int()`).

**Migration Order**:
1. Fix `syntactic/__init__.py` (root cause)
2. Update `logos/semantic.py` usage sites
3. Update `bimodal/semantic.py` usage sites
4. Run comparison tests -- all 138 should pass
5. Address isinstance/exception checks (secondary)

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary approach: file analysis, migration strategy | completed | high |
| B | Alternative patterns, prior art, risk analysis | completed | high |

## References

- `code/src/model_checker/syntactic/__init__.py` - Root cause location
- `code/src/model_checker/syntactic/atoms.py` - `get_atom_sort()` / `reset_atom_sort()`
- `code/src/model_checker/solver/expressions.py` - Abstraction layer (already complete)
- `code/src/model_checker/theory_lib/logos/semantic.py` - Crash site (verify/falsify)
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Crash site (truth_condition)
- Tasks 59-63 git history - Prior successful migrations
