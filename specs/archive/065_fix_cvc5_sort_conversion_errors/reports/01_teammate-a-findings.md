# Task 65: Fix cvc5 Sort Conversion Errors - Research Findings

**Artifact:** 01
**Teammate:** A
**Focus:** Primary migration approach - analyzing affected files and solver abstraction layer

---

## Summary

The root cause of all 138 comparison failures is **NOT** that `z3.IntSort/BitVecSort/BoolSort/Function` need to be replaced with `solver.expressions` equivalents. The z3_shim already routes those calls to the correct backend at runtime. The real root cause is that **`syntactic.AtomSort` is permanently bound as a z3 Sort object** in the `syntactic` module's namespace at first import time, and cannot be updated when the backend switches.

---

## Key Findings

### Finding 1: The True Root Cause - `syntactic.AtomSort` Stale Cache

**File:** `/home/benjamin/Projects/Logos/ModelChecker/code/src/model_checker/syntactic/__init__.py` (line 9)

```python
from .atoms import AtomSort, AtomVal  # This permanently binds AtomSort at import time
```

When `syntactic/__init__.py` is first imported, the `from .atoms import AtomSort` statement:
1. Loads the `atoms` module
2. Calls `getattr(atoms_module, 'AtomSort')`, which triggers `atoms.__getattr__('AtomSort')`
3. `__getattr__` calls `get_atom_sort()` which calls `DeclareSort("AtomSort")` using the active backend (z3)
4. The result is **bound in `syntactic.__dict__`** as a z3 SortRef object

After this, even if `reset_atom_sort()` is called, `syntactic.AtomSort` still refers to the old z3 Sort because it's stored in the module's `__dict__`, not re-computed via `__getattr__` each time.

**Verified experimentally:**
```
After z3 setup: syntactic.AtomSort type = <class 'z3.z3.SortRef'>
After cvc5 switch + reset_atom_sort(): syntactic.AtomSort type = <class 'z3.z3.SortRef'>  # Still z3!
```

### Finding 2: Where AtomSort Causes the Error

The actual crash occurs in these usages of `syntactic.AtomSort`:

**`logos/semantic.py` lines 141-156** - `LogosSemantics.__init__`:
```python
self.verify = z3.Function(
    "verify",
    z3.BitVecSort(self.N),   # cvc5 BitVecSort - correct
    syntactic.AtomSort,       # z3 Sort - WRONG (stale)
    z3.BoolSort()             # cvc5 BoolSort - correct
)
```
When the cvc5 backend is active, `z3.BitVecSort` and `z3.BoolSort` return cvc5 Sorts, but `syntactic.AtomSort` is still a z3 Sort. cvc5's `Function()` cannot mix these.

**`bimodal/semantic.py` line 175-179** - `define_primitives`:
```python
self.truth_condition = z3.Function(
    "truth_condition",
    self.WorldStateSort,   # cvc5 BitVecSort - correct
    syntactic.AtomSort,    # z3 Sort - WRONG (stale)
    z3.BoolSort()          # cvc5 BoolSort - correct
)
```

**`bimodal/semantic.py` line 304**:
```python
sentence_letter = z3.Const('atom_interpretation', syntactic.AtomSort)  # z3 Sort - WRONG
```

### Finding 3: z3_shim Works Correctly

The `from model_checker import z3_shim as z3` import IS correctly routing to the active backend. For example, `z3.BitVecSort(N)`, `z3.BoolSort()`, `z3.Function()`, `z3.IntSort()` all work correctly with cvc5. The issue is only `syntactic.AtomSort` which bypasses z3_shim.

**Verified:** `z3.Function('test', z3.IntSort(), z3.IntSort(), z3.BoolSort())` works fine with cvc5 backend.

### Finding 4: Complete Inventory of z3 Sort Usages in Affected Files

#### `logos/semantic.py` - Sort/Function usages causing errors:
| Line | Usage | Issue |
|------|-------|-------|
| 141-146 | `z3.Function("verify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())` | `syntactic.AtomSort` is stale z3 sort |
| 147-152 | `z3.Function("falsify", z3.BitVecSort(N), syntactic.AtomSort, z3.BoolSort())` | same |
| 153-157 | `z3.Function("possible", z3.BitVecSort(N), z3.BoolSort())` | Works fine (no AtomSort) |
| 742-747 | `z3.BitVecSort(N)` + `z3.Function(...)` in `register_function` | Works via shim |
| 785-797 | `z3.BitVecSort(N)` + `z3.Function(...)` + `z3.BoolSort()` in `register_predicate` | Works via shim |

#### `bimodal/semantic.py` - Sort/Function usages causing errors:
| Line | Usage | Issue |
|------|-------|-------|
| 128 | `self.WorldStateSort = z3.BitVecSort(self.N)` | Works via shim |
| 129-130 | `self.TimeSort = z3.IntSort()` / `self.WorldIdSort = z3.IntSort()` | Works via shim |
| 150-154 | `z3.Function("Task", ..., z3.BoolSort())` | Works via shim |
| 175-179 | `z3.Function("truth_condition", ..., syntactic.AtomSort, z3.BoolSort())` | `syntactic.AtomSort` is stale |
| 304 | `z3.Const('atom_interpretation', syntactic.AtomSort)` | `syntactic.AtomSort` is stale |
| 753-754 | `z3.Function('forward_of/backward_of', self.WorldIdSort, self.WorldIdSort)` | Works via shim |

#### `bimodal/semantic/witness_registry.py` - Sort/Function usages:
| Line | Usage | Issue |
|------|-------|-------|
| 85-90 | `z3.Function(pred_name, z3.IntSort(), z3.IntSort(), z3.IntSort())` | Works via shim - no AtomSort |

#### `bimodal/semantic/witness_constraints.py`:
No Sort/Function calls that use AtomSort. Uses `z3.Int()`, `z3.ForAll()`, `z3.And()`, etc. - all route correctly via shim.

### Finding 5: Secondary Issues - z3-Specific Type Checks

`bimodal/semantic.py` also contains these z3-specific runtime type checks that will fail with cvc5:

| Lines | Code | Problem |
|-------|------|---------|
| 1172 | `isinstance(time, z3.ArithRef) and time.sort() == z3.IntSort()` | cvc5 uses different type |
| 1184 | `isinstance(world_array, z3.ArrayRef)` | cvc5 has different ArrayRef |
| 1188 | `isinstance(world_array, z3.QuantifierRef)` | cvc5 has different QuantifierRef |
| 867, 879, 1081, 1117, 1141, 1243, 1626, 1737 | `except z3.Z3Exception` | cvc5 uses different exception |

These are additional bugs but secondary to the AtomSort issue (they only matter for execution after the Function declarations succeed).

### Finding 6: Type Annotations Using z3 Types

Both `logos/semantic.py` and `bimodal/semantic.py` use z3-specific types in annotations:
- `z3.FuncDeclRef`, `z3.BoolRef`, `z3.BitVecRef`, `z3.ArithRef`, etc.

These are **not runtime errors** because they appear in function signatures and docstrings accessed only during type checking. However, they document a z3-only assumption that should be noted.

---

## Recommended Approach

### Primary Fix: Fix `syntactic.AtomSort` Caching (Highest Priority)

The root cause is in `syntactic/__init__.py`. There are two approaches:

**Option A: Add `__getattr__` to `syntactic/__init__.py` (Recommended)**

```python
# In syntactic/__init__.py, replace:
from .atoms import AtomSort, AtomVal

# With:
from .atoms import AtomVal, get_atom_sort

# Add module-level __getattr__:
def __getattr__(name):
    if name == 'AtomSort':
        return get_atom_sort()
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
```

This makes `syntactic.AtomSort` always return the current backend's sort by calling `get_atom_sort()` dynamically, while `syntactic.AtomVal` continues working as before.

**Option B: Replace all `syntactic.AtomSort` usages with `get_atom_sort()` calls**

In each usage site:
```python
# In logos/semantic.py:
from model_checker.syntactic.atoms import get_atom_sort

self.verify = z3.Function(
    "verify",
    z3.BitVecSort(self.N),
    get_atom_sort(),       # dynamic lookup
    z3.BoolSort()
)
```

Option A is preferable as it fixes the problem at the source.

### Secondary Fix: z3-Specific isinstance Checks (bimodal/semantic.py)

The `isinstance(time, z3.ArithRef)` and similar checks need to be made backend-agnostic. These should use duck typing or helper functions:

```python
# Instead of:
isinstance(time, z3.ArithRef) and time.sort() == z3.IntSort()

# Use:
hasattr(time, 'sort') and hasattr(time, 'as_long')
# OR
hasattr(time, 'sort')  # sufficient if we already checked it's not a plain int
```

For `z3.Z3Exception`, the comparison.py switch would need to either:
- Catch `Exception` broadly, OR
- Import exception type from a compat layer

### Tertiary Fix: Other z3_shim Imports

The files all use `from model_checker import z3_shim as z3` which **already works** for most things. No changes needed to Sort/Function calls that don't involve `syntactic.AtomSort`.

### Migration Order (Step-by-Step)

1. **Fix `syntactic/__init__.py`** - add `__getattr__` for `AtomSort` (Option A above)
2. **Verify `logos/semantic.py`** compiles and runs with cvc5 - the three Function declarations (verify, falsify, possible) should now work
3. **Verify `bimodal/semantic.py`** - the two usages of `syntactic.AtomSort` should now work
4. **Address isinstance checks** in `bimodal/semantic.py` (lines 1172, 1184, 1188) using duck typing
5. **Address Z3Exception catches** in `bimodal/semantic.py` - wrap with `Exception` or add compat layer
6. **Run comparison tests** to verify all 138 examples pass

---

## Evidence/Examples

### Successful Pattern: `model_checker/models/semantic.py`

This file was successfully migrated and uses explicit imports from `solver.expressions`:

```python
from model_checker.solver.expressions import (
    And, BitVecSort, BitVecVal, EmptySet, IntVal,
    IsMember, Not, SetAdd, simplify, BoolVal,
)
```

However, note that this file does NOT use `AtomSort` - it only uses value-level constructs.

### Successful Pattern: `syntactic/collection.py`

Uses `get_atom_sort()` directly (the function form), which is correct:
```python
from .atoms import get_atom_sort
```

### Successful Pattern: `utils/context.py`

The `reset_solver_context()` function correctly resets `_atom_sort = None` but does NOT fix the `syntactic.__dict__['AtomSort']` binding, which is the deeper problem.

### Experimental Verification

```
# Reproducing the error:
set_cli_backend('cvc5')
LogosSemantics({'N': 2, ...})
# --> TypeError: Cannot convert Sort to cvc5.cvc5_python_base.Sort
# at: sort = ctx.tm.mkFunctionSort([sig[i].ast for i in range(arity)], rng.ast)
```

The error occurs exactly at `z3.Function("verify", ..., syntactic.AtomSort, ...)` because `syntactic.AtomSort` is a z3 SortRef but the other arguments are cvc5 SortRefs.

---

## Confidence Level: HIGH

- Root cause identified experimentally with full stack trace
- Error reproduced in isolation and confirmed
- Fix is straightforward (1-3 line change to `syntactic/__init__.py`)
- The other issues (isinstance checks, Z3Exception) are secondary and can be addressed independently
- Total changes: ~5-10 lines across 3 files for the primary fix

---

## Files to Modify (Summary)

| File | Change | Priority |
|------|--------|----------|
| `src/model_checker/syntactic/__init__.py` | Add `__getattr__` for `AtomSort` | **Critical** |
| `src/model_checker/theory_lib/logos/semantic.py` | None needed (unless Option B chosen) | Low |
| `src/model_checker/theory_lib/bimodal/semantic.py` | Fix isinstance checks, Z3Exception catches | Medium |
| `src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` | None needed | N/A |
| `src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` | None needed | N/A |

The four files listed in the task description mostly do NOT need their `z3_shim` usage changed - the shim already works. Only `syntactic/__init__.py` needs the critical fix, plus the secondary `isinstance`/exception issues in `bimodal/semantic.py`.
