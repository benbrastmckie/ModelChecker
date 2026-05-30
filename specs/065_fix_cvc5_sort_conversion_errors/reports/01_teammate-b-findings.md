# Task 65: Teammate B Research Findings
## Alternative Patterns, Prior Art, and Risks

**Date**: 2026-03-30
**Focus**: Prior migration patterns, cvc5 adapter analysis, root cause diagnosis, risk analysis

---

## Key Findings

### 1. Root Cause Identified (Critical)

The error "Cannot convert Sort to cvc5.cvc5_python_base.Sort" is caused by a
**stale AtomSort binding in `model_checker.syntactic`'s module-level namespace**.

Execution trace:
1. `syntactic/__init__.py` contains `from .atoms import AtomSort`
2. This eagerly binds `AtomSort` as a z3 `SortRef` object into `syntactic.__dict__['AtomSort']`
   at import time (Python default backend)
3. When the backend switches to cvc5, `reset_atom_sort()` correctly resets `atoms._atom_sort = None`
   so `get_atom_sort()` regenerates using cvc5
4. BUT `syntactic.AtomSort` is still the old z3 `SortRef` object -- it was bound by
   value, not by reference
5. When `logos/semantic.py` and `bimodal/semantic.py` call `z3.Function('...', syntactic.AtomSort, ...)`
   the cvc5 backend rejects the z3 `SortRef` with "Cannot convert Sort to cvc5.cvc5_python_base.Sort"

This is **not** a z3_shim problem -- the shim works correctly. The issue is that
`syntactic.AtomSort` is a cached z3 object, not a dynamic accessor.

Verified reproduction path:
```python
# After backend switch + reset_atom_sort():
from model_checker import syntactic
type(syntactic.AtomSort)       # -> z3.z3.SortRef   (STALE!)
from model_checker.syntactic.atoms import get_atom_sort
type(get_atom_sort())          # -> cvc5.pythonic.cvc5_pythonic.SortRef  (CORRECT)
```

### 2. The Migration Pattern (Tasks 59-63) Did Not Address AtomSort

Tasks 59-63 successfully migrated `import z3` to `from model_checker import z3_shim as z3`
across 35 production files. This migration handled:
- `is_true`, `is_false` -> `from model_checker.solver import is_true, is_false`
- All expression-building calls via z3_shim (which correctly routes to active backend)

But it did NOT address:
- `syntactic.AtomSort` -- still binds eagerly at import time with z3 backend
- `isinstance(x, z3.ArithRef)` -- still uses z3's concrete types for runtime checks
- `isinstance(x, z3.ArrayRef)` -- same issue
- `isinstance(x, z3.QuantifierRef)` -- same issue
- `z3.Z3Exception` in except clauses -- z3-specific exception

The migration left these as z3-specific because they need deeper fixes (type checking
and exception handling are more than just name substitution).

### 3. The z3_shim Works Correctly for All Non-AtomSort Cases

Verified: when cvc5 is active, `z3_shim.BitVecSort(N)`, `z3_shim.IntSort()`,
`z3_shim.BoolSort()`, `z3_shim.Function(...)`, `z3_shim.ArraySort(...)` all return
correct cvc5 types. The `Function` call in bimodal/semantic.py and logos/semantic.py
would work correctly if `syntactic.AtomSort` were also a cvc5 sort.

### 4. solver/expressions.py Already Has All Required Abstractions

The `solver/expressions.py` module already exports:
- `BitVecSort`, `IntSort`, `BoolSort`, `ArraySort` -- for sort construction
- `Function`, `Const`, `DeclareSort` -- for function/constant creation
- `ForAll`, `Exists`, `And`, `Or`, `Not`, `Implies` -- for formula construction
- `IntVal`, `BitVecVal` -- for constants

No new functions need to be added to expressions.py for this migration.

### 5. Test Files Use Direct `import z3`

Eleven test files still use `import z3` directly:
- `bimodal/tests/integration/test_injection.py` -- uses `z3.Solver()`, `z3.sat`
- `bimodal/tests/unit/test_witness_*.py` -- uses `z3.FuncDeclRef`, `z3.BoolRef`
- `logos/tests/unit/test_semantic_methods.py` -- uses `isinstance(x, z3.FuncDeclRef)`
- `logos/tests/integration/test_injection.py` -- uses `z3.Solver()`, `z3.Const()`

These test failures are a **secondary issue** -- they are test infrastructure bugs,
not production code bugs. The test_injection.py files use `z3.Solver()` directly,
which will always be z3-specific (these tests were written to test z3 integration
specifically).

### 6. Comparison.py Already Shows the Correct Reset Pattern

`logos/comparison.py`'s `switch_solver()` function calls `reset_atom_sort()` after
switching backends. This is the right approach but it only resets the atoms module
cache -- it does not update `syntactic.__dict__['AtomSort']`.

The `test_solver_comparison.py` reset fixture does NOT call `reset_atom_sort()`, which
is why running the comparison test with `MODEL_CHECKER_SOLVER=cvc5` set externally
still fails.

---

## Risk Analysis

### Risk 1: AtomSort Binding in syntactic.__dict__ (HIGH)

The key risk is that fixing AtomSort in the semantic modules (using `get_atom_sort()`
instead of `syntactic.AtomSort`) will work -- but only if these semantic classes are
instantiated AFTER the backend switch and AFTER `reset_atom_sort()` is called.

If any code holds a reference to a `LogosSemantics` or `BimodalSemantics` instance
created under z3 and tries to use it under cvc5, the stored `self.verify` etc.
will be z3 FuncDeclRef objects that cvc5 cannot use.

**Mitigation**: Semantic instances should always be created fresh when the backend
changes. The comparison.py and test_solver_comparison.py fixtures already do this.

### Risk 2: isinstance() Checks on z3 Types in bimodal/semantic.py (MEDIUM)

`bimodal/semantic.py` contains:
```python
isinstance(time, z3.ArithRef)      # line 1172
isinstance(world_array, z3.ArrayRef)   # line 1184, 1246
isinstance(world_array, z3.QuantifierRef)  # line 1188
```

With the z3_shim approach, `z3.ArithRef` is `cvc5.pythonic.ArithRef` when cvc5 is active,
so `isinstance(x, z3.ArithRef)` would work correctly IF `x` is also from cvc5.

However, if `x` was created under z3 and checked under cvc5, or vice versa, this fails.
The current migration makes the isinstance checks dynamic (via z3_shim), which is correct.

**Mitigation**: Keep using `z3.ArithRef` via z3_shim (not direct import z3) -- this
already works correctly. No additional changes needed here beyond the existing shim.

### Risk 3: z3.Z3Exception in Exception Handlers (LOW)

`bimodal/semantic.py` has `except (TypeError, z3.Z3Exception)` at line 1243.
With z3_shim, `z3.Z3Exception` resolves to `cvc5.pythonic.CVC5Exception` when cvc5 is active.
This is functionally correct via the shim.

**Mitigation**: Already handled by z3_shim (no additional changes needed).

### Risk 4: sort() Comparison at Line 1172 (MEDIUM)

```python
time.sort() == z3.IntSort()
```

This creates a new `IntSort()` on each call for comparison. With z3_shim, both sides
are from the same backend, so equality should hold. However, cvc5's `IntSort()` creates
a new `ArithSortRef` object each time -- equality semantics might differ from z3.

**Mitigation**: Use `str(time.sort()) == "Int"` or `hasattr(time, 'sort') and is_int(time)`
from `solver.expressions`. The `is_int()` function in expressions.py is already available
and backend-agnostic.

### Risk 5: Breaking z3 Backend (LOW)

The migration from `syntactic.AtomSort` to `get_atom_sort()` in semantic constructors
is safe for z3 because `get_atom_sort()` returns the same z3 SortRef when z3 is active.
No z3 functionality breaks.

### Risk 6: Test Files as Separate Concern (MEDIUM)

The test files using `import z3` directly will continue failing under `MODEL_CHECKER_SOLVER=cvc5`.
These tests were designed for the z3 backend. The task description says 138 comparison
examples fail -- these are the `test_solver_comparison.py` tests, which go through the
full pipeline. The unit tests (test_semantic_methods.py, test_witness_*.py) failing
with cvc5 is acceptable if they test z3-specific behavior.

The 138 comparison failures are likely in the `test_solver_comparison.py` running
without the cvc5 env var (the test itself switches backends, but the module-level
AtomSort was created under z3 at import time).

---

## Alternative Approaches

### Approach A: Fix AtomSort Binding in syntactic/__init__.py (RECOMMENDED)

Change `syntactic/__init__.py` to use `__getattr__` for `AtomSort` instead of
a direct import:

```python
# Remove: from .atoms import AtomSort
# Add:
def __getattr__(name):
    if name == 'AtomSort':
        from .atoms import get_atom_sort
        return get_atom_sort()
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
```

This makes `syntactic.AtomSort` always return the current backend's sort.
**Pro**: Fixes the root cause. All code accessing `syntactic.AtomSort` works correctly.
**Con**: Module-level `__getattr__` has slightly more overhead per access.
**Risk**: Code that does `from model_checker.syntactic import AtomSort` would get the
sort at import time and cache it -- same problem as before. Must use `syntactic.AtomSort`.

### Approach B: Use get_atom_sort() in Semantic Constructors (TARGETED FIX)

In `logos/semantic.py` and `bimodal/semantic.py`, replace `syntactic.AtomSort` with
a call to `get_atom_sort()` at each site:

```python
from model_checker.syntactic.atoms import get_atom_sort
# ...
self.verify = z3.Function(
    "Verify",
    z3.BitVecSort(self.N),
    get_atom_sort(),      # instead of syntactic.AtomSort
    z3.BoolSort()
)
```

**Pro**: Minimal change, targets exact failure sites.
**Con**: Does not fix the underlying binding issue -- other code accessing
`syntactic.AtomSort` directly would still break.

### Approach C: Enhance reset_atom_sort() to Update syntactic Module

Modify `reset_atom_sort()` to also update `model_checker.syntactic.__dict__['AtomSort']`:

```python
def reset_atom_sort() -> None:
    global _atom_sort
    _atom_sort = None
    # Also invalidate the cached binding in the syntactic package
    import model_checker.syntactic as syn_pkg
    if hasattr(syn_pkg, '__dict__') and 'AtomSort' in syn_pkg.__dict__:
        del syn_pkg.__dict__['AtomSort']
```

**Pro**: Fixes the root cause from the reset side.
**Con**: Deleting from module __dict__ triggers __getattr__ on next access, but
atoms.py's __getattr__ only covers `model_checker.syntactic.atoms`, not
`model_checker.syntactic`. syntactic/__init__.py has no __getattr__.

This approach requires BOTH:
1. Delete from syntactic.__dict__
2. Add __getattr__ to syntactic/__init__.py

### Approach D: Lazy Initialization in Semantic Classes (DEFERRED CREATION)

Instead of creating Functions at `__init__` time, use Python properties:

```python
@property
def verify(self):
    if self._verify is None:
        self._verify = z3.Function('Verify', z3.BitVecSort(self.N),
                                    get_atom_sort(), z3.BoolSort())
    return self._verify
```

**Pro**: Completely defers sort resolution to first use.
**Con**: Large refactor. Functions are currently set as instance attributes
and cached -- converting all of them to properties is extensive work.

### Approach E: Enhance z3_shim to Handle AtomSort Transparently

The z3_shim could be enhanced to detect when a z3-backend Sort is passed to a
cvc5 backend Function, and convert it. This would be a "compatibility shim" approach.

**Pro**: No changes to semantic files needed.
**Con**: Very complex. Sort conversion between backends is semantically ambiguous.
Not recommended.

---

## Recommended Migration Strategy

**The simplest correct fix for the 138 failing comparison tests** is a combination
of Approaches A and B:

1. **Fix syntactic/__init__.py** with `__getattr__` for `AtomSort` (Approach A) --
   this is the principled root cause fix.

2. **In semantic constructors**, also switch from `syntactic.AtomSort` to `get_atom_sort()`
   (Approach B) -- defensive fix that works regardless of module import order.

3. **Test files** (`import z3`) can be left as-is if they are backend-specific tests.
   OR migrate them to use `from model_checker import z3_shim as z3` for backend agnosticism.

**Files requiring changes**:
- `code/src/model_checker/syntactic/__init__.py` -- add __getattr__ for AtomSort
- `code/src/model_checker/theory_lib/logos/semantic.py` -- 2 sites: lines 144, 150
- `code/src/model_checker/theory_lib/bimodal/semantic.py` -- 2 sites: lines 178, 304
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_registry.py` -- z3 shim
- `code/src/model_checker/theory_lib/bimodal/semantic/witness_constraints.py` -- z3 shim
- `code/src/model_checker/theory_lib/logos/tests/integration/test_solver_comparison.py` --
  add `reset_atom_sort()` to `switch_solver()` and `reset_state` fixture

**Files NOT requiring changes for core functionality** (tests can be addressed separately):
- `test_injection.py` -- uses z3.Solver() directly, z3-specific test
- `test_semantic_methods.py` -- uses isinstance(x, z3.FuncDeclRef), z3-specific
- `test_witness_*.py` -- z3-specific unit tests

---

## Confidence Level

**HIGH** for root cause analysis. The exact error, its cause, and the fix were
reproduced and verified through Python execution traces.

**HIGH** for witness_registry.py and witness_constraints.py migration -- these only
use `z3.Function(...)` and `z3.IntSort()` which are straightforwardly migrated.

**MEDIUM** for the isinstance() checks in bimodal/semantic.py -- these work correctly
via z3_shim but there may be edge cases with sort comparison (`time.sort() == z3.IntSort()`).

**HIGH** that migrating to `get_atom_sort()` in semantic constructors (instead of
`syntactic.AtomSort`) will fix the 138 failing comparison examples without breaking z3.
