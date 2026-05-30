# Research Report: cvc5 "Z3 expression expected" Compatibility Errors

## Executive Summary

The "Z3 expression expected" error in cvc5 mode is caused by a **static binding issue** in `semantic.py`. The module imports `simplify` from `z3_shim` at module load time, before the backend is switched to cvc5. This creates a static binding to z3's `simplify` function that persists even after the backend is changed, causing z3's `simplify` to receive cvc5 expressions.

## Root Cause Analysis

### Problem Location

**File**: `code/src/model_checker/theory_lib/logos/semantic.py`
**Line 13**: `from model_checker.z3_shim import simplify`
**Line 539**: `bit_ab = simplify(bit_a | bit_b)` (uses the statically-bound z3 simplify)

### Technical Explanation

1. When Python imports a module, the `from X import Y` statement resolves `Y` at import time and creates a local binding in the module namespace.

2. The `z3_shim` module uses `__getattr__` for lazy loading, which dynamically retrieves attributes from the active backend (z3 or cvc5).

3. When `semantic.py` is first imported (before `set_cli_backend("cvc5")` is called), the default backend is z3, so `simplify` resolves to `z3.z3.simplify`.

4. After switching backends to cvc5, the `simplify` variable in `semantic.py` still points to the z3 version because Python's import mechanism does not re-evaluate the binding.

5. When `product()` is called with cvc5 BitVec expressions, it passes them to `z3.simplify()`, which raises "Z3 expression expected".

### Verification Evidence

```python
# BEFORE backend switch
semantic_module.simplify.__module__  # 'z3.z3'

# AFTER backend switch to cvc5
# (without module reload)
semantic_module.simplify.__module__  # Still 'z3.z3' - BUG!

# z3_shim.simplify correctly points to cvc5
z3_shim.simplify.__module__  # 'cvc5.pythonic.cvc5_pythonic'
```

### Contrast with Working Pattern

Lines 1320 and 1524 in `semantic.py` use `z3.simplify(result)` where `z3` is imported as `from model_checker import z3_shim as z3`. This works because:
- The access `z3.simplify` triggers `__getattr__` on the module
- `__getattr__` checks the current backend and returns the correct function
- The lookup happens at call time, not import time

## Affected Examples

All examples that use operators requiring `product()` or `coproduct()` methods fail:

| Subtheory | Failing Examples | Common Pattern |
|-----------|------------------|----------------|
| Extensional | EXT_CM_2 | Uses conditional (rightarrow) |
| Modal | MOD_CM_3, MOD_CM_4 | Uses conditional |
| Constitutive | CL_CM_4 through CL_CM_14 (10 examples) | Uses conditional/biconditional |

### Examples That Pass

Examples using only atomic propositions and negation pass because they don't invoke `product()` or `coproduct()`:
- All EXT_TH_* theorems
- All MOD_TH_* theorems
- CL_CM_1, CL_CM_2 (simple structures)

## Proposed Fix

### Primary Fix: Use Dynamic Lookup

**Change line 539** from:
```python
bit_ab = simplify(bit_a | bit_b)
```

To:
```python
bit_ab = z3.simplify(bit_a | bit_b)
```

Where `z3` is already imported as `from model_checker import z3_shim as z3` (line 14).

### Secondary Fix: Remove Static Import

**Remove line 13**:
```python
from model_checker.z3_shim import simplify  # DELETE THIS LINE
```

This import is only used in one place and should be replaced with dynamic access.

### Alternative: Use solver.expressions.simplify

The `solver/expressions.py` module provides a `simplify()` function that uses dynamic backend lookup:

```python
from model_checker.solver.expressions import simplify
```

This is the recommended approach as it aligns with the solver abstraction layer design.

## Code Paths Requiring Modification

| File | Line | Current | Fix |
|------|------|---------|-----|
| `theory_lib/logos/semantic.py` | 13 | `from model_checker.z3_shim import simplify` | Remove |
| `theory_lib/logos/semantic.py` | 539 | `simplify(bit_a \| bit_b)` | `z3.simplify(bit_a \| bit_b)` |

## Verification Steps

1. Run comparison.py after fix to verify all EXT_CM_2, MOD_CM_3, MOD_CM_4, and CL_CM_4-14 examples pass
2. Verify existing z3 tests still pass (regression test)
3. Run the full test suite with both z3 and cvc5 backends

## Additional Notes

### Similar Pattern in models/semantic.py

The base `SemanticDefaults` class in `models/semantic.py` also uses `simplify` at line 251, but it imports from `solver.expressions` which uses dynamic lookup, so it is not affected.

### No Module Reload Needed

The fix is to change the call site from static binding to dynamic lookup. No module reload mechanism is needed because the `z3` module alias triggers `__getattr__` on each attribute access.

## Risk Assessment

- **Low Risk**: Single-line change to use existing dynamic lookup pattern
- **No Breaking Changes**: All existing z3-mode functionality preserved
- **Well-Tested Pattern**: The `z3.simplify()` pattern is already used in lines 1320 and 1524 of the same file
