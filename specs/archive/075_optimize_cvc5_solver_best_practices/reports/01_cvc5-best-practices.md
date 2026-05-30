# Research Report: CVC5 Solver Integration Best Practices

- **Task**: 75 - Optimize CVC5 solver integration following best practices
- **Date**: 2026-03-31
- **Session**: sess_1774996596_KnlqNq
- **Status**: Complete

## Executive Summary

Research into CVC5 documentation and community best practices confirms the two optimizations identified in Task 74, and provides additional recommendations for efficient CVC5 integration. The primary findings:

1. **`is None` pattern is essential** - CVC5's `ModelRef.__len__()` triggers `decls()` enumeration, making truthiness checks ~3000x slower than identity checks
2. **Term IDs are available via `get_id()`** - CVC5 pythonic API provides `term.get_id()` for O(1) term identification, eliminating need for `str()` conversion
3. **Additional optimizations** - Model cores, solver options timing, and evaluation patterns

## CVC5 API Research Findings

### 1. Python API Variants

CVC5 offers two Python APIs:
- **Base Python API**: Direct mapping of C++ API, verbose but feature-complete
- **Pythonic API**: Z3-compatible interface with automatic solver management

The project uses the pythonic API for Z3 compatibility. This is the recommended approach per CVC5 documentation.

**Sources**:
- [Base Python API](https://cvc5.github.io/docs/cvc5-1.1.2/api/python/base/python.html)
- [Pythonic API Tutorial](https://hackmd.io/@s-fish/H1nqUvx6j)

### 2. Term Identification Methods

CVC5 terms support multiple identification approaches:

| Method | Access | Type | Notes |
|--------|--------|------|-------|
| `term.get_id()` | Pythonic | `int` | Unique per solver session |
| `term.ast.getId()` | Base API | `int` | Same value as `get_id()` |
| `term.hash()` | Pythonic | `int` | Hash value (same as id) |
| `id(term)` | Python | `int` | Python object id (different per wrapper) |

**Verification** (from live testing):
```python
x = cvc5p.Int('x')
print(x.get_id())      # 312
print(x.ast.getId())   # 312
print(x.hash())        # 312
```

**Key insight**: `get_id()` returns a stable term identifier that can be used for O(1) term comparison instead of `str()` conversion.

**Source**: [Term API Documentation](https://cvc5.github.io/docs/cvc5-1.0.0/api/cpp/term.html)

### 3. Model Truthiness Behavior

CVC5's `ModelRef` implements `__len__()` which calls `decls()`, enumerating all model declarations:

| Pattern | Time (100 iterations) | Notes |
|---------|----------------------|-------|
| `if model:` | 23.275ms | Triggers `__len__()` -> `decls()` |
| `if model is not None:` | 0.007ms | Direct identity check |

**Ratio**: 3325x slower for truthiness check

For models with many declarations (Task 74 found ~48s for 5 calls with large models), this overhead is catastrophic.

**Source**: [Solvers & Results Documentation](https://cvc5.github.io/docs/cvc5-1.1.0/api/python/pythonic/solver.html)

### 4. Model Evaluation Best Practices

From CVC5 documentation:

1. **Call immediately after `check()`**: `getValue()` and `getModel()` require "immediately" following a satisfiability check
2. **Use `model_completion=True`** selectively: Adds default interpretations for uninterpreted symbols, may add overhead
3. **Model cores available**: `isModelCoreSymbol()` identifies essential symbols when `model-cores` option enabled
4. **Direct indexing preferred**: `model[x]` is more efficient than `model.eval(x)` for simple variable access

**Source**: [Solver Documentation](https://cvc5.github.io/docs/cvc5-1.0.2/api/python/base/solver.html)

### 5. Solver Options

CVC5 options must be set **before** any assertions are added:

```python
# CORRECT: Set options first
solver = cvc5p.Solver()
solver.set('produce-unsat-cores', 'true')
solver.set('tlimit-per', '10000')
solver.add(constraint)  # Now add constraints

# INCORRECT: Will raise RuntimeError
solver.add(constraint)
solver.set('produce-unsat-cores', 'true')  # Error!
```

**Relevant options**:
| Option | Default | Description |
|--------|---------|-------------|
| `produce-models` | false | Enable `getValue`/`getModel` |
| `produce-unsat-cores` | false | Enable unsat core extraction |
| `model-cores` | none | Compute minimal model cores |
| `tlimit-per` | 0 | Per-query timeout (ms) |
| `minimal-unsat-cores` | false | Compute minimal unsat cores |

**Source**: [CVC5 Options Documentation](https://cvc5.github.io/docs/cvc5-1.0.2/options.html)

## Implementation Recommendations

### Fix 1: `is None` Pattern (High Impact)

**Files**: `code/src/model_checker/models/structure.py`

**Locations already fixed** (from Task 74 inspection):
- Line 328-329: `interpret()` - FIXED
- Line 390-391: `_get_relevant_constraints()` - FIXED
- Line 594-595: `print_evaluated_sentences()` - FIXED
- Line 878-879: `extract_verify_falsify_state()` - FIXED

**Pattern**:
```python
# Before (slow for CVC5)
if not self.z3_model:
    return

# After (fast for both backends)
if self.z3_model is None:
    return
```

**Expected impact**: Eliminates ~48s overhead (85% of excess time)

### Fix 2: Term ID-Based Tracking (High Impact)

**File**: `code/src/model_checker/solver/cvc5_adapter.py`

**Current implementation** (from reading the file):
```python
def assert_tracked(self, constraint: Any, label: str) -> None:
    self._tracked[label] = constraint
    self._reverse[id(constraint)] = label
    # String conversion deferred until unsat_core() is called
    self._solver.add(constraint)
```

The current implementation already defers string conversion (line 81 comment indicates this was already addressed). However, the `unsat_core()` method still falls back to string comparison:

```python
def unsat_core(self) -> List[str]:
    # Lazy populate string-to-label mapping
    if not self._str_to_label:
        self._str_to_label = {str(c): lbl for lbl, c in self._tracked.items()}
```

**Recommended enhancement**: Use `get_id()` instead of `str()` for term matching:

```python
def assert_tracked(self, constraint: Any, label: str) -> None:
    self._tracked[label] = constraint
    self._reverse[id(constraint)] = label
    # Use term ID for fast matching (O(1) vs O(n) string comparison)
    if hasattr(constraint, 'get_id'):
        self._term_id_to_label[constraint.get_id()] = label
    self._solver.add(constraint)

def unsat_core(self) -> List[str]:
    core_terms = self._solver.unsat_core()
    labels = []
    for term in core_terms:
        # Try Python object id first
        label = self._reverse.get(id(term))
        if label:
            labels.append(label)
            continue

        # Try term ID (fast, O(1))
        if hasattr(term, 'get_id'):
            label = self._term_id_to_label.get(term.get_id())
            if label:
                labels.append(label)
                continue

        # Fallback to string matching (slow, only if needed)
        # ... existing string logic ...
```

**Expected impact**: Eliminates ~7.9s overhead (14% of excess time)

### Fix 3: Model Core Optimization (Optional)

For large models, enable model cores to reduce enumeration:

```python
solver.set('model-cores', 'simple')  # or 'none', 'simple', 'full'
```

This filters model output to essential symbols only.

### Fix 4: Avoid `len(model)` Calls

If any code uses `len(model)` to check model emptiness, replace with:

```python
# Slow
if len(model) == 0:
    return

# Fast
if model is None:
    return
```

## Performance Summary

| Fix | Overhead Eliminated | Implementation Effort | Status |
|-----|---------------------|----------------------|--------|
| `is None` checks | ~48s (85%) | Low (4 lines) | Already applied |
| Term ID tracking | ~7.9s (14%) | Medium | Enhancement available |
| Model cores | Variable | Low (1 option) | Optional |
| Avoid `len()` | Variable | Low | Audit needed |

## Code Locations Summary

### structure.py (already fixed)
- Line 328-329: `interpret()` method
- Line 390-391: `_get_relevant_constraints()` method
- Line 594-595: `print_evaluated_sentences()` method
- Line 878-879: `extract_verify_falsify_state()` method

### cvc5_adapter.py (enhancement available)
- Line 62-82: `assert_tracked()` - Can add `get_id()` tracking
- Line 128-168: `unsat_core()` - Can use term ID for matching
- Line 27: Constructor - Add `_term_id_to_label` dict

## Web Research Sources

- [CVC5 Python API Overview](https://cvc5.github.io/docs/cvc5-1.0.0/api/python/python.html)
- [Base Python API](https://cvc5.github.io/docs/cvc5-1.1.2/api/python/base/python.html)
- [Pythonic API Tutorial](https://hackmd.io/@s-fish/H1nqUvx6j)
- [Term API (C++)](https://cvc5.github.io/docs/cvc5-1.0.0/api/cpp/term.html)
- [Solver API](https://cvc5.github.io/docs/cvc5-1.0.2/api/python/base/solver.html)
- [Options Reference](https://cvc5.github.io/docs/cvc5-1.0.2/options.html)
- [Solvers & Results](https://cvc5.github.io/docs/cvc5-1.1.0/api/python/pythonic/solver.html)
- [CVC5 TACAS Paper](https://www-cs.stanford.edu/~preiner/publications/2022/BarbosaBBKLMMMN-TACAS22.pdf)
- [CVC5 GitHub Repository](https://github.com/cvc5/cvc5)

## Conclusion

The CVC5 best practices research confirms Task 74's findings and provides the technical basis for implementation:

1. **`is None` pattern**: Essential for CVC5 compatibility, already applied in structure.py
2. **Term ID tracking**: Available via `get_id()`, can eliminate string conversion overhead
3. **Solver options**: Must be set before assertions, cannot be changed at runtime

After implementing the recommended fixes, CVC5 should perform at ~20x slower than Z3 (raw solver ratio) rather than the original 32x overhead.
