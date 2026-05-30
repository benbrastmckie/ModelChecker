# Teammate A Findings: Model-Checker Architecture Analysis

- **Task**: 75 - Optimize CVC5 solver integration following best practices
- **Role**: Teammate A - Primary Architecture Analysis
- **Date**: 2026-03-31
- **Confidence**: High

## Executive Summary

The model-checker uses a clean Protocol-based adapter pattern for solver abstraction.
Both `Z3SolverAdapter` and `CVC5SolverAdapter` implement `TrackedSolverProtocol` without
formal inheritance - relying on structural subtyping via Python Protocols. The `is None`
pattern is already fully applied in `structure.py`. The term ID tracking optimization
belongs in `cvc5_adapter.py`, added as a third lookup tier in the existing three-tier
fallback chain.

---

## Architecture Diagram

```
                     User / CLI / Settings
                            |
                            v
              ┌─────────────────────────┐
              │  registry.get_active_   │
              │  backend() / create_    │
              │  solver()               │
              └──────────┬──────────────┘
                         |
          +--------------+-------------+
          |                            |
          v                            v
  ┌───────────────┐          ┌──────────────────┐
  │ Z3SolverAdapter│         │CVC5SolverAdapter │
  │               │         │                  │
  │  _solver:     │         │  _solver:        │
  │  z3.Solver    │         │  cvc5.pythonic   │
  │               │         │  .Solver         │
  │  _tracked:    │         │                  │
  │  {label->expr}│         │  _tracked:       │
  └───────────────┘         │  {label->expr}   │
          |                 │  _reverse:       │
          |                 │  {id(expr)->lbl} │
          |                 │  _str_to_label:  │ <-- lazy string fallback
          |                 │  {str->label}    │
          |                 └──────────────────┘
          |                          |
          +----------+---------------+
                     |
                     v
          ┌──────────────────────┐
          │  TrackedSolverProtocol│  (structural, not inherited)
          │  - add()             │
          │  - check()           │
          │  - model()           │
          │  - assert_tracked()  │
          │  - unsat_core()      │
          │  - push() / pop()    │
          └──────────────────────┘
                     |
                     v
          ┌──────────────────────┐
          │  ModelDefaults       │  (models/structure.py)
          │  (solve, re_solve,   │
          │   interpret, etc.)   │
          │  self.z3_model       │  <-- holds raw model ref
          └──────────────────────┘
                     |
       +-------------+------------+
       |                          |
       v                          v
┌──────────────┐          ┌───────────────────┐
│ iterate/     │          │ theory_lib/       │
│ constraints. │          │ */semantic.py     │
│ py           │          │                  │
│ (CVC5 path:  │          │ accesses         │
│  reuses raw  │          │ self.z3_model    │
│  _solver for │          │ directly via     │
│  iteration)  │          │ model.eval()     │
└──────────────┘          └───────────────────┘
```

### z3_shim.py Role

```
┌─────────────────────────────────┐
│  z3_shim.py                     │
│  (transitional shim)            │
│                                 │
│  __getattr__(name) ->           │
│    if backend == "z3":          │
│      return z3.name             │
│    if backend == "cvc5":        │
│      return cvc5.pythonic.name  │
│                                 │
│  Registered with lifecycle:     │
│  _reset_backend() called on     │
│  backend switch                 │
└─────────────────────────────────┘
```

The shim is a transitional compatibility layer - code using
`from model_checker import z3_shim as z3` gets the correct backend
module transparently. The target is migration to
`model_checker.solver.expressions` (already exists as a replacement).

---

## 1. Adapter Pattern Analysis

### Interface Contracts

**`TrackedSolverProtocol`** (defined in `solver/protocols.py`):
- Extends `SolverProtocol` with `assert_tracked(constraint, label)` and `unsat_core()`
- Runtime-checkable via `@runtime_checkable`
- Both adapters satisfy this via structural subtyping - no explicit inheritance required

**Both adapters implement the same surface:**

| Method | Z3SolverAdapter | CVC5SolverAdapter | Notes |
|--------|-----------------|-------------------|-------|
| `add(constraint)` | direct passthrough | type-checked + passthrough | Z3 slightly thinner |
| `assert_tracked(constraint, label)` | uses z3.Bool + assert_and_track | manual dict tracking | Key difference |
| `check(*assumptions)` | returns SolverResult string | returns SolverResult string | Same interface |
| `model()` | returns z3.ModelRef | returns cvc5 ModelRef | Both satisfy ModelProtocol |
| `unsat_core()` | trivial (z3 native) | complex 3-tier lookup | Main complexity point |
| `push/pop` | direct passthrough | direct passthrough | Identical |
| `set_timeout(ms)` | uses 'timeout' option | uses 'tlimit-per' option | Different option names |
| `reset()` | direct + clear dict | handles missing reset | Defensive handling |
| `raw_solver` property | returns z3.Solver | returns cvc5.pythonic.Solver | Escape hatch |

### Key Structural Difference: assert_tracked / unsat_core

Z3 natively supports `assert_and_track(constraint, bool_var)` and `unsat_core()` returns
the bool vars. CVC5 lacks this native pattern, so `CVC5SolverAdapter` maintains its own
tracking dictionaries:

- `_tracked: Dict[str, Any]` - label to constraint
- `_reverse: Dict[int, str]` - `id(constraint)` to label (Python object ID)
- `_str_to_label: Dict[str, str]` - lazy-populated string representation to label

The unsat_core lookup tries these in order:
1. `_reverse[id(term)]` - O(1) Python object identity (fast, unreliable across sessions)
2. `_str_to_label[str(term)]` - O(1) string lookup (but populating is expensive: ~15ms/term)
3. Linear scan via `str(constraint) == term_str` - O(n) last resort

---

## 2. The `is None` Pattern - Current Status

**All critical locations in `structure.py` already use `is None`:**

| Line | Method | Pattern Used |
|------|--------|--------------|
| 110 | `__init__` exit guard | `if self.z3_model is None:` |
| 329 | `interpret()` | `if self.z3_model is None:` |
| 391 | `_get_relevant_constraints()` | `if self.z3_model is not None:` |
| 595 | `print_input_sentences()` | `if self.z3_model is None:` |
| 879 | `extract_verify_falsify_state()` | `if self.z3_model is None:` |

**Other files also use correct patterns:**
- `iterate/iterator.py:52` - uses `z3_model is None`
- `builder/example.py:260` - uses `z3_model is None`
- `theory_lib/logos/semantic.py:1465, 1693` - use `z3_model is not None` and `is None`
- `theory_lib/bimodal/semantic.py:1820+` - uses `z3_model is None`
- `utils/testing.py:140` - uses `z3_model is not None`

**No remaining `if not self.z3_model:` or `if self.z3_model:` patterns found.**

This fix is already complete across all files.

---

## 3. Term ID Tracking - Recommended Design

### Where to Add It

Term ID tracking belongs in `CVC5SolverAdapter` as a **third lookup tier** in the
`_term_id_to_label` dict, inserted between the existing Python object ID lookup and
the expensive string fallback.

**Why in the adapter, not a higher abstraction:**
- The `TrackedSolverProtocol` interface is already adequate - callers just need `unsat_core()` to return labels
- The tracking strategy is an internal implementation detail of each adapter
- Z3 does not need this (Z3's native tracking is already O(1))
- Adding term ID tracking to a shared base class would pollute the interface unnecessarily

### Minimal Required Changes to `cvc5_adapter.py`

**Constructor** - add one dict:
```python
def __init__(self) -> None:
    # ... existing setup ...
    self._tracked: Dict[str, Any] = {}
    self._reverse: Dict[int, str] = {}
    self._str_to_label: Dict[str, str] = {}
    self._term_id_to_label: Dict[int, str] = {}  # NEW: term.get_id() -> label
```

**`assert_tracked()`** - add term ID registration:
```python
def assert_tracked(self, constraint: Any, label: str) -> None:
    from .type_guards import assert_backend_types
    assert_backend_types(constraint, "cvc5")
    self._tracked[label] = constraint
    self._reverse[id(constraint)] = label
    # NEW: Register term ID for O(1) lookup (faster than str fallback)
    if hasattr(constraint, 'get_id'):
        self._term_id_to_label[constraint.get_id()] = label
    self._solver.add(constraint)
```

**`unsat_core()`** - insert term ID tier before string fallback:
```python
def unsat_core(self) -> List[str]:
    try:
        core_terms = self._solver.unsat_core()
    except Exception:
        return []

    labels = []
    for term in core_terms:
        # Tier 1: Python object id (fastest, may miss across solver sessions)
        label = self._reverse.get(id(term))
        if label:
            labels.append(label)
            continue

        # Tier 2: CVC5 term ID - O(1), stable within solver session  [NEW]
        if hasattr(term, 'get_id'):
            label = self._term_id_to_label.get(term.get_id())
            if label:
                labels.append(label)
                continue

        # Tier 3: String representation - lazy-populate only if needed
        if not self._str_to_label:
            self._str_to_label = {str(c): lbl for lbl, c in self._tracked.items()}
        term_str = str(term)
        label = self._str_to_label.get(term_str)
        if label:
            labels.append(label)
            continue

        # Tier 4: Linear scan fallback (last resort)
        for lbl, constraint in self._tracked.items():
            if str(constraint) == term_str:
                labels.append(lbl)
                break

    return labels
```

**`reset()`** - clear the new dict:
```python
def reset(self) -> None:
    # ... existing reset logic ...
    self._tracked.clear()
    self._reverse.clear()
    self._str_to_label.clear()
    self._term_id_to_label.clear()  # NEW
```

---

## 4. How to Make It Backend-Agnostic for Future Solvers

The current design is already well-structured for extensibility. Recommendations:

### Option A: No Change (Current Design is Adequate)

The `TrackedSolverProtocol` interface is backend-agnostic. Each adapter encapsulates its
own tracking strategy. A future solver adapter would implement the same interface and use
whatever term identification method that solver provides.

This is the recommended approach - protocol-based duck typing without shared base classes
gives maximum flexibility.

### Option B: Document the Term-ID Convention

Add a comment to `TrackedSolverProtocol` or the adapter docstring noting that adapters
should implement O(1) term lookup where possible, preferring native term IDs over string
representations. This serves as guidance for future adapter authors without imposing
structure.

### Option C: Optional `TermIdMixin` (over-engineering for now)

Not recommended at this scale, but a `TermIdMixin` could provide `_register_term_id()`
and `_lookup_term_id()` helpers if more adapters needed this pattern.

---

## 5. Model Access Patterns - Abstraction Boundaries

### How `structure.py` Accesses Models

`ModelDefaults` calls `self.solver.model()` which returns whatever the adapter's
`model()` method returns:
- Z3: returns `z3.ModelRef`
- CVC5: returns `cvc5.pythonic` model object

Both are stored as `self.z3_model` (legacy naming) and accessed via:
- `self.z3_model.eval(expr, model_completion=True)` - used in `extract_verify_falsify_state()`
- `self.z3_model is None` - all guards use identity checks (already fixed)

The `compat.py` module provides `eval_model()` which handles the `eval()` vs `evaluate()`
API difference, but `structure.py` calls `self.z3_model.eval()` directly, relying on
`ModelProtocol` compatibility.

### Boundary: `iterate/constraints.py`

This is the most complex boundary. For CVC5, the iterator **bypasses the adapter entirely**
and accesses the raw `cvc5.pythonic.Solver` directly:

```python
from model_checker.solver.cvc5_adapter import CVC5SolverAdapter
if isinstance(original_solver, CVC5SolverAdapter):
    raw = original_solver._solver  # Direct access to internal solver
    return raw
```

This is documented as intentional: CVC5 does not support assertion-copying between solver
instances (unlike Z3). The raw solver is reused to avoid this limitation.

**Implication**: Any changes to `CVC5SolverAdapter._solver` initialization or option-setting
could affect iteration behavior. The `_term_id_to_label` additions do not affect this path.

---

## 6. Shim Layer Role

`z3_shim.py` serves three purposes:
1. **Backward compatibility**: Existing code using `from model_checker import z3_shim as z3`
   continues to work with both backends
2. **Lazy loading**: Backend module cached after first access, reset via lifecycle hook
3. **Transitional marker**: The module docstring explicitly labels it "transitional" and
   points to `model_checker.solver.expressions` as the migration target

The shim does NOT need modification for either optimization. It is transparent to the
`is None` fix and to the term ID tracking (which lives entirely in `cvc5_adapter.py`).

---

## Summary of Findings

| Concern | Finding | Confidence |
|---------|---------|------------|
| `is None` pattern status | Fully applied in all relevant locations | High |
| Term ID tracking location | `cvc5_adapter.py` only, not shared base | High |
| Interface adequacy | `TrackedSolverProtocol` is sufficient | High |
| Backend-agnostic design | Current protocol approach is correct | High |
| Iteration path for CVC5 | Bypasses adapter, uses raw solver directly | High |
| Z3 shim role | Transitional compatibility layer, unaffected | High |

### Primary Recommendation

Implement term ID tracking as described in section 3. Changes are minimal (4 locations in
`cvc5_adapter.py`, ~10 lines total) and fully contained within that file. No changes to
`protocols.py`, `structure.py`, or any other files are needed for this optimization.

The `is None` pattern fix is already complete - no action required.
