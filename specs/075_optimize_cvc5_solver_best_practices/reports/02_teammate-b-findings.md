# Research Report: Alternative Design Patterns for Solver Abstraction

- **Task**: 75 - Optimize CVC5 solver integration following best practices
- **Teammate**: B - Alternative Approaches and Prior Art
- **Date**: 2026-03-31
- **Status**: Complete

## Executive Summary

After analyzing the current solver abstraction architecture and surveying relevant prior art (pySMT, SMT-LIB tooling, and multi-solver Python frameworks), the project's **Adapter pattern** implementation is already well-chosen. The key design question is not which pattern to use but how to handle term identification within each adapter cleanly. The recommended approach is a **per-adapter TermTracker** (a private implementation detail within `CVC5SolverAdapter`) rather than a shared abstraction. This keeps the common `TrackedSolverProtocol` clean while allowing each backend to use its native term identity mechanism.

---

## Design Pattern Comparison

### Pattern 1: Strategy Pattern

In the Strategy pattern, the algorithm (here: term tracking) is extracted into an interchangeable class that is injected at runtime.

**Applied to term tracking**:
```python
class TermTracker(Protocol):
    def register(self, term: Any, label: str) -> None: ...
    def lookup(self, term: Any) -> Optional[str]: ...

class CVC5TermTracker:
    def register(self, term, label):
        self._by_id[term.get_id()] = label
    def lookup(self, term):
        return self._by_id.get(term.get_id())

class Z3TermTracker:
    def register(self, term, label):
        self._by_py_id[id(term)] = label
    def lookup(self, term):
        return self._by_py_id.get(id(term))
```

**Pros**:
- Clean separation of term identification logic
- Testable in isolation
- Supports adding trackers for new backends (Bitwuzla, Yices) without modifying adapters

**Cons**:
- Adds a layer of indirection that provides little benefit when each adapter already owns its own tracking logic
- Creates a shared interface for something that is not actually shared across backends
- `Z3TermTracker` is trivial (Z3's `assert_and_track` does not need custom tracking)

**Verdict**: Overkill for the current two-backend scenario. Appropriate only if TermTracker needs to be composed or swapped independently of the adapter.

### Pattern 2: Adapter Pattern (Current)

The project already uses the Adapter pattern: `CVC5SolverAdapter` and `Z3SolverAdapter` wrap their respective solver objects behind the `TrackedSolverProtocol` interface.

**Applied to term tracking**:
Term tracking is a private concern of each adapter. `CVC5SolverAdapter` uses whatever approach is most efficient for cvc5 internals; `Z3SolverAdapter` uses Z3's native `assert_and_track`.

**Pros**:
- Matches the existing architecture exactly
- Each adapter owns all backend-specific knowledge
- Protocol surface stays minimal and stable
- No shared abstraction where none is needed

**Cons**:
- `CVC5SolverAdapter._str_to_label` and `_reverse` are ad-hoc; term ID approach is not documented as the canonical tracking mechanism

**Verdict**: Best fit for the current problem. Enhancing the CVC5 adapter's internal tracking to use `get_id()` is an implementation detail change requiring no architectural change.

### Pattern 3: Bridge Pattern

The Bridge pattern separates an abstraction hierarchy from an implementation hierarchy so both can vary independently.

**Applied here**:
```
SolverFacade (abstraction)
    |
    +-- TrackedSolverFacade
            |
    SolverBackend (implementation)
            |
            +-- Z3Backend
            +-- CVC5Backend
```

**Pros**:
- Enables clean future extension: a `TimeoutSolverFacade` or `ProfiledSolverFacade` can wrap any backend
- Supports orthogonal variation of facade and backend

**Cons**:
- The project's Protocol-based design already achieves this through structural typing
- Introducing explicit Bridge inheritance hierarchies adds boilerplate to a Python codebase that benefits from duck typing
- The existing `TrackedSolverProtocol` already serves as the abstraction layer

**Verdict**: The Protocol-based approach in the codebase is a structural-typing equivalent of Bridge. No change needed.

### Pattern 4: Template Method Pattern

The base adapter provides a template for `assert_tracked` and `unsat_core`, with hooks for backend-specific term identification.

**Applied here**:
```python
class BaseSolverAdapter:
    def assert_tracked(self, constraint, label):
        self._label_map[label] = constraint
        self._register_term(constraint, label)  # hook
        self._add_to_solver(constraint)

    def _register_term(self, term, label):
        """Override in subclass for backend-specific registration."""
        pass
```

**Pros**:
- Eliminates duplicated `assert_tracked` structure
- Makes the common flow explicit

**Cons**:
- Python inheritance is heavier than Protocol-based duck typing
- Z3's `assert_and_track` replaces the tracking entirely, making the template structure misleading
- The two adapters have fundamentally different tracking strategies, not just different implementations of the same strategy

**Verdict**: Not appropriate. The adapters' tracking strategies differ too much to share a template.

---

## Design Pattern Comparison Matrix

| Pattern | Fit | Complexity | Extensibility | Matches Existing Style |
|---------|-----|------------|---------------|------------------------|
| Adapter (current) | High | Low | Medium | Yes (exact match) |
| Strategy | Medium | Medium | High | Partial |
| Bridge | Medium | High | High | No (requires inheritance) |
| Template Method | Low | Medium | Low | No (requires inheritance) |

**Recommendation**: Continue with the Adapter pattern. Enhance `CVC5SolverAdapter` internals to use `get_id()` as a pure implementation detail.

---

## Prior Art: How Multi-Solver Systems Handle Backend Differences

### pySMT

pySMT ([github.com/pysmt/pysmt](https://github.com/pysmt/pysmt)) is the closest prior art: a Python framework supporting Z3, CVC4/CVC5, Yices, MathSAT, and others via a unified formula language.

**Key design decisions**:

1. **Shared formula representation**: pySMT defines its own AST (`pysmt.formula`). All formulas are translated into backend-native terms at solve time. This eliminates the term identity problem entirely since pySMT terms are Python objects with stable Python `id()` values.

2. **Solver-specific converters**: Each solver has a `Converter` class that translates pySMT formulas to backend terms. The converter maintains a `memoization` dict keyed on pySMT term identity, not backend term identity.

3. **No shared TermTracker**: Each `Solver` adapter owns its own formula-to-solver-term mapping. The Z3 solver uses Z3's native API; the CVC5 solver uses CVC5's native API. There is no common term-tracking interface.

4. **Implications for this project**: The ModelChecker project takes a simpler approach: it uses the backend's native expression types directly (Z3 BitVec or CVC5 BitVec), avoiding the cost of a separate formula layer. This means term identity cannot be delegated to a shared layer and must be handled per-adapter.

**Lesson**: The per-adapter tracking strategy in the current codebase is consistent with how pySMT handles this, despite pySMT's added formula-translation layer.

### SMT-LIB Tools (z3, CVC5 standalone)

SMT-LIB tools (the standard input format) are irrelevant here since the project uses programmatic APIs, not textual SMT-LIB. The term identity problem is a programmatic API concern.

### Dolmen / Alt-Ergo (OCaml SMT tooling)

OCaml SMT tools use algebraic types for terms, giving structural equality for free. Python lacks this, requiring explicit tracking strategies. No lessons directly applicable.

### SMTInterpol / JavaSMT

JavaSMT ([github.com/sosy-lab/java-smt](https://github.com/sosy-lab/java-smt)) is the closest Java equivalent to this project's architecture. Key finding: JavaSMT wraps each solver behind `ProverEnvironment`. For term tracking, it maintains `Map<BooleanFormula, String>` where `BooleanFormula` wraps solver-native terms. Identity uses solver-native equality (`isSame()` method on the formula wrapper).

**Lesson**: Using a solver-native equality check (`get_id()` for CVC5, `eq()` for Z3) is standard practice in multi-solver Java frameworks. The Python equivalent is using `get_id()` in the CVC5 adapter.

---

## Recommended Abstraction Approach

The recommended approach enhances the CVC5 adapter's internal tracking to use term IDs with a clean, layered fallback strategy. No protocol changes are needed.

### Layered Term Identification (for CVC5)

CVC5 terms returned in `unsat_core()` may not be the same Python objects that were originally added (they are reconstructed from solver state). The identification strategy should be:

```
Layer 1: Python object identity (id(term))
         - Fast O(1)
         - Works when cvc5 returns the same wrapper object
         - Succeeds: ~50% of the time in practice

Layer 2: CVC5 term ID (term.get_id())
         - Fast O(1)
         - Stable across wrapper reconstruction
         - Succeeds: when Layer 1 fails due to wrapper recreation
         - Available: cvc5 >= 1.0

Layer 3: String representation (str(term))
         - Slow O(n) (deferred to here)
         - Structural equality fallback
         - Succeeds: when term was rebuilt with identical structure
         - Cost: ~15ms per term (only pays when Layers 1 and 2 fail)
```

### Recommended Interface Design (Pseudocode)

No protocol changes needed. The enhancement is entirely within `CVC5SolverAdapter`:

```python
class CVC5SolverAdapter:
    def __init__(self):
        self._solver = CVC5Solver()
        self._solver.set('produce-unsat-cores', 'true')

        self._tracked: Dict[str, Any] = {}          # label -> constraint
        self._by_py_id: Dict[int, str] = {}          # id(constraint) -> label
        self._by_term_id: Dict[int, str] = {}        # constraint.get_id() -> label
        # _by_str populated lazily only if Layers 1 and 2 both fail
        self._by_str: Dict[str, str] = {}
        self._str_populated: bool = False

    def assert_tracked(self, constraint: Any, label: str) -> None:
        self._tracked[label] = constraint
        self._by_py_id[id(constraint)] = label
        # Register term ID immediately (O(1), no string cost)
        if hasattr(constraint, 'get_id'):
            self._by_term_id[constraint.get_id()] = label
        self._solver.add(constraint)

    def unsat_core(self) -> List[str]:
        core_terms = self._solver.unsat_core()
        labels = []
        for term in core_terms:
            # Layer 1: Python object identity
            label = self._by_py_id.get(id(term))
            if label:
                labels.append(label)
                continue
            # Layer 2: CVC5 term ID
            if hasattr(term, 'get_id'):
                label = self._by_term_id.get(term.get_id())
                if label:
                    labels.append(label)
                    continue
            # Layer 3: String fallback (lazy, expensive)
            if not self._str_populated:
                self._by_str = {str(c): lbl for lbl, c in self._tracked.items()}
                self._str_populated = True
            label = self._by_str.get(str(term))
            if label:
                labels.append(label)
        return labels

    def reset(self):
        # Must clear all tracking state on reset
        self._tracked.clear()
        self._by_py_id.clear()
        self._by_term_id.clear()
        self._by_str.clear()
        self._str_populated = False
        # ... solver reset ...
```

**Why not expose TermTracker as a public abstraction**: The Z3 adapter does not need any of this - it uses Z3's native `assert_and_track` which stores labels as named boolean variables inside the solver itself. Adding a shared `TermTracker` abstraction would create a facade over a problem that only exists for one of the two backends.

---

## Handling Solver-Specific Features Without Protocol Pollution

The current approach is sound: backend-specific features are exposed through the `raw_solver` escape hatch:

```python
@property
def raw_solver(self) -> Any:
    """Access underlying solver directly (use sparingly)."""
    return self._solver
```

For features that genuinely benefit both backends, they belong in the protocol. For CVC5-specific features (like `set('model-cores', 'simple')`), they remain in `CVC5SolverAdapter` as named methods or via `raw_solver`.

**Recommended additions to `CVC5SolverAdapter`** (not to the protocol):

```python
def enable_model_cores(self, mode: str = 'simple') -> None:
    """Enable model core computation (reduces model enumeration cost).
    Must be called before any assertions are added."""
    self._solver.set('model-cores', mode)
```

This keeps the protocol clean and documents the timing constraint (must be called before `add()`).

---

## Extensibility: Adding Future Backends

The current registry-based factory pattern (`registry.py`) is already extensible. Adding Bitwuzla or Yices requires:

1. Create `bitwuzla_adapter.py` implementing `TrackedSolverProtocol`
2. Add `detect_bitwuzla()` and `"bitwuzla"` to `registry.py`
3. Register the factory in `create_solver()`

For term tracking in new backends:
- **Bitwuzla**: Provides `term.id()` (integer), matching the CVC5 `get_id()` pattern exactly
- **Yices**: Terms are integer indices internally; Python API exposes term IDs directly
- **MathSAT**: Uses `msat_term` handles; identity via Python id() is stable

All future backends will fit the Adapter pattern. The layered fallback strategy (py_id -> term_id -> str) is generalizable: each backend would add its native ID method to Layer 2.

**Suggested extensibility hook for future backends**:

```python
def _get_term_id(term: Any) -> Optional[int]:
    """Get backend-native term ID for O(1) identity lookup.
    Returns None if backend does not support stable term IDs."""
    # CVC5 and Bitwuzla
    if hasattr(term, 'get_id'):
        return term.get_id()
    # Yices-style backends
    if hasattr(term, 'term_id'):
        return term.term_id
    return None
```

This helper can live in `compat.py` or as a private method in a shared base.

---

## Automatic vs. Per-Solver vs. Opt-In Optimization Configuration

| Strategy | Description | Recommendation |
|----------|-------------|----------------|
| Automatic | Always use `get_id()` when available | Best choice for term ID tracking |
| Per-solver config | Pass `use_term_ids=True` to adapter | Unnecessary complexity |
| Opt-in | User explicitly enables optimization | Wrong level; user should not need to know |

**Recommendation**: The `get_id()` optimization should be automatic and transparent. The `hasattr(constraint, 'get_id')` guard provides safety if CVC5 ever removes this API. No user-facing configuration is needed.

For model cores (`set('model-cores', 'simple')`), per-solver configuration is appropriate since it affects solver completeness semantics, not just performance. This should be a named method on `CVC5SolverAdapter`, not a protocol concern.

---

## Documentation Recommendations

Backend-specific behavior should be documented at three levels:

### 1. Adapter-level docstring

At the class level, explain the tracking strategy and its rationale:

```python
class CVC5SolverAdapter:
    """Wraps cvc5.pythonic.Solver with TrackedSolverProtocol interface.

    Term Tracking Strategy
    ----------------------
    CVC5's unsat_core() returns term objects that may be different Python
    wrappers than the originally added terms (wrappers are recreated from
    solver state). To identify core terms, we use a three-layer strategy:

    1. Python object identity (id()) - fastest, works ~50% of the time
    2. CVC5 term ID (term.get_id()) - O(1), stable across wrapper recreation
    3. String representation - O(n) fallback, computed lazily

    Performance Notes
    -----------------
    - Do NOT check CVC5 ModelRef truthiness (if model:). Use (model is not None).
      ModelRef.__len__() enumerates all declarations (~9.5s for large models).
    - str(term) on CVC5 terms is ~15ms; defer until Layer 3 is needed.
    """
```

### 2. Method-level inline comments

For non-obvious choices (already present in the codebase but should be extended):

```python
# Use term.get_id() rather than str(term): get_id() is O(1) and stable
# across wrapper recreation. str() is ~15ms and scales with expression depth.
if hasattr(constraint, 'get_id'):
    self._by_term_id[constraint.get_id()] = label
```

### 3. CLAUDE.md or solver/README.md

For maintainers adding new backends, document the term ID protocol:

```
## Adding a New Backend

When implementing a new adapter:
- Implement TrackedSolverProtocol (see protocols.py)
- For term tracking in unsat_core(), prefer native term IDs over str()
  - CVC5: term.get_id() returns stable int
  - Z3: uses assert_and_track (no custom tracking needed)
  - Bitwuzla: term.id() returns stable int
- ModelRef truthiness: always use "is None" check, not bool(model)
```

---

## Confidence Assessment

| Finding | Confidence | Basis |
|---------|------------|-------|
| Adapter pattern is correct choice | High | Matches codebase style; consistent with pySMT, JavaSMT prior art |
| Per-adapter TermTracker (not shared) | High | Z3 uses different mechanism entirely; no shared interface makes sense |
| `get_id()` as Layer 2 in fallback chain | High | Confirmed in Task 75 Report 01; CVC5 docs confirm stability |
| Automatic (not opt-in) optimization | High | No correctness tradeoff; guard via `hasattr` for safety |
| Current protocol surface is correct | High | No changes to TrackedSolverProtocol needed |
| Future backends will fit this pattern | Medium | Bitwuzla/Yices have term IDs; MathSAT untested |
| Layered fallback hitting Layer 3 is rare | Medium | Observed ~50% hit rate for Layer 1 in informal testing from Task 74 findings; Layer 2 should cover the rest |

---

## Summary Recommendations

1. **No protocol changes needed**: `TrackedSolverProtocol` is already correct and complete.

2. **Enhance `CVC5SolverAdapter` internals only**: Add `_by_term_id` dict populated via `get_id()` in `assert_tracked()`, and use it in `unsat_core()` before falling back to string matching.

3. **Rename internal dicts for clarity**: `_reverse` -> `_by_py_id` communicates intent; `_str_to_label` -> `_by_str` is simpler.

4. **Add `_str_populated` flag**: Prevents repopulating the string dict across multiple `unsat_core()` calls when strings are never needed (the common case).

5. **Document the tracking strategy**: Add class-level docstring explaining the three-layer approach and its performance rationale.

6. **No shared TermTracker abstraction**: Creates complexity without benefit for a two-backend system where the backends use fundamentally different mechanisms.
