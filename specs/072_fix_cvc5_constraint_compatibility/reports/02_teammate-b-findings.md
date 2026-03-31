# CVC5 Constraint Compatibility: Alternative Approaches and Prior Art

## Task Context

Research into alternative architectures and prior art for the Z3-CVC5 dual-backend compatibility problem.
This report complements Teammate A's analysis of the SMT-LIB interchange approach.

---

## Key Findings

### 1. The Real Root Cause is Simpler Than the Error Suggests

Hands-on investigation reveals the actual failure is **not** that Z3 expressions are irreversibly
embedded in the constraint pipeline. It is a **module caching problem** in `z3_shim.py`.

When the solver backend is changed (e.g., via `set_cli_backend('cvc5')`), `z3_shim._backend_module`
retains the previously-loaded `z3` module unless `z3_shim._reset_backend()` is explicitly called.
The semantics layer then creates Z3-typed expressions and passes them to the CVC5 solver.

**Verified behavior**:
```python
# Backend=z3 first access
z3_shim._backend_module = <module 'z3'>        # cached on first access
# Backend switches to cvc5 BUT no reset
z3_shim.BitVec('x', 4)                         # returns z3.z3.BitVecRef, not cvc5!
```

**Verified fix**:
```python
reset_registry()
set_cli_backend('cvc5')
z3_shim._reset_backend()      # <-- required
reset_atom_sort()              # <-- also required (AtomSort is globally cached)
# Now:
LogosSemantics({'N': 4, 'solver': 'cvc5'})   # creates cvc5.pythonic types correctly
```

**This means the cvc5.pythonic API is already Z3-compatible by design.** The library was built
as a drop-in replacement and the function signatures are identical. No expression conversion is
needed if the shim and atom sort caches are properly invalidated before use.

### 2. Secondary Issue: `AtomSort` Global Cache

The `get_atom_sort()` function in `syntactic/atoms.py` uses a module-level cache:
```python
_atom_sort = None

def get_atom_sort() -> Any:
    global _atom_sort
    if _atom_sort is None:
        _atom_sort = DeclareSort("AtomSort")   # Created via solver/expressions.py
    return _atom_sort
```

If `AtomSort` was created with the Z3 backend, it becomes a `z3.SortRef`. If a CVC5 solver is
later used, the atom sort is the wrong type. The `reset_atom_sort()` function exists for exactly
this purpose but is not called during backend switching.

### 3. Three-Location Cache Problem

The complete set of caches that must be invalidated when switching backends:

| Location | Reset Function | Called During Backend Switch? |
|----------|---------------|-------------------------------|
| `z3_shim._backend_module` | `z3_shim._reset_backend()` | NO - must be called manually |
| `syntactic/atoms._atom_sort` | `reset_atom_sort()` | NO - must be called manually |
| `solver/registry._available_backends` | `reset_registry()` | YES - in test infrastructure |

The test file `test_solver_comparison.py` already calls `z3_shim._reset_backend()` and
`reset_registry()` in its `reset_state` fixture, which is why integration tests work.
But production code paths do not perform this full reset.

### 4. Prior Art: pySMT's Architecture

pySMT (the most widely-used multi-solver Python library) solves this problem with a
**solver-independent intermediate representation**:

- All formulas are created as `FNode` objects (solver-agnostic)
- A `Converter` class translates `FNode` trees to solver-specific expressions at solve time
- Forward and backward conversion with caching
- The `DagWalker` pattern traverses formula trees systematically

**Key insight from pySMT**: They maintain solver-specific contexts and avoid mixing expressions
between contexts entirely. Each solver backend gets fresh expressions created in its own context.

This approach is architecturally robust but represents a significant rewrite. The ModelChecker
codebase has instead chosen an API-compatibility approach (cvc5.pythonic mimics z3), which is
a valid alternative that requires much less refactoring.

### 5. CVC5 Pythonic is an Intentional Z3 Drop-In

From the cvc5_pythonic_api README: "This API is based on Z3's Python API: Z3Py, both in spirit
and in code. It includes a substantial amount of Z3Py's source."

This confirms the design intent: code that uses Z3's Python API should work with cvc5.pythonic
by changing imports. The `z3_shim.py` module was designed to exploit exactly this property.

The cvc5.pythonic API provides:
- Identical function signatures: `BitVec`, `BitVecVal`, `And`, `Or`, `Not`, `Implies`, `Function`
- Same expression introspection: `decl().kind()`, `num_args()`, `children()`
- Same `substitute()` interface
- Compatible `ForAll`/`Exists` behavior (though ModelChecker uses its own expansion-based versions)

**The API compatibility has been verified to work** - `LogosSemantics` can be created with
CVC5 types when the caches are properly reset.

---

## Recommended Approach

**Option B: Fix the Initialization Ordering** (preferred over Teammate A's Option A)

The correct fix is to ensure proper initialization order and cache invalidation rather than adding
expression conversion infrastructure. This approach:

1. Requires minimal code changes
2. Has no runtime overhead (no conversion at constraint-add time)
3. Is architecturally correct (expressions stay in their native types throughout)
4. Leverages the existing API-compatibility between z3 and cvc5.pythonic

### Implementation

**Step 1: Fix backend switching in registry** (`solver/registry.py`)

Add a callback/notification mechanism so that when `set_cli_backend()` or `get_active_backend()`
determines a new backend, dependent caches are invalidated:

```python
def set_cli_backend(backend: str) -> None:
    global _cli_override
    if backend not in ("z3", "cvc5"):
        raise ValueError(f"Unknown solver backend: {backend}")
    _cli_override = backend
    _invalidate_expression_caches()   # NEW

def _invalidate_expression_caches() -> None:
    """Invalidate all backend-specific caches when backend changes."""
    try:
        from model_checker.z3_shim import _reset_backend
        _reset_backend()
    except ImportError:
        pass
    try:
        from model_checker.syntactic.atoms import reset_atom_sort
        reset_atom_sort()
    except ImportError:
        pass
```

**Step 2: Ensure settings-driven backend is set early** (`builder/example.py`)

The `_initialize_z3_context` method currently resets the Z3 context but does not set the solver
backend from settings. Add backend initialization:

```python
def _initialize_z3_context(self) -> None:
    """Reset solver context and set backend from settings."""
    # Set backend before any expression construction
    settings = self.example_settings or {}
    solver_backend = settings.get('solver', 'z3')
    from model_checker.solver.registry import set_cli_backend
    set_cli_backend(solver_backend)   # This will also invalidate caches
```

**Step 3: Update `reset_registry()` to also reset expression caches** (`solver/registry.py`)

```python
def reset_registry() -> None:
    """Reset the registry state (useful for testing)."""
    global _available_backends, _cli_override, _active_backend
    _available_backends = {}
    _cli_override = None
    _active_backend = None
    _invalidate_expression_caches()   # Add this
```

### Why Not Option A (Expression Conversion)?

Teammate A's expression-conversion approach in the CVC5 adapter would work but has significant
drawbacks:

1. **Performance**: Recursive tree traversal on every `solver.add()` call
2. **Correctness risk**: Must handle ALL Z3 expression kinds (100+)
3. **Function declarations**: Uninterpreted functions (`verify`, `falsify`, `possible`) need
   context-level re-registration, not just expression conversion
4. **Quantifier variables**: Bound variable identity must be preserved during conversion
5. **Ongoing maintenance**: Every new expression type added to operators needs converter support

The initialization-ordering approach avoids these issues entirely because expressions are always
created in the correct backend from the start.

---

## Evidence and Examples

### The Fix Works

Verified in Python REPL:
```python
from model_checker.solver.registry import set_cli_backend, reset_registry
from model_checker import z3_shim
from model_checker.syntactic.atoms import reset_atom_sort

# Full backend switch
reset_registry()
set_cli_backend('cvc5')
z3_shim._reset_backend()
reset_atom_sort()

# Result: CVC5 types throughout
sem = LogosSemantics({'N': 4, 'solver': 'cvc5'})
# sem.verify is cvc5.pythonic.cvc5_pythonic.FuncDeclRef
# sem.main_world is cvc5.pythonic.cvc5_pythonic.BitVecRef
```

### Test Infrastructure Already Does This

The existing `test_solver_comparison.py` fixture proves the approach works:
```python
def switch_solver(backend: str) -> None:
    clear_cli_backend()
    reset_registry()
    z3_shim._reset_backend()   # <-- the critical missing step in production
    set_cli_backend(backend)
```

Production code paths simply need to call `z3_shim._reset_backend()` at the right time.

### ForAll/Exists are Backend-Agnostic

The quantifier expansion in `utils/z3_helpers.py` uses only `solver/expressions.py` functions
(`BitVecVal`, `And`, `Or`, `substitute`), not `z3_shim` directly. Since `solver/expressions.py`
delegates to the active backend, ForAll/Exists already work correctly with any backend.

---

## Extensibility for Future Solvers

The initialization-ordering approach scales cleanly:

- Adding Bitwuzla or Yices support requires:
  1. Register detection function in `registry.py`
  2. Create an adapter class conforming to `TrackedSolverProtocol`
  3. Implement a pythonic wrapper or update `z3_shim` to delegate to the new backend

No changes to semantics layers or operator implementations are needed.

The pySMT intermediate-representation approach would be more robust for solvers that do NOT
offer a Z3-compatible pythonic API, but given that cvc5.pythonic explicitly provides Z3
compatibility, it is over-engineering for this project's current needs.

---

## Testing Strategy

1. **Unit test**: Verify `set_cli_backend()` automatically invalidates z3_shim and atom sort caches
2. **Integration test**: Run all subtheory examples with both backends and compare results
3. **Regression test**: Ensure Z3 backend still works after backend switching
4. **Type-check test**: Assert that all created expressions are of the correct backend type

The `test_solver_comparison.py` file already has most of this infrastructure; it just needs to
verify that production code (not just tests) correctly initializes the backend.

---

## Confidence Level

**HIGH** - Based on:
- Direct Python REPL verification that CVC5 types are created correctly when caches are reset
- Code reading of `z3_shim._reset_backend()` and `reset_atom_sort()` confirming the mechanism
- Review of existing test infrastructure that successfully uses this exact approach
- API documentation confirming cvc5.pythonic is an intentional Z3 drop-in
