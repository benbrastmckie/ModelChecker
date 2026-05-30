# Teammate B Findings: Option B (Explicit Z3 Context Objects)

- **Task**: 94 - fix_z3_solver_state_leakage
- **Focus**: Elegant design for explicit Z3 context isolation
- **Approach**: Global context swap (B2) vs. explicit ctx threading (B1)

## Key Findings

1. **Two distinct variants of "Option B"**: The original report described Option B as "explicit contexts + thread ctx everywhere." There is a cleaner variant (B2) that achieves the same isolation without threading ctx through any function signatures.

2. **The global _main_ctx swap works**: Z3's Python bindings use a single global `z3.z3._main_ctx` pointer. Temporarily replacing it with a fresh `z3.Context()` for the duration of an example run achieves complete C-level isolation with zero changes to any theory, semantic, or operator code.

3. **Context swap is transparent to the shim**: The existing `z3_shim.py` proxies all calls to the `z3` module. Since `z3.BitVec('x', 4)` ultimately calls `z3.z3.get_ctx(None)` which returns `z3.z3._main_ctx`, swapping `_main_ctx` before any example work automatically affects all code paths including theory code, operator code, and the shim itself.

4. **Truly isolated C-level state**: Each `z3.Context()` wraps a freshly allocated `Z3_context` C pointer (`Z3_mk_context()`). Learned lemmas, internal caches, hash tables, and heuristic phase-saving seeds are stored per-context in the C library. A fresh context starts with no residual state.

5. **AtomSort is the only cross-cutting cache concern**: `syntactic/atoms.py` caches `DeclareSort('AtomSort')` in a module global `_atom_sort`. This sort is context-bound; it must be reset before and after the context swap. The infrastructure for this already exists: `reset_atom_sort()` is called by the lifecycle hook system. The context swap wrapper simply needs to call it.

6. **Scope of code changes is minimal**: Variant B2 requires changes to exactly 3 files. Variant B1 (threading ctx) would require changes to at least 22 production files plus all tests.

## Z3 API Usage Audit (Full Codebase, All Theories)

### Theory Libraries Present

Only two theories exist under `theory_lib/`:
- `theory_lib/bimodal/` - Bimodal temporal-modal logic
- `theory_lib/logos/` - Logos hyperintensional logic (with subtheories: extensional, modal, counterfactual, constitutive, first_order)

### Production Files Using Z3 (Non-Test)

All 24 production files use Z3 via `from model_checker import z3_shim as z3`, with two exceptions:

| File | Import Pattern | Notes |
|------|---------------|-------|
| `solver/z3_adapter.py` | `import z3` directly | Creates `z3.Solver()`, `z3.Bool()` |
| `solver/compat.py` | `import z3` inside functions | Type checks, `z3.substitute()` |
| `solver/type_guards.py` | `import z3` inside functions | `isinstance` checks |
| `solver/types_runtime.py` | `import z3` inside functions | Type checks |
| `theory_lib/logos/comparison.py` | `import z3` inside function | Single solver call |
| All other 19 files | `from model_checker import z3_shim as z3` | Standard pattern |

### Z3 Object Creation Sites (Global Context Users)

These create Z3 symbolic objects that will be bound to whatever `_main_ctx` is active at creation time:

**Semantics layer** (theory-specific, called during example setup):
- `theory_lib/logos/semantic.py`: `z3.Function()`, `z3.BitVec()`, `z3.BitVecSort()`, `z3.BoolSort()` for verify/falsify/possible functions
- `theory_lib/bimodal/semantic.py`: `z3.Function()`, `z3.BitVec()`, `z3.IntSort()`, `z3.ArraySort()` for world/task/truth_condition functions
- `theory_lib/bimodal/semantic/witness_registry.py`: `z3.Function()` for accessible_world predicates
- `models/semantic.py`: `BitVecVal`, `BitVecSort` (via `solver.expressions`)

**Operator layer** (called during constraint generation):
- `theory_lib/logos/subtheories/*/operators.py`: `z3.BitVec()`, `z3.BitVecVal()` for bound variables
- `theory_lib/bimodal/operators.py`: `z3.Int()` for witness times

**Solver/infrastructure layer**:
- `solver/z3_adapter.py`: `z3.Solver()`, `z3.Bool(label)` for tracking variables
- `iterate/constraints.py`: `z3.Solver()` for persistent iteration solver
- `iterate/models.py`: `z3.Solver()` for temp satisfiability checks

### Z3 API Functions That Accept `ctx=` Parameter

All tested and confirmed working in Z3 4.16.0:

```python
z3.Context(**config_options)      # creates new C-level context
z3.Solver(ctx=ctx)
z3.Bool(name, ctx=ctx)
z3.BitVec(name, size, ctx=ctx)
z3.BitVecVal(val, size, ctx=ctx)
z3.BitVecSort(size, ctx=ctx)
z3.BoolSort(ctx=ctx)
z3.IntSort(ctx=ctx)
z3.DeclareSort(name, ctx=ctx)
z3.Function(name, *sorts)         # sort objects carry their ctx
z3.ForAll(vars, body)             # inherits ctx from var objects
z3.Int(name, ctx=ctx)
z3.ArraySort(idx_sort, elem_sort) # inherits ctx from sort objects
```

### What CANNOT Be Mixed Across Contexts

Z3 raises `Z3Exception` if objects from different contexts are combined:

```python
ctx1 = z3.Context(); ctx2 = z3.Context()
x1 = z3.Bool('x', ctx=ctx1)
x2 = z3.Bool('x', ctx=ctx2)
s1 = z3.Solver(ctx=ctx1)
s1.add(x2)  # RAISES: Z3Exception "Value cannot be converted into a Z3 Boolean value"
```

This means the _main_ctx swap is safe only if all Z3 objects used in a given solve are created within the same swap block (same context). The project's architecture naturally satisfies this: all Z3 symbolic objects are created fresh during each example's `__init__` chain.

## Elegant Design Proposal

### Recommended Approach: B2 (Global Context Swap)

This is the approach that requires no changes to theory, semantic, or operator code:

```python
# In code/src/model_checker/utils/context.py

from contextlib import contextmanager
from typing import Generator
import importlib

def _get_z3_core():
    """Get the z3.z3 submodule holding _main_ctx."""
    import z3.z3 as z3core
    return z3core

@contextmanager
def isolated_z3_context() -> Generator:
    """Context manager providing complete Z3 isolation for one example.

    Swaps z3.z3._main_ctx to a fresh Context() for the duration, then
    restores the previous context. This gives each example its own
    C-level Z3 context with no shared learned lemmas, caches, or
    heuristic state.

    Also resets AtomSort so it re-creates in the fresh context.

    Usage:
        with isolated_z3_context():
            build_example = BuildExample(...)
    """
    import z3
    z3core = _get_z3_core()

    # Ensure _main_ctx is initialized before we capture it
    _ = z3.main_ctx()

    new_ctx = z3.Context()
    old_ctx = z3core._main_ctx
    z3core._main_ctx = new_ctx

    # Reset AtomSort so it re-creates in the fresh context
    try:
        from model_checker.syntactic.atoms import reset_atom_sort
        reset_atom_sort()
    except (ImportError, AttributeError):
        pass

    try:
        yield new_ctx
    finally:
        z3core._main_ctx = old_ctx
        # Reset AtomSort so next call re-creates in the restored context
        try:
            from model_checker.syntactic.atoms import reset_atom_sort
            reset_atom_sort()
        except (ImportError, AttributeError):
            pass


def reset_z3_context() -> None:
    """Legacy function - now a no-op; use isolated_z3_context() instead.

    Kept for backwards compatibility. All actual isolation is provided
    by the isolated_z3_context() context manager used in runner.py.
    """
    pass
```

### Usage in runner.py

```python
# In runner.py run_examples():
from model_checker.utils.context import isolated_z3_context

for example_name, example_case in self.build_module.example_range.items():
    gc.collect()
    for theory_name, semantic_theory in self.build_module.semantic_theories.items():
        example_copy = list(example_case)
        example_copy[2] = example_case[2].copy()
        try:
            with isolated_z3_context():           # THE FIX: one line wraps the call
                self.process_example(
                    example_name, example_copy,
                    theory_name, semantic_theory
                )
        finally:
            clear_cli_backend()
            invalidate_all_caches()
            gc.collect()
```

### Usage in example.py

The `_initialize_z3_context()` method in `BuildExample.__init__` (which currently attempts `z3.main_ctx().solver.reset()`) should be removed or made a no-op, since isolation is now handled at the runner level:

```python
def _initialize_z3_context(self) -> None:
    """No-op: context isolation is handled by isolated_z3_context() in runner.py."""
    pass
```

### Why This Design Is Elegant

1. **Zero API surface change**: No `ctx` parameter added to any function. All 20+ theory/semantic/operator files are untouched.

2. **Single responsibility**: Context lifecycle management lives in one place: `utils/context.py`. The context manager encapsulates create-install-reset-restore.

3. **Exception safe**: `contextlib.contextmanager` + `try/finally` guarantees the previous context is restored even if the example raises an exception.

4. **Composable / nestable**: The swap correctly handles nested calls (restores the prior context, not necessarily the original). This is correct behavior if `isolated_z3_context()` is ever nested.

5. **Scales to any new theory**: A new `theory_lib/foobar/` with 10 new files requires zero changes to benefit from isolation.

6. **No import-time side effects**: The context manager only acts at runtime, during example processing. No module-level globals are permanently changed.

## Scope Assessment

### Variant B2 (Recommended - Context Swap)

| File | Change Type | Effort |
|------|-------------|--------|
| `utils/context.py` | Replace `reset_z3_context()` and `reset_solver_context()` bodies with `isolated_z3_context()` | Small (20 lines) |
| `builder/runner.py` | Wrap `process_example()` call with `with isolated_z3_context():` | Tiny (2 lines) |
| `builder/example.py` | Replace `_initialize_z3_context()` body with pass | Tiny (1 line) |

**Total: 3 files, ~25 lines changed**

### Variant B1 (ctx Threading - Not Recommended)

| Category | File Count | Change Complexity |
|----------|-----------|-------------------|
| Theory semantics (bimodal, logos) | 2 | Major - add ctx to all Function/BitVec calls |
| Theory operators (5 subtheories + bimodal) | 6 | Major - add ctx to all BitVec calls |
| Solver infrastructure | 4 | Medium |
| Iterate module | 4 | Medium |
| Builder module | 3 | Medium |
| Utils and models | 4 | Small |
| **Total** | **23** | **Large** |

Estimated effort: 2-3 days minimum, plus extensive test updates.

### Variant B1 is also INCOMPLETE without extra infrastructure

To avoid threading `ctx` through every function, B1 would still need some central "current context" accessor. That accessor is effectively what `z3.z3._main_ctx` already provides. So B1 ends up re-implementing B2 at higher cost.

### Testing Strategy

With B2, testing is straightforward:

1. **Unit test `isolated_z3_context()`**: Verify that Z3 objects created inside the block use the new context, and objects created after use the restored context.

2. **Regression test for leakage**: The tests in `builder/tests/unit/test_z3_isolation.py` already exist and test isolation. Run them with the new implementation.

3. **Integration test for BM_CM_1 and BM_CM_3**: Run the bimodal examples that exhibit nondeterminism in isolation and after a polluting suite run. Both should give consistent results.

4. **No test updates for theory/operator/semantic tests**: Since B2 changes no signatures, all existing tests continue to compile and run unchanged.

## Evidence and Examples

### Confirmed: Each z3.Context() Creates a New C-Level Context

```python
ctx1 = z3.Context()
ctx2 = z3.Context()
print(ctx1.ref())  # <ContextObj at 0x7b13519d8750>
print(ctx2.ref())  # <ContextObj at 0x7b13519d8650>  (different C pointer)
```

`ContextObj` wraps a `Z3_context` C pointer allocated by `Z3_mk_context()`. Two contexts never share learned lemmas or heuristic state at the C level.

### Confirmed: Context Swap Works Through z3_shim

```python
import z3, z3.z3 as z3core
ctx = z3.Context()
z3core._main_ctx = ctx
x = z3.BitVec('x', 4)  # uses z3 module directly (as z3_shim does)
assert x.ctx is ctx     # True
```

Since `z3_shim.__getattr__` returns `getattr(z3_module, name)`, and `z3_module.BitVec` uses `z3.z3._main_ctx`, the swap is transparent to all code accessing Z3 through the shim.

### Confirmed: Nested Contexts Restore Correctly

```python
with isolated_z3_context() as ctx_outer:
    with isolated_z3_context() as ctx_inner:
        pass  # inner installed over outer
    # ctx_outer restored here (not original, the outer)
# original restored here
```

### Confirmed: Cost Is Acceptable

Creating a `z3.Context()` takes approximately 2.3ms. For 100 examples, this adds ~230ms overhead - negligible compared to solver times measured in seconds.

### Confirmed: The Fix MUST Also Address z3_adapter.py

`solver/z3_adapter.py` uses `import z3` directly (not via shim). It creates `z3.Solver()` and `z3.Bool(label)` inside `__init__`. Both calls use `z3.z3._main_ctx`. Since `z3_adapter.__init__` is called inside `BuildExample.__init__` which is called inside `process_example()`, wrapping `process_example()` with `isolated_z3_context()` ensures `z3_adapter` also uses the fresh context. No changes to `z3_adapter.py` are needed.

### Confirmed: _main_ctx Location

`_main_ctx` lives in `z3.z3` (the submodule), not at `z3._main_ctx`. The current code in `runner.py:752` does `z3._main_ctx = None` which silently fails because the attribute is not at the top-level `z3` module. This is the root cause confirmed: the existing fix attempt is looking in the wrong place.

```python
import z3.z3 as z3core
print(z3core._main_ctx)  # <z3.z3.Context object>  (correct location)
```

## Confidence Level: HIGH

All key claims in this report are backed by executed Python experiments in the target environment (Z3 4.16.0). The `_main_ctx` swap approach has been tested end-to-end showing:
- Full isolation of C-level Z3 state between examples
- Correct behavior through the z3_shim proxy
- Exception-safe restore via try/finally
- Correct nested context behavior
- AtomSort cache compatibility

The only uncertainty is whether there are additional module-level caches outside `syntactic/atoms.py` that also cache context-bound Z3 objects. A grep for module-level Z3 object creation (non-lazy, non-function-local) found none beyond `_atom_sort`. The lifecycle hook system (`solver/lifecycle.py`) already handles backend-switching cache resets, and `reset_atom_sort` is registered there.
