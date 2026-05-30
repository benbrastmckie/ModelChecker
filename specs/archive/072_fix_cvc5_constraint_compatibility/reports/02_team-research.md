# Research Report: Task #72 - Fix CVC5 Constraint Compatibility

**Task**: Fix CVC5 constraint compatibility with Z3 expression types
**Date**: 2026-03-31
**Mode**: Team Research (2 teammates)

## Summary

Two parallel research angles produced a key insight: **the root cause is simpler than initially assumed**. The first research round (01) diagnosed the problem as Z3 expression types being incompatible with CVC5 and recommended expression reconstruction. This team research discovered that `cvc5.pythonic` is an intentional Z3 drop-in replacement -- the real issue is a **cache invalidation bug** preventing proper backend switching.

Two approaches were validated experimentally:
1. **Fix initialization ordering** (Teammate B) - Invalidate caches when backend changes so cvc5.pythonic types are used from the start
2. **SMT-LIB interchange bridge** (Teammate A) - Convert Z3 expressions to SMT-LIB2 text and parse with CVC5's low-level API

The synthesis recommends **approach 1 (initialization fix) as primary** with approach 2 as a defensive fallback for edge cases.

## Key Findings

### Primary Approach: Fix Initialization Ordering (from Teammate B)

The `cvc5.pythonic` module is designed as a Z3 drop-in replacement with identical function signatures (`BitVec`, `And`, `Or`, `Function`, `ForAll`, etc.). The `z3_shim.py` module was built to exploit this -- it delegates to whichever backend is active.

**Root cause**: Three caches prevent proper backend switching:

| Location | Reset Function | Called During Backend Switch? |
|----------|---------------|-------------------------------|
| `z3_shim._backend_module` | `z3_shim._reset_backend()` | **NO** |
| `syntactic/atoms._atom_sort` | `reset_atom_sort()` | **NO** |
| `solver/registry._available_backends` | `reset_registry()` | YES (in tests only) |

When the solver backend changes to `cvc5`, the shim still returns Z3 types from its stale cache. The semantics layer then builds Z3 expressions that CVC5's solver correctly rejects.

**Fix verified in Python REPL**: After calling `_reset_backend()` and `reset_atom_sort()`, `LogosSemantics` correctly creates cvc5.pythonic types. The existing test infrastructure (`test_solver_comparison.py`) already does this in its `switch_solver` fixture.

**Implementation** (3 files, ~15 lines changed):
1. `solver/registry.py`: Add `_invalidate_expression_caches()` called from `set_cli_backend()`
2. `builder/example.py`: Set backend from settings before expression construction
3. `solver/registry.py`: Update `reset_registry()` to also invalidate expression caches

**Advantages**: No runtime overhead, minimal code changes, expressions are always native types.

### Alternative Approach: SMT-LIB Interchange Bridge (from Teammate A)

A fully working `SmtLibBridgeAdapter` was prototyped and experimentally validated. It intercepts Z3 expressions in `CVC5SolverAdapter.add()`, converts them via `z3.Solver.to_smt2()`, and feeds the SMT-LIB2 text to CVC5's low-level `InputParser` with a shared `SymbolManager`.

**Critical implementation details discovered**:
- `z3.Solver.to_smt2()` produces complete, valid SMT-LIB2 with all declarations
- `cvc5.InputParser` + shared `SymbolManager` enables incremental parsing
- Symbol redeclaration must be filtered (causes `RuntimeError` with let-bound expressions)
- Logic `ALL` handles the project's mix of bitvectors, uninterpreted sorts, and quantifiers
- `set-logic` can only be issued once per `SymbolManager`

**Performance**: ~4.7ms per constraint vs 0.35ms for Z3 native (13x overhead). Acceptable for model checking where solve time dominates.

**Advantages**: Works regardless of how expressions are created, standard interchange format.

### Risks and Edge Cases

| Risk | Impact | Mitigation |
|------|--------|------------|
| Undiscovered caches beyond the 3 identified | Medium | SMT-LIB fallback if types leak |
| push/pop interaction with declaration accumulation | Low | Declarations don't pop (correct SMT-LIB2 behavior) |
| Unsat core string matching across solvers | Medium | Track constraint labels separately |
| Third-party code creating Z3 types directly | Low | Audit imports, add type assertions |

## Synthesis

### Conflict Resolved: Initialization Fix vs SMT-LIB Bridge

The teammates recommend different primary approaches. Resolution:

**Initialization fix is the correct primary approach** because:
1. It addresses the root cause rather than the symptom
2. Zero runtime overhead (no conversion, no serialization)
3. 3 files / ~15 lines changed vs a new adapter class
4. The cvc5.pythonic API was specifically designed for this use case
5. Test infrastructure already validates this pattern works

**SMT-LIB bridge is the correct defensive fallback** because:
1. If any Z3 types leak through undiscovered caches, the bridge catches them
2. It provides a clean migration path if a future solver lacks a pythonic API
3. The prototype is fully working and experimentally validated

### Recommended Architecture

```
                     Settings (solver='cvc5')
                              |
                    [1] set_cli_backend('cvc5')
                              |
                    [2] _invalidate_expression_caches()
                              |
              +---------------+---------------+
              |                               |
    z3_shim._reset_backend()      reset_atom_sort()
              |                               |
    [3] All subsequent z3_shim       AtomSort now
    calls return cvc5.pythonic       cvc5.pythonic type
              |                               |
              +---------------+---------------+
                              |
                    Semantics layer builds
                    cvc5.pythonic expressions
                              |
                    CVC5SolverAdapter receives
                    native cvc5 types (no conversion)
```

**Optional defensive layer** (Phase 2):
```python
# In CVC5SolverAdapter.add():
def add(self, constraint):
    if self._is_z3_expr(constraint):
        # Fallback: convert via SMT-LIB bridge
        batch = self._z3_to_smt2_batch(constraint)
        self._parse_and_add(batch)
    else:
        self._solver.add(constraint)  # Happy path: native cvc5
```

### Gaps Identified

1. **Unsat core compatibility**: Neither teammate fully addressed how unsat core extraction works when using CVC5. Need to verify `CVC5SolverAdapter.get_unsat_core()` returns labels compatible with the constraint tracking system.
2. **Model extraction**: The model display system extracts values from solver models. Need to verify CVC5 model extraction produces compatible results for the output formatting pipeline.
3. **Operator compatibility**: While cvc5.pythonic mirrors Z3's API, some operators in the subtheory files may use Z3-specific methods not in cvc5.pythonic. A systematic audit of operator files is needed.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | SMT-LIB Interchange Architecture | completed | HIGH |
| B | Alternative Approaches / Prior Art | completed | HIGH |

### Teammate A Key Contribution
- Experimentally validated the full SMT-LIB interchange pipeline
- Discovered the critical redeclaration filtering requirement
- Provided working `SmtLibBridgeAdapter` prototype with performance benchmarks
- Identified that cvc5 low-level API (not pythonic) is needed for SMT-LIB parsing

### Teammate B Key Contribution
- Identified the true root cause: cache invalidation, not type incompatibility
- Mapped all 3 cache locations requiring invalidation
- Verified the fix works via Python REPL
- Showed test infrastructure already validates this approach
- Demonstrated cvc5.pythonic is an intentional Z3 drop-in

## Recommendations

### Revised Implementation Plan

The original plan (01_cvc5-expression-conversion.md) should be revised to reflect the simpler approach:

**Phase 1: Fix Cache Invalidation** (primary fix, ~1 hour)
- Add `_invalidate_expression_caches()` to `solver/registry.py`
- Call from `set_cli_backend()` and `reset_registry()`
- Set backend early in `builder/example.py` before expression construction

**Phase 2: Verify Core Functionality** (~1 hour)
- Run counterfactual examples with CVC5 and verify results match Z3
- Test push/pop, unsat core extraction, and model display
- Audit operator files for Z3-specific methods

**Phase 3: Add Defensive SMT-LIB Fallback** (optional, ~2 hours)
- Implement `SmtLibBridgeAdapter` based on Teammate A's prototype
- Add Z3 type detection in `CVC5SolverAdapter.add()`
- Use as fallback if native types not detected

**Phase 4: Test Suite and Documentation** (~1 hour)
- Add backend-switching integration tests
- Test all subtheory examples with both solvers
- Document the multi-solver architecture

**Total estimated effort**: 3-5 hours (down from 6 in original plan)

## References

- [cvc5 Parser with Shared Symbol Manager](https://cvc5.github.io/docs/cvc5-1.1.1/examples/parser_sym_manager.html)
- [cvc5 Parser Example (Python)](https://cvc5.github.io/docs/cvc5-1.1.1/examples/parser.html)
- [SMTMSMT: Gluing Together CVC5 and Z3 Nelson Oppen Style](https://www.philipzucker.com/glue-cvc5-z3/)
- [cvc5: A Versatile and Industrial-Strength SMT Solver (TACAS 2022)](https://link.springer.com/chapter/10.1007/978-3-030-99524-9_24)
- [cvc5_pythonic_api GitHub - Z3Py-compatible interface](https://github.com/cvc5/cvc5_pythonic_api)
