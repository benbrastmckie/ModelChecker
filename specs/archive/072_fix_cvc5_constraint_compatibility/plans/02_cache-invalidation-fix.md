# Implementation Plan: Task #72

- **Task**: 72 - Fix CVC5 constraint compatibility with Z3 expression types
- **Status**: [NOT STARTED]
- **Effort**: 3-4 hours
- **Dependencies**: None
- **Research Inputs**: reports/02_team-research.md
- **Artifacts**: plans/02_cache-invalidation-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: true

## Overview

The team research (reports/02_team-research.md) discovered that the CVC5 compatibility issue is **NOT** a type conversion problem requiring expression reconstruction. The root cause is a **cache invalidation bug** in three locations that prevents proper backend switching. When `cvc5.pythonic` (an intentional Z3 drop-in replacement) is selected, stale caches cause Z3 types to be used instead of native CVC5 types. The fix is minimal: invalidate caches when the backend changes so expressions are built with native types from the start.

### Research Integration

Key findings from team research (02_team-research.md) that supersede the original plan:
- `cvc5.pythonic` is designed as a Z3 drop-in with identical function signatures
- Three caches prevent proper backend switching: `z3_shim._backend_module`, `syntactic/atoms._atom_sort`, `solver/registry._available_backends`
- Verified in Python REPL: After calling `_reset_backend()` and `reset_atom_sort()`, expressions correctly use cvc5.pythonic types
- Test infrastructure (`test_solver_comparison.py`) already validates this pattern works

## Goals & Non-Goals

**Goals**:
- Invalidate expression caches when solver backend changes
- Ensure backend is set before any expression construction in example.py
- Run counterfactual examples with CVC5 and verify correct behavior
- Optional: Add defensive SMT-LIB fallback for edge cases

**Non-Goals**:
- Expression reconstruction/conversion (not needed - wrong diagnosis)
- Modifying cvc5.pythonic or z3 APIs
- Performance optimization (cache invalidation is O(1), happens once per backend switch)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Undiscovered caches beyond the 3 identified | Medium | Low | SMT-LIB fallback catches any leaked Z3 types |
| Import order dependencies | Medium | Low | Test with fresh Python interpreter |
| Unsat core compatibility between solvers | Medium | Medium | Test unsat core extraction explicitly |
| Third-party code creating Z3 types directly | Low | Low | Audit imports, existing code uses z3_shim |

## Implementation Phases

### Phase 1: Add Cache Invalidation to Registry [NOT STARTED]

**Goal**: Create `_invalidate_expression_caches()` function and call it when backend changes.

**Tasks**:
- [ ] Add `_invalidate_expression_caches()` function to `solver/registry.py`
  - Import and call `z3_shim._reset_backend()`
  - Import and call `syntactic.atoms.reset_atom_sort()`
- [ ] Call `_invalidate_expression_caches()` from `set_cli_backend()` after setting `_cli_override`
- [ ] Call `_invalidate_expression_caches()` from `reset_registry()` for test compatibility
- [ ] Add docstrings explaining the cache invalidation requirement

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/solver/registry.py` - Add invalidation function and calls (~15 lines)

**Code Change**:
```python
def _invalidate_expression_caches() -> None:
    """Invalidate expression caches when backend changes.

    Three caches hold backend-specific types that must be reset:
    - z3_shim._backend_module: Cached module (z3 or cvc5.pythonic)
    - syntactic.atoms._atom_sort: Cached AtomSort declaration
    - registry._available_backends: Reset by reset_registry() already
    """
    from model_checker.z3_shim import _reset_backend
    from model_checker.syntactic.atoms import reset_atom_sort
    _reset_backend()
    reset_atom_sort()

def set_cli_backend(backend: str) -> None:
    """Set the solver backend from CLI flag."""
    global _cli_override
    if backend not in ("z3", "cvc5"):
        raise ValueError(f"Unknown solver backend: {backend}")
    _cli_override = backend
    _invalidate_expression_caches()  # NEW: Clear stale types
```

**Verification**:
- Unit test: `set_cli_backend("cvc5")` followed by `z3_shim.BitVec("x", 8)` returns cvc5.pythonic type
- `reset_registry()` also clears expression caches

---

### Phase 2: Set Backend Early in Example Construction [NOT STARTED]

**Goal**: Ensure backend is set from settings before any expression construction.

**Tasks**:
- [ ] In `BuildExample.__init__`, check settings for `solver` key early
- [ ] If `solver` is set in settings and differs from current, call `set_cli_backend()`
- [ ] This must happen BEFORE `_initialize_z3_context()` which accesses z3_shim

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/builder/example.py` - Add early backend initialization (~10 lines)

**Code Change** (in `BuildExample.__init__`):
```python
def __init__(
    self,
    build_module: 'BuildModule',
    semantic_theory: Dict[str, Any],
    example_case: List[Any],
    theory_name: Optional[str] = None
) -> None:
    # Set backend from settings BEFORE any expression construction
    self._configure_solver_backend(example_case)

    # Initialize Z3 context and store module reference
    self._initialize_z3_context()
    # ... rest unchanged

def _configure_solver_backend(self, example_case: List[Any]) -> None:
    """Configure solver backend from example settings before expression construction."""
    from model_checker.solver.registry import set_cli_backend, get_active_backend

    # example_case is [premises, conclusions, settings]
    if len(example_case) >= 3 and isinstance(example_case[2], dict):
        settings = example_case[2]
        requested_solver = settings.get("solver")
        if requested_solver and requested_solver in ("z3", "cvc5"):
            current = get_active_backend()
            if current != requested_solver:
                set_cli_backend(requested_solver)
```

**Verification**:
- Example with `settings={"solver": "cvc5"}` uses cvc5.pythonic types throughout
- Example without solver setting uses default (z3)

---

### Phase 3: Verify Core Functionality with CVC5 [NOT STARTED]

**Goal**: Run counterfactual examples with CVC5 and verify results match Z3.

**Tasks**:
- [ ] Run existing counterfactual examples with `--cvc5` flag
- [ ] Verify example results match Z3 (sat/unsat, model values)
- [ ] Test push/pop behavior with CVC5
- [ ] Test unsat core extraction with CVC5
- [ ] Audit operator files for Z3-specific methods not in cvc5.pythonic

**Timing**: 1 hour

**Files to test**:
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py`
- `code/src/model_checker/solver/tests/unit/test_solver_comparison.py`

**Verification**:
- All counterfactual examples pass with CVC5
- No SMTException about "True, False or SMT Boolean expression expected"
- Model values are consistent between solvers

---

### Phase 4: Add Defensive SMT-LIB Fallback (Optional) [NOT STARTED]

**Goal**: Add type detection and SMT-LIB conversion fallback in CVC5 adapter for robustness.

**Tasks**:
- [ ] Add `_is_z3_expr()` helper to detect Z3 expression types
- [ ] If Z3 types leak through, convert via SMT-LIB2 text interchange
- [ ] Use `z3.Solver().to_smt2()` and `cvc5.InputParser` with shared `SymbolManager`
- [ ] Log a warning when fallback is used (indicates undiscovered cache)

**Timing**: 2 hours (optional, only if Phase 3 reveals issues)

**Files to modify**:
- `code/src/model_checker/solver/cvc5_adapter.py` - Add fallback conversion

**Decision Point**: This phase should only be implemented if Phase 3 testing reveals Z3 types still leaking through after cache invalidation. The team research showed the primary fix (Phases 1-2) should be sufficient.

**Verification**:
- If implemented, warning is logged when Z3 types are converted
- Conversion produces equivalent results

---

## Testing & Validation

- [ ] Unit tests for cache invalidation in registry.py
- [ ] Unit tests for early backend configuration in example.py
- [ ] Integration test: counterfactual examples with CVC5 match Z3 results
- [ ] Run `test_solver_comparison.py` with CVC5 enabled
- [ ] Verify no SMTException with CVC5 on examples that previously crashed
- [ ] Test that switching solvers mid-session works correctly

## Artifacts & Outputs

- `code/src/model_checker/solver/registry.py` - Cache invalidation function (~15 lines)
- `code/src/model_checker/builder/example.py` - Early backend configuration (~10 lines)
- `specs/072_fix_cvc5_constraint_compatibility/summaries/02_cache-invalidation-summary.md` - Execution summary

## Rollback/Contingency

If cache invalidation proves insufficient (unlikely based on research):
1. Revert changes to registry.py and example.py
2. Implement Phase 4 (SMT-LIB fallback) as primary approach
3. Fall back to original plan (01_cvc5-expression-conversion.md) as last resort

The team research validated that cache invalidation works in the Python REPL, so this contingency is unlikely to be needed.

## Comparison to Original Plan

| Aspect | Original Plan (01) | Revised Plan (02) |
|--------|-------------------|-------------------|
| Root cause | Type incompatibility | Cache invalidation |
| Approach | Expression reconstruction | Clear caches on switch |
| Code changes | ~200+ lines | ~25 lines |
| Phases | 4 (all required) | 3 required + 1 optional |
| Effort | 6 hours | 3-4 hours |
| Runtime overhead | O(n) per constraint | O(1) per backend switch |
| Risk | Complex edge cases | Minimal (uses designed API) |
