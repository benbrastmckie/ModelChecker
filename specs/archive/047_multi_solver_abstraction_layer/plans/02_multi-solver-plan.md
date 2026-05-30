# Implementation Plan: Multi-Solver Abstraction Layer

- **Task**: 47 - Implement multi-solver abstraction layer for z3, cvc5, and future constraint solvers
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Dependencies**: None
- **Research Inputs**: specs/047_multi_solver_abstraction_layer/reports/01_team-research.md
- **Artifacts**: plans/02_multi-solver-plan.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/context/formats/plan-format.md
- **Type**: z3
- **Lean Intent**: false

## Overview

This plan implements a thin protocol-based solver abstraction layer that enables ModelChecker to use Z3, cvc5, or other SMT solvers interchangeably. The architecture leverages cvc5's Pythonic API which deliberately mirrors Z3's Python API, meaning formula construction code (30+ operator files) needs only import path changes. The actual translation code is concentrated in 4-6 divergent solver control methods in 2-3 files.

### Research Integration

Key findings from the team research report (01_team-research.md):
- cvc5.pythonic provides Z3-compatible API for all formula construction functions
- Only 4-6 solver control methods differ between solvers (assert_and_track, unsat_core, timeout, etc.)
- Existing multi-solver libraries (pySMT, smt-switch, pysmtlib) are unsuitable
- Architecture should use ABC for solver control interface, module-level aliasing for expressions

## Goals & Non-Goals

**Goals**:
- Create `model_checker/solver/` package with clean abstraction boundaries
- Enable solver selection via settings default with `--z3` and `--cvc5` CLI flag overrides
- Maintain behavior-identical Z3 path (zero regression risk)
- Support cvc5 as an alternative solver backend
- Establish architecture for future solver additions (Bitwuzla, Yices2)

**Non-Goals**:
- No theory operator rewrites needed
- No SemanticDefaults set operation rewrites
- No z3_helpers.py ForAll/Exists rewrites
- No new formula representation language
- Bitwuzla/Yices2 implementation deferred to future tasks

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| cvc5.pythonic API gaps | High | Low | Verify API coverage before phase 3; document gaps |
| Import cycle during transition | Medium | Medium | Use lazy imports and runtime binding |
| Performance regression | Medium | Low | Benchmark Z3 path before/after; ensure zero-overhead passthrough |
| Missing assert_and_track in cvc5 | Medium | High | Implement manual tracking shim in cvc5 adapter |

## Implementation Phases

### Phase 1: Create Solver Package Structure [NOT STARTED]

**Goal**: Establish the solver abstraction package with Z3 passthrough

**Tasks**:
- [ ] Create `code/src/model_checker/solver/__init__.py` with package exports
- [ ] Create `code/src/model_checker/solver/interface.py` with ABC defining solver control interface:
  - `AbstractSolver` ABC with methods: `add`, `check`, `model`, `push`, `pop`, `set_timeout`
  - `AbstractSolverAdapter` ABC for solver-specific adapters
- [ ] Create `code/src/model_checker/solver/expressions.py` that re-exports all formula construction functions from Z3 (initial passthrough)
- [ ] Create `code/src/model_checker/solver/z3_adapter.py` implementing the interface for Z3 (transparent passthrough)
- [ ] Create `code/src/model_checker/solver/types.py` with solver-agnostic type aliases
- [ ] Create `code/src/model_checker/solver/registry.py` for runtime solver detection and selection

**Timing**: 1.5 hours

**Files to modify**:
- `code/src/model_checker/solver/__init__.py` - new
- `code/src/model_checker/solver/interface.py` - new
- `code/src/model_checker/solver/expressions.py` - new
- `code/src/model_checker/solver/z3_adapter.py` - new
- `code/src/model_checker/solver/types.py` - new
- `code/src/model_checker/solver/registry.py` - new

**Verification**:
- All tests pass with no changes (Z3 passthrough is transparent)
- `from model_checker.solver.expressions import And, Or, Not` works identically to `from z3 import And, Or, Not`

---

### Phase 2: Migrate Import Paths [NOT STARTED]

**Goal**: Change all Z3 imports to use the solver abstraction layer

**Tasks**:
- [ ] Update `syntactic/atoms.py` to import from `model_checker.solver.expressions`
- [ ] Update `models/semantic.py` to import from `model_checker.solver.expressions`
- [ ] Update `models/structure.py` to import from `model_checker.solver.expressions` and use solver interface
- [ ] Update `utils/z3_helpers.py` to import from `model_checker.solver.expressions`
- [ ] Update `iterate/constraints.py` to import from `model_checker.solver.expressions`
- [ ] Update all `theory_lib/*/operators.py` files to import from `model_checker.solver.expressions`
- [ ] Update `theory_lib/logos/semantic.py` and `theory_lib/bimodal/semantic.py`
- [ ] Update remaining files with Z3 imports (74 files identified in research)

**Timing**: 2 hours

**Files to modify**:
- `code/src/model_checker/syntactic/atoms.py`
- `code/src/model_checker/models/semantic.py`
- `code/src/model_checker/models/structure.py`
- `code/src/model_checker/utils/z3_helpers.py`
- `code/src/model_checker/iterate/constraints.py`
- `code/src/model_checker/theory_lib/logos/semantic.py`
- `code/src/model_checker/theory_lib/bimodal/semantic.py`
- `code/src/model_checker/theory_lib/logos/subtheories/*/operators.py` (5 files)
- `code/src/model_checker/theory_lib/bimodal/operators.py`
- Additional files (~60) with Z3 imports

**Verification**:
- All existing tests pass unchanged
- No direct `import z3` or `from z3 import` statements in non-test source files (except solver/)
- Grep verification: `grep -r "from z3 import\|import z3" code/src/model_checker --include="*.py" | grep -v solver/ | grep -v test`

---

### Phase 3: Implement cvc5 Adapter [NOT STARTED]

**Goal**: Create cvc5 solver adapter for the divergent solver control methods

**Tasks**:
- [ ] Create `code/src/model_checker/solver/cvc5_adapter.py` implementing `AbstractSolverAdapter`
- [ ] Implement `assert_and_track` shim (cvc5.pythonic lacks this - use manual constraint tracking)
- [ ] Implement `unsat_core` translation (`solver.getUnsatCore()` in cvc5 base API)
- [ ] Implement timeout setting (`solver.setOption("tlimit-per", str(ms))`)
- [ ] Implement `model.evaluate(expr, True)` wrapper for Z3's `model.eval(expr, model_completion=True)`
- [ ] Implement `is_true`/`is_false` equivalents for cvc5
- [ ] Add cvc5 detection to `registry.py`
- [ ] Update `expressions.py` to support cvc5 backend switching

**Timing**: 2 hours

**Files to modify**:
- `code/src/model_checker/solver/cvc5_adapter.py` - new
- `code/src/model_checker/solver/registry.py` - update with cvc5 detection
- `code/src/model_checker/solver/expressions.py` - update for backend switching

**Verification**:
- cvc5 adapter can be instantiated when cvc5 is installed
- Manual test with simple constraint shows cvc5 solving works
- Graceful fallback when cvc5 not installed

---

### Phase 4: Add Solver Selection Configuration [NOT STARTED]

**Goal**: Enable solver selection via settings and CLI flags

**Tasks**:
- [ ] Add `solver` setting to `DEFAULT_GENERAL_SETTINGS` in `models/semantic.py` (default: "z3")
- [ ] Add `--z3` CLI flag to `__main__.py` that sets solver to "z3"
- [ ] Add `--cvc5` CLI flag to `__main__.py` that sets solver to "cvc5"
- [ ] Update `SettingsManager` to handle solver setting
- [ ] Update `registry.py` to read solver from settings with CLI override priority
- [ ] Implement fallback chain: CLI flag > settings > semantics default > "z3"
- [ ] Add `MODEL_CHECKER_SOLVER` environment variable support as alternative override

**Timing**: 1 hour

**Files to modify**:
- `code/src/model_checker/models/semantic.py` - add solver to DEFAULT_GENERAL_SETTINGS
- `code/src/model_checker/__main__.py` - add --z3 and --cvc5 flags
- `code/src/model_checker/settings/settings.py` - handle solver setting
- `code/src/model_checker/solver/registry.py` - implement selection logic

**Verification**:
- `model-checker --z3 examples.py` uses Z3
- `model-checker --cvc5 examples.py` uses cvc5 (if installed)
- Without flags, uses settings default (z3)
- Error message when requested solver not installed

---

### Phase 5: Integration Testing [NOT STARTED]

**Goal**: Validate solver equivalence across existing theories

**Tasks**:
- [ ] Create `code/src/model_checker/solver/tests/test_adapter_equivalence.py`
- [ ] Test that Z3 and cvc5 produce equivalent results on logos theory examples
- [ ] Test that Z3 and cvc5 produce equivalent results on bimodal theory examples
- [ ] Test unsat_core behavior parity
- [ ] Test timeout behavior parity
- [ ] Add solver backend to test matrix for CI

**Timing**: 1 hour

**Files to modify**:
- `code/src/model_checker/solver/tests/__init__.py` - new
- `code/src/model_checker/solver/tests/test_adapter_equivalence.py` - new
- `code/src/model_checker/solver/tests/test_registry.py` - new

**Verification**:
- All equivalence tests pass when cvc5 is installed
- Tests skip gracefully when cvc5 not installed
- No regressions in existing test suite

---

### Phase 6: Documentation and Cleanup [NOT STARTED]

**Goal**: Document the solver abstraction layer and clean up technical debt

**Tasks**:
- [ ] Create `code/src/model_checker/solver/README.md` documenting the architecture
- [ ] Update `code/src/model_checker/utils/README.md` to reference solver layer for Z3 helpers
- [ ] Add docstrings to all new modules
- [ ] Update theory_lib docs to mention solver-agnostic expressions
- [ ] Add `cvc5` as optional dependency in `pyproject.toml`: `pip install model-checker[cvc5]`
- [ ] Clean up any remaining direct z3 imports in type hints (use TYPE_CHECKING blocks)

**Timing**: 0.5 hours

**Files to modify**:
- `code/src/model_checker/solver/README.md` - new
- `code/src/model_checker/utils/README.md` - update
- `pyproject.toml` - add cvc5 optional dependency

**Verification**:
- Documentation is complete and accurate
- `pip install model-checker[cvc5]` installs cvc5
- All code passes linting/type checking

## Testing & Validation

- [ ] All existing unit tests pass without modification
- [ ] All existing integration tests pass without modification
- [ ] New solver equivalence tests pass (when cvc5 installed)
- [ ] Manual verification: `model-checker --z3 examples/default.py` produces expected output
- [ ] Manual verification: `model-checker --cvc5 examples/default.py` produces equivalent output
- [ ] Performance: Z3 path shows no measurable regression

## Artifacts & Outputs

- `code/src/model_checker/solver/` package (new)
- `code/src/model_checker/solver/__init__.py`
- `code/src/model_checker/solver/interface.py`
- `code/src/model_checker/solver/expressions.py`
- `code/src/model_checker/solver/z3_adapter.py`
- `code/src/model_checker/solver/cvc5_adapter.py`
- `code/src/model_checker/solver/registry.py`
- `code/src/model_checker/solver/types.py`
- `code/src/model_checker/solver/README.md`
- `code/src/model_checker/solver/tests/` test directory
- Updated CLI with `--z3` and `--cvc5` flags
- Updated settings with `solver` configuration

## Rollback/Contingency

If issues arise during implementation:
1. Phase 1-2 are easily reversible by removing solver/ package and reverting import changes
2. Git commits at each phase boundary enable targeted rollback
3. Z3 passthrough design ensures no behavioral changes until cvc5 is explicitly selected
4. If cvc5 adapter proves problematic, keep it as experimental with clear warnings

If cvc5 proves unsuitable:
- Architecture still enables future solver additions
- Z3 remains default and fully functional
- Remove cvc5 adapter and document lessons learned
