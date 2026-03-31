# Implementation Plan: Per-Example Solver Setting

- **Task**: 71 - Add per-example solver setting
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: None (builds on existing solver abstraction from tasks 58-65, 70)
- **Research Inputs**: specs/071_add_per_example_solver_setting/reports/01_per-example-solver.md
- **Artifacts**: plans/01_per-example-solver.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Add a `solver` field to example settings that accepts `'z3'` or `'cvc5'` and overrides semantic theory defaults. The existing infrastructure already supports a `solver` field in general settings and the solver registry already has precedence logic. The main implementation work connects these existing pieces: add `solver` to `DEFAULT_EXAMPLE_SETTINGS`, pass settings to `create_solver()`, and handle `None` values in the registry.

### Research Integration

Key findings from research report (01_per-example-solver.md):
- `solver` field already exists in `DEFAULT_GENERAL_SETTINGS` but NOT in `DEFAULT_EXAMPLE_SETTINGS`
- `create_solver()` is called without passing settings in `structure.py`
- `get_active_backend()` already supports a `settings` parameter
- CLI flags set a global `_cli_override` that takes precedence over everything else

## Goals & Non-Goals

**Goals**:
- Add `solver` field to `DEFAULT_EXAMPLE_SETTINGS` in all theories
- Pass merged settings to `create_solver()` in `ModelDefaults`
- Implement precedence: CLI flags > per-example > general settings > theory defaults > registry default
- Validate solver field values ('z3', 'cvc5', or None)
- Add comprehensive tests for the precedence chain

**Non-Goals**:
- Changing existing CLI flag behavior
- Adding new solver backends
- Modifying the solver registry's core architecture

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Multiple solver creation points missed | H | M | Grep for all `create_solver()` calls and update systematically |
| Settings merge order incorrect | M | L | Add explicit tests for precedence chain |
| Breaking existing tests | M | L | Run test suite after each phase |
| cvc5 availability on CI | L | L | Skip cvc5-specific tests if unavailable |

## Implementation Phases

### Phase 1: Add solver field to DEFAULT_EXAMPLE_SETTINGS [NOT STARTED]

**Goal**: Add the `solver` field to example settings defaults in all theories with value `None` (indicating "use higher-level defaults").

**Tasks**:
- [ ] Add `'solver': None` to `LogosSemantics.DEFAULT_EXAMPLE_SETTINGS` in `theory_lib/logos/semantic.py`
- [ ] Add `'solver': None` to `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS` in `theory_lib/bimodal/semantic.py`
- [ ] Verify `SemanticDefaults.DEFAULT_GENERAL_SETTINGS` already has `'solver': 'z3'`

**Timing**: 20 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/semantic.py` - Add solver field
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Add solver field

**Verification**:
- Run existing tests to confirm no breakage
- Manually verify settings merge includes solver field

---

### Phase 2: Update solver registry to handle None values [NOT STARTED]

**Goal**: Modify `get_active_backend()` to treat `None` solver value as "not specified", falling through to next precedence level.

**Tasks**:
- [ ] Update `get_active_backend()` in `registry.py` to check for `None` before using settings value
- [ ] Ensure the precedence chain is: CLI > env var > settings (if not None) > default

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/solver/registry.py` - Handle None in get_active_backend()

**Verification**:
- Unit test: `get_active_backend({'solver': None})` returns default
- Unit test: `get_active_backend({'solver': 'cvc5'})` returns 'cvc5'

---

### Phase 3: Pass settings to create_solver() in ModelDefaults [NOT STARTED]

**Goal**: Modify solver creation points to pass the merged settings dictionary to `create_solver()`.

**Tasks**:
- [ ] Locate all `create_solver()` call sites in `structure.py`
- [ ] Update `_setup_solver()` to pass `self.settings` to `create_solver()`
- [ ] Update `solve()` to pass `self.settings` to `create_solver()`
- [ ] Verify settings are available at both call sites

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/models/structure.py` - Pass settings at both create_solver() calls

**Verification**:
- Run existing tests to confirm no breakage
- Add debug logging to verify correct solver is selected

---

### Phase 4: Add validation for solver field [NOT STARTED]

**Goal**: Add validation to reject invalid solver values early with clear error messages.

**Tasks**:
- [ ] Add validation in settings processing for `solver` field
- [ ] Valid values: `None`, `'z3'`, `'cvc5'`
- [ ] Raise clear error for invalid values

**Timing**: 20 minutes

**Files to modify**:
- `code/src/model_checker/settings/settings.py` - Add solver validation

**Verification**:
- Test that invalid solver value raises appropriate error
- Test that valid values pass validation

---

### Phase 5: Add comprehensive tests [NOT STARTED]

**Goal**: Add tests verifying the complete precedence chain and per-example solver functionality.

**Tasks**:
- [ ] Add test: per-example `solver: 'cvc5'` uses cvc5 (when available)
- [ ] Add test: per-example `solver: None` uses general settings default
- [ ] Add test: CLI `--z3` overrides per-example `solver: 'cvc5'`
- [ ] Add test: CLI `--cvc5` overrides per-example `solver: 'z3'`
- [ ] Add test: invalid solver value raises error
- [ ] Skip cvc5 tests if cvc5 not available

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/solver/tests/unit/test_registry.py` - Add precedence tests

**Verification**:
- All new tests pass
- Existing tests still pass
- Test coverage includes all precedence levels

---

### Phase 6: Documentation updates [NOT STARTED]

**Goal**: Update documentation to describe the per-example solver setting and precedence chain.

**Tasks**:
- [ ] Update `solver/README.md` with precedence chain documentation
- [ ] Add example showing per-example solver usage
- [ ] Document valid values and default behavior

**Timing**: 20 minutes

**Files to modify**:
- `code/src/model_checker/solver/README.md` - Document precedence chain

**Verification**:
- Documentation is clear and accurate
- Example code is syntactically correct

## Testing & Validation

- [ ] All existing solver tests pass
- [ ] New precedence chain tests pass
- [ ] Example with `solver: 'z3'` uses z3
- [ ] Example with `solver: 'cvc5'` uses cvc5 (when available)
- [ ] Example with `solver: None` uses theory default
- [ ] CLI flags override per-example settings
- [ ] Invalid solver values are rejected with clear errors
- [ ] Integration test: run same example with different per-example solver settings

## Artifacts & Outputs

- Modified: `code/src/model_checker/theory_lib/logos/semantic.py`
- Modified: `code/src/model_checker/theory_lib/bimodal/semantic.py`
- Modified: `code/src/model_checker/solver/registry.py`
- Modified: `code/src/model_checker/models/structure.py`
- Modified: `code/src/model_checker/settings/settings.py`
- Modified: `code/src/model_checker/solver/tests/unit/test_registry.py`
- Modified: `code/src/model_checker/solver/README.md`

## Rollback/Contingency

If implementation causes issues:
1. Revert the `solver` field additions to `DEFAULT_EXAMPLE_SETTINGS`
2. Revert changes to `create_solver()` calls in `structure.py`
3. Existing behavior is preserved (CLI and general settings continue to work)

The changes are additive and isolated to the settings flow, so rollback is straightforward.
