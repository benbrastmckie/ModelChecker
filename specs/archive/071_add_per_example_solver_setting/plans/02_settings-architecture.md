# Implementation Plan: Task #71

- **Task**: 71 - Add per-example solver setting
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: None (builds on completed Task 70 cvc5 compatibility)
- **Research Inputs**: reports/01_per-example-solver.md, reports/02_settings-architecture.md
- **Artifacts**: plans/02_settings-architecture.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: true

## Overview

Add a `solver` field to example settings that enables per-example solver selection. The research identified a well-designed layered settings system where the infrastructure already supports this feature -- the gap is simply connecting existing pieces. The key insight is using `'solver': None` as default to enable proper fall-through precedence, and passing `self.settings` to `create_solver()` calls.

### Research Integration

From the deep-dive research (02_settings-architecture.md):
- Settings flow: SemanticDefaults -> Theory defaults -> SettingsManager.get_complete_settings() -> merged `self.settings`
- The gap: `create_solver()` accepts a `settings` parameter but isn't being passed `self.settings`
- Design pattern: `'solver': None` enables proper fall-through to general settings and theory defaults
- CLI override via `_cli_override` global already takes absolute precedence

## Goals & Non-Goals

**Goals**:
- Add `solver` field to `DEFAULT_EXAMPLE_SETTINGS` in all semantic theories
- Pass merged settings to `create_solver()` in `ModelDefaults`
- Handle `None` solver value correctly in registry's `get_active_backend()`
- Validate solver field values ('z3', 'cvc5', or None)
- Maintain CLI override as highest precedence

**Non-Goals**:
- Changing the CLI flag processing (already works correctly)
- Adding new CLI flags
- Modifying the SettingsManager merge logic (already correct)
- Supporting additional solver backends beyond z3/cvc5

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Multiple solver creation points missed | Medium | Low | Research identified exactly 2 call sites in structure.py |
| Settings merge order incorrect | Medium | Low | Research confirmed example settings override general settings |
| Existing tests break | Medium | Low | Run existing test suite after each change |

## Implementation Phases

### Phase 1: Add solver to DEFAULT_EXAMPLE_SETTINGS [NOT STARTED]

**Goal**: Enable `solver` as a recognized example-level setting in all semantic theories

**Tasks**:
- [ ] Add `'solver': None` to `LogosSemantics.DEFAULT_EXAMPLE_SETTINGS` in `theory_lib/logos/semantic.py`
- [ ] Add `'solver': None` to `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS` in `theory_lib/bimodal/semantic.py`
- [ ] Verify setting is recognized (no "unknown setting" warning)

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/semantic.py` - Add solver field
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Add solver field

**Verification**:
- Example with `'solver': 'z3'` in settings does not produce "unknown setting" warning
- Example with `'solver': 'cvc5'` in settings does not produce "unknown setting" warning

---

### Phase 2: Handle None in get_active_backend [NOT STARTED]

**Goal**: Ensure `None` solver value falls through to next precedence level

**Tasks**:
- [ ] Modify `get_active_backend()` in `solver/registry.py` to check `settings["solver"] is not None`
- [ ] Ensure existing precedence chain (CLI > env > settings > default) is preserved

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/solver/registry.py` - Add null check in get_active_backend()

**Verification**:
- `get_active_backend({"solver": None})` returns "z3" (default)
- `get_active_backend({"solver": "cvc5"})` returns "cvc5"
- `get_active_backend(None)` returns "z3" (default)

---

### Phase 3: Pass settings to create_solver [NOT STARTED]

**Goal**: Connect the merged settings to solver creation

**Tasks**:
- [ ] Update `_setup_solver()` in `models/structure.py` to pass `self.settings`
- [ ] Update `solve()` in `models/structure.py` to pass `self.settings`

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/models/structure.py` - Pass settings to create_solver() at 2 call sites

**Verification**:
- Example with `'solver': 'cvc5'` uses cvc5 solver
- Example with no solver setting uses z3 (default)
- CLI `--cvc5` still overrides example setting

---

### Phase 4: Add validation and tests [NOT STARTED]

**Goal**: Ensure invalid solver values are caught and precedence chain is tested

**Tasks**:
- [ ] Add solver value validation in `SettingsManager._validate_solver_value()` or similar
- [ ] Add test for per-example solver selection in `solver/tests/unit/test_registry.py`
- [ ] Add test for precedence: CLI > example > general > default
- [ ] Add test for None handling (falls through to next level)

**Timing**: 45 minutes

**Files to modify**:
- `code/src/model_checker/settings/settings.py` - Add solver value validation
- `code/src/model_checker/solver/tests/unit/test_registry.py` - Add precedence tests

**Verification**:
- Invalid solver value (e.g., 'invalid') raises ValidationError
- All new tests pass
- Existing tests still pass

---

### Phase 5: Documentation [NOT STARTED]

**Goal**: Document the new per-example solver setting

**Tasks**:
- [ ] Update `settings/README.md` to document the solver field in example settings
- [ ] Update `solver/README.md` to document the complete precedence chain

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/settings/README.md` - Document solver example setting
- `code/src/model_checker/solver/README.md` - Document precedence chain

**Verification**:
- Documentation accurately describes the solver setting
- Precedence chain is clearly documented

## Testing & Validation

- [ ] Run existing solver tests: `pytest code/src/model_checker/solver/tests/`
- [ ] Run settings tests: `pytest code/src/model_checker/settings/tests/`
- [ ] Test example with `'solver': 'z3'` setting
- [ ] Test example with `'solver': 'cvc5'` setting
- [ ] Test example without solver setting (uses default)
- [ ] Test CLI `--cvc5` overrides example `'solver': 'z3'`
- [ ] Test general_settings solver overridden by example solver

## Artifacts & Outputs

- plans/02_settings-architecture.md (this file)
- summaries/02_execution-summary.md (upon completion)

## Rollback/Contingency

If implementation causes issues:
1. Revert the 4 modified files to their pre-change state
2. The system returns to using only CLI and environment-based solver selection
3. No data loss possible -- changes are purely additive to settings infrastructure
