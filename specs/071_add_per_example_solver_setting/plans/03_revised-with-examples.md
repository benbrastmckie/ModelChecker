# Implementation Plan: Task #71 (Revised)

- **Task**: 71 - Add per-example solver setting
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: None (builds on completed Task 70 cvc5 compatibility)
- **Research Inputs**: reports/01_per-example-solver.md, reports/02_settings-architecture.md
- **Artifacts**: plans/03_revised-with-examples.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: true

## Overview

Add a `solver` field to example settings that enables per-example solver selection. This revision changes the default value from `None` to `'z3'` for explicit declaration, and adds a phase to update all existing examples with the new field.

### Revision Notes

Changes from v02:
1. **Default value**: Changed from `'solver': None` to `'solver': 'z3'` - explicit is better than implicit
2. **Example updates**: Added Phase 4 to update all existing example files with the solver field
3. **Simplified registry logic**: No need for special None handling since default is 'z3'

### Precedence Chain

Still maintains: CLI flags (`--z3`/`--cvc5`) > per-example `solver` setting > semantic theory defaults

## Goals & Non-Goals

**Goals**:
- Add `'solver': 'z3'` field to `DEFAULT_EXAMPLE_SETTINGS` in all semantic theories
- Pass merged settings to `create_solver()` in `ModelDefaults`
- Update all existing examples to include `'solver': 'z3'` or `'solver': 'cvc5'` as appropriate
- Validate solver field values ('z3', 'cvc5')
- Maintain CLI override as highest precedence

**Non-Goals**:
- Changing the CLI flag processing (already works correctly)
- Supporting additional solver backends beyond z3/cvc5

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Many examples need updating | Low | High | Use grep/sed to batch update all examples |
| Some examples require cvc5 | Medium | Low | Identify during update, set to 'cvc5' explicitly |
| Existing tests break | Medium | Low | Run test suite after each change |

## Implementation Phases

### Phase 1: Add solver to DEFAULT_EXAMPLE_SETTINGS [NOT STARTED]

**Goal**: Enable `solver` as a recognized example-level setting with 'z3' default

**Tasks**:
- [ ] Add `'solver': 'z3'` to `LogosSemantics.DEFAULT_EXAMPLE_SETTINGS` in `theory_lib/logos/semantic.py`
- [ ] Add `'solver': 'z3'` to `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS` in `theory_lib/bimodal/semantic.py`
- [ ] Verify setting is recognized (no "unknown setting" warning)

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/semantic.py` - Add solver field
- `code/src/model_checker/theory_lib/bimodal/semantic.py` - Add solver field

**Verification**:
- Example with `'solver': 'z3'` in settings does not produce "unknown setting" warning
- Example with `'solver': 'cvc5'` in settings does not produce "unknown setting" warning

---

### Phase 2: Registry handles solver setting [NOT STARTED]

**Goal**: Ensure `get_active_backend()` reads solver from settings

**Tasks**:
- [ ] Verify `get_active_backend()` in `solver/registry.py` reads from `settings["solver"]`
- [ ] Ensure CLI override (`_cli_override`) still takes precedence
- [ ] Test with explicit 'z3' and 'cvc5' values

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/solver/registry.py` - Verify/update get_active_backend()

**Verification**:
- `get_active_backend({"solver": "z3"})` returns "z3"
- `get_active_backend({"solver": "cvc5"})` returns "cvc5"
- CLI `--cvc5` overrides `{"solver": "z3"}`

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
- Example with `'solver': 'z3'` uses z3 solver
- CLI `--cvc5` still overrides example setting

---

### Phase 4: Update all examples with solver field [NOT STARTED]

**Goal**: Add explicit `'solver': 'z3'` or `'solver': 'cvc5'` to all existing examples

**Tasks**:
- [ ] Identify all example directories in theory_lib (logos, bimodal, first_order, etc.)
- [ ] For each example file, add `'solver': 'z3'` to the example_settings dict
- [ ] Identify any examples that specifically require cvc5 and set to `'solver': 'cvc5'`
- [ ] Run tests to verify all examples still pass

**Timing**: 45 minutes

**Files to modify**:
- All example files in `code/src/model_checker/theory_lib/*/examples/*.py`
- Estimated 50-100 example files

**Pattern for update**:
```python
# Before
example_settings = {
    'N': 3,
    'contingent': True,
}

# After
example_settings = {
    'N': 3,
    'contingent': True,
    'solver': 'z3',  # Added
}
```

**Verification**:
- All examples have solver field
- `grep -r "example_settings" | grep -v "solver"` returns nothing in theory_lib examples
- All tests pass

---

### Phase 5: Add validation and tests [NOT STARTED]

**Goal**: Ensure invalid solver values are caught and precedence chain is tested

**Tasks**:
- [ ] Add solver value validation (must be 'z3' or 'cvc5')
- [ ] Add test for per-example solver selection in solver tests
- [ ] Add test for precedence: CLI > example > theory default
- [ ] Add test for cvc5 example running with cvc5

**Timing**: 30 minutes

**Files to modify**:
- `code/src/model_checker/settings/settings.py` - Add solver value validation
- `code/src/model_checker/solver/tests/unit/test_registry.py` - Add precedence tests

**Verification**:
- Invalid solver value (e.g., 'invalid') raises ValidationError
- All new tests pass
- Existing tests still pass

---

### Phase 6: Documentation [NOT STARTED]

**Goal**: Document the new per-example solver setting

**Tasks**:
- [ ] Update settings documentation to describe solver field
- [ ] Document precedence chain: CLI > example setting > theory default

**Timing**: 15 minutes

**Files to modify**:
- `code/src/model_checker/settings/README.md` - Document solver example setting
- `code/src/model_checker/solver/README.md` - Document precedence chain

**Verification**:
- Documentation accurately describes the solver setting
- Precedence chain is clearly documented

## Testing & Validation

- [ ] Run existing solver tests: `pytest code/src/model_checker/solver/tests/`
- [ ] Run all example tests: `python run_tests.py`
- [ ] Test example with `'solver': 'z3'` setting
- [ ] Test example with `'solver': 'cvc5'` setting
- [ ] Test CLI `--cvc5` overrides example `'solver': 'z3'`

## Artifacts & Outputs

- plans/03_revised-with-examples.md (this file)
- summaries/03_execution-summary.md (upon completion)

## Rollback/Contingency

If implementation causes issues:
1. Revert the modified files to their pre-change state
2. The system returns to using only CLI and environment-based solver selection
3. No data loss possible -- changes are additive to settings infrastructure
