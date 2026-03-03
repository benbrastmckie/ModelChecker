# Implementation Plan: Task #28

- **Task**: 28 - archive_unused_theories
- **Status**: [NOT STARTED]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: None (basic exploration conducted during planning)
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Archive the `theory_lib/exclusion/` and `theory_lib/imposition/` directories to `code/boneyard/`, preserving their directory structure. Update all references throughout the codebase to either remove them or handle their absence gracefully. This is a cleanup operation to retire unused semantic theories while maintaining project history.

## Goals & Non-Goals

**Goals**:
- Archive exclusion and imposition theories to `code/boneyard/` preserving structure
- Remove these theories from `AVAILABLE_THEORIES` registry
- Update or remove all import references across the codebase
- Update notebook templates to remove exclusion/imposition support
- Update tests to skip or remove theory-specific tests
- Ensure remaining tests pass after removal

**Non-Goals**:
- Preserving backwards compatibility for these theories
- Creating migration paths for users of these theories
- Maintaining any functionality from these theories in active code

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Breaking imports in external code | M | L | Clear documentation in boneyard about archived status |
| Test failures from missing theories | H | H | Update parametrized tests to exclude these theories |
| Incomplete reference removal | M | M | Use comprehensive grep search in each phase |
| Missing runtime checks for theory availability | M | M | Test dynamic theory loading after changes |

## Implementation Phases

### Phase 1: Create Boneyard and Archive Directories [NOT STARTED]

**Goal**: Move exclusion and imposition theory directories to boneyard while preserving structure

**Tasks**:
- [ ] Create `code/boneyard/` directory if it doesn't exist
- [ ] Create `code/boneyard/theory_lib/` subdirectory
- [ ] Move `code/src/model_checker/theory_lib/exclusion/` to `code/boneyard/theory_lib/exclusion/`
- [ ] Move `code/src/model_checker/theory_lib/imposition/` to `code/boneyard/theory_lib/imposition/`
- [ ] Create `code/boneyard/README.md` explaining archive purpose and contents

**Timing**: 0.5 hours

**Files to modify**:
- Create `code/boneyard/` (new directory)
- Create `code/boneyard/theory_lib/` (new directory)
- Create `code/boneyard/README.md` (new file)
- Move `code/src/model_checker/theory_lib/exclusion/` (directory move)
- Move `code/src/model_checker/theory_lib/imposition/` (directory move)

**Verification**:
- `code/boneyard/theory_lib/exclusion/` exists with all original files
- `code/boneyard/theory_lib/imposition/` exists with all original files
- Original directories no longer exist in `theory_lib/`
- `code/boneyard/README.md` documents archive date and contents

---

### Phase 2: Update Theory Library Registry [NOT STARTED]

**Goal**: Remove exclusion and imposition from AVAILABLE_THEORIES and update related code

**Tasks**:
- [ ] Edit `code/src/model_checker/theory_lib/__init__.py` to remove 'exclusion' and 'imposition' from AVAILABLE_THEORIES list
- [ ] Update docstring to remove references to exclusion and imposition
- [ ] Update any inline comments referencing these theories

**Timing**: 0.5 hours

**Files to modify**:
- `code/src/model_checker/theory_lib/__init__.py` - Remove from AVAILABLE_THEORIES, update docstring

**Verification**:
- `from model_checker.theory_lib import AVAILABLE_THEORIES` returns only ['logos', 'bimodal']
- No references to exclusion/imposition in module docstring
- Python can import theory_lib without errors

---

### Phase 3: Update Notebook Templates [NOT STARTED]

**Goal**: Remove exclusion and imposition notebook template support

**Tasks**:
- [ ] Delete `code/src/model_checker/output/notebook/templates/exclusion.py`
- [ ] Delete `code/src/model_checker/output/notebook/templates/imposition.py`
- [ ] Update `code/src/model_checker/output/notebook/templates/__init__.py` if needed

**Timing**: 0.25 hours

**Files to modify**:
- Delete `code/src/model_checker/output/notebook/templates/exclusion.py`
- Delete `code/src/model_checker/output/notebook/templates/imposition.py`
- Review `code/src/model_checker/output/notebook/templates/__init__.py`

**Verification**:
- Template files no longer exist
- Notebook generation for logos still works
- No import errors in templates module

---

### Phase 4: Update Utils and Builder References [NOT STARTED]

**Goal**: Remove or update references in utils/testing.py and builder modules

**Tasks**:
- [ ] Update `code/src/model_checker/utils/testing.py` to remove exclusion-specific test helper (run_strategy_test function)
- [ ] Update `code/src/model_checker/builder/loader.py` to remove exclusion/imposition from prop_to_theory and theory_patterns mappings
- [ ] Update `code/src/model_checker/builder/serialize.py` to remove imposition operator reference
- [ ] Update `code/src/model_checker/builder/runner.py` comments if needed

**Timing**: 0.75 hours

**Files to modify**:
- `code/src/model_checker/utils/testing.py` - Remove run_strategy_test function and exclusion imports
- `code/src/model_checker/builder/loader.py` - Remove ExclusionProposition and ImpositionProposition mappings
- `code/src/model_checker/builder/serialize.py` - Remove imposition operator reference
- `code/src/model_checker/builder/runner.py` - Update comments

**Verification**:
- utils.testing module imports without errors
- builder modules import without errors
- No references to exclusion/imposition in these files

---

### Phase 5: Update Test Files [NOT STARTED]

**Goal**: Update test files to remove or skip exclusion/imposition theory tests

**Tasks**:
- [ ] Update `code/tests/fixtures/example_data.py` to remove exclusion/imposition from THEORY_NAMES and MODULE_TEMPLATES
- [ ] Update `code/tests/integration/test_system_imports.py` to remove exclusion/imposition from parametrized tests
- [ ] Update `code/tests/e2e/test_project_creation.py` to remove exclusion/imposition theory tests
- [ ] Update `code/src/model_checker/builder/tests/fixtures/test_data.py` to remove exclusion content
- [ ] Update or remove `code/src/model_checker/builder/tests/integration/test_build_module_theories.py` exclusion-specific tests
- [ ] Update `code/src/model_checker/builder/tests/unit/test_project_version.py` theory list
- [ ] Update `code/src/model_checker/builder/tests/unit/test_package_marker.py` exclusion references
- [ ] Update `code/src/model_checker/builder/tests/integration/test_component_integration.py` multi-theory tests
- [ ] Delete or update theory_lib-level test files that specifically test exclusion/imposition:
  - `code/src/model_checker/theory_lib/tests/unit/test_error_handling.py`
  - `code/src/model_checker/theory_lib/tests/integration/test_refactored_workflows.py`
- [ ] Update `code/src/model_checker/iterate/tests/integration/test_real_theory_integration.py`

**Timing**: 1.0 hours

**Files to modify**:
- `code/tests/fixtures/example_data.py`
- `code/tests/integration/test_system_imports.py`
- `code/tests/e2e/test_project_creation.py`
- `code/src/model_checker/builder/tests/fixtures/test_data.py`
- `code/src/model_checker/builder/tests/integration/test_build_module_theories.py`
- `code/src/model_checker/builder/tests/unit/test_project_version.py`
- `code/src/model_checker/builder/tests/unit/test_package_marker.py`
- `code/src/model_checker/builder/tests/integration/test_component_integration.py`
- `code/src/model_checker/theory_lib/tests/unit/test_error_handling.py`
- `code/src/model_checker/theory_lib/tests/integration/test_refactored_workflows.py`
- `code/src/model_checker/iterate/tests/integration/test_real_theory_integration.py`

**Verification**:
- All modified test files pass syntax check
- No import errors from test modules
- Test collection succeeds (pytest --collect-only)

---

### Phase 6: Update Documentation References [NOT STARTED]

**Goal**: Update documentation files that reference exclusion/imposition theories

**Tasks**:
- [ ] Update `code/src/model_checker/theory_lib/docs/usage_guide.md` to remove exclusion/imposition sections
- [ ] Update `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` if it references these theories
- [ ] Review and update any other documentation in `code/src/model_checker/theory_lib/docs/`

**Timing**: 0.25 hours

**Files to modify**:
- `code/src/model_checker/theory_lib/docs/usage_guide.md`
- `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` (if needed)

**Verification**:
- Documentation files have no broken references to exclusion/imposition
- Remaining documentation accurately describes available theories

---

### Phase 7: Run Tests and Validate [NOT STARTED]

**Goal**: Verify all tests pass and no regressions exist

**Tasks**:
- [ ] Run full test suite: `PYTHONPATH=code/src pytest code/tests/ -v`
- [ ] Run theory_lib tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/ -v` (for remaining logos/bimodal)
- [ ] Run builder tests: `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -v`
- [ ] Run logos theory tests: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/ -v`
- [ ] Test dynamic theory loading: verify `get_examples('logos')` works and `get_examples('exclusion')` raises ValueError
- [ ] Verify CLI works with remaining theories

**Timing**: 0.25 hours

**Verification**:
- All test suites pass
- No import errors at runtime
- CLI functions correctly with logos theory
- Dynamic theory loading raises appropriate errors for removed theories

## Testing & Validation

- [ ] Full test suite passes with `PYTHONPATH=code/src pytest code/tests/ -v`
- [ ] Builder tests pass with theory loading
- [ ] Logos theory tests pass completely
- [ ] Bimodal theory tests pass
- [ ] No import errors when running model-checker CLI
- [ ] `get_examples('exclusion')` raises `ValueError: Unknown theory: exclusion`
- [ ] `get_examples('imposition')` raises `ValueError: Unknown theory: imposition`

## Artifacts & Outputs

- `code/boneyard/theory_lib/exclusion/` - Archived exclusion theory
- `code/boneyard/theory_lib/imposition/` - Archived imposition theory
- `code/boneyard/README.md` - Archive documentation
- Updated source files throughout codebase

## Rollback/Contingency

To restore the archived theories if needed:
1. Move directories back: `mv code/boneyard/theory_lib/exclusion code/src/model_checker/theory_lib/`
2. Move directories back: `mv code/boneyard/theory_lib/imposition code/src/model_checker/theory_lib/`
3. Revert changes to `theory_lib/__init__.py` (add back to AVAILABLE_THEORIES)
4. Restore notebook templates from git history
5. Restore test file changes from git history
6. Run tests to verify restoration

Git provides full history for reverting individual file changes if partial restoration is needed.
