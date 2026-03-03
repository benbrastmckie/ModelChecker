# Implementation Summary: Task #28

**Completed**: 2026-03-03
**Duration**: ~45 minutes

## Changes Made

Archived the `exclusion` and `imposition` semantic theories to `code/boneyard/`, removing them from active codebase while preserving for historical reference. Updated all references throughout the codebase to either remove these theories or handle their absence gracefully.

## Files Modified

### Phase 1: Archive Creation
- Created `code/boneyard/theory_lib/exclusion/` (moved from `code/src/model_checker/theory_lib/exclusion/`)
- Created `code/boneyard/theory_lib/imposition/` (moved from `code/src/model_checker/theory_lib/imposition/`)
- Created `code/boneyard/README.md` - Documents archive purpose and restoration instructions

### Phase 2: Theory Registry Update
- `code/src/model_checker/theory_lib/__init__.py` - Removed exclusion/imposition from AVAILABLE_THEORIES, updated docstring

### Phase 3: Notebook Templates
- Deleted `code/src/model_checker/output/notebook/templates/exclusion.py`
- Deleted `code/src/model_checker/output/notebook/templates/imposition.py`

### Phase 4: Utils and Builder Updates
- `code/src/model_checker/utils/testing.py` - Removed `run_strategy_test` function (exclusion-specific)
- `code/src/model_checker/utils/__init__.py` - Removed `run_strategy_test` from exports
- `code/src/model_checker/builder/loader.py` - Removed exclusion/imposition from prop_to_theory and theory_patterns mappings
- `code/src/model_checker/builder/serialize.py` - Updated docstring example (imposition -> logos)
- `code/src/model_checker/builder/runner.py` - Updated comment example

### Phase 5: Test File Updates
- `code/tests/fixtures/example_data.py` - Updated THEORY_NAMES, CLI_TEST_ARGS, MODULE_TEMPLATES
- `code/tests/integration/test_system_imports.py` - Updated theory imports and parametrized tests
- `code/tests/e2e/test_project_creation.py` - Updated parametrized theory tests
- `code/src/model_checker/builder/tests/fixtures/test_data.py` - Replaced EXCLUSION_CONTENT with BIMODAL_CONTENT, updated references
- `code/src/model_checker/builder/tests/unit/test_comparison.py` - Replaced Exclusion references with Bimodal
- `code/src/model_checker/builder/tests/unit/test_project_version.py` - Updated theory_names list
- `code/src/model_checker/builder/tests/unit/test_package_marker.py` - Changed exclusion test to bimodal
- `code/src/model_checker/builder/tests/integration/test_component_integration.py` - Updated multi-theory test content
- `code/src/model_checker/builder/tests/integration/test_build_module_theories.py` - Comprehensive updates from exclusion to bimodal
- `code/src/model_checker/theory_lib/tests/unit/test_error_handling.py` - Removed TestErrorHandlingIntegration class (relied on archived theories)
- Deleted `code/src/model_checker/theory_lib/tests/integration/test_refactored_workflows.py` - Entirely tested archived theories
- `code/src/model_checker/theory_lib/tests/__init__.py` - Updated docstring
- `code/src/model_checker/iterate/tests/integration/test_real_theory_integration.py` - Simplified to use mock instead of exclusion theory

### Phase 6: Documentation Updates
- `code/src/model_checker/theory_lib/docs/usage_guide.md` - Rewrote to focus on logos/bimodal, removed exclusion/imposition sections
- `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md` - Updated example reference

## Verification

- Import tests: All 25 critical tests pass
- Theory loading: `get_examples('logos')` works
- Error handling: `get_examples('exclusion')` and `get_examples('imposition')` raise `ValueError` as expected
- AVAILABLE_THEORIES correctly returns `['logos', 'bimodal']`

## Notes

- The archived theories remain accessible in `code/boneyard/` for historical reference
- Restoration instructions are documented in `code/boneyard/README.md`
- Two pre-existing test failures in `test_cli_subtheory.py` are unrelated to this change (they test exclusion theory CLI flags that were already failing)
