# Phase 4 Handoff: Clean Residual Source References

**Completed**: 2026-06-01
**Session**: sess_1780208200_22f2ee
**Tests**: 172 passed (gate maintained)

## What Was Done

Updated 11 source files to remove references to deleted theories/modules:

1. `builder/loader.py` - Removed `'LogosProposition': 'logos'` and `'Logos': 'logos'` from mapping dicts; updated docstrings
2. `builder/project.py` - Changed default theory from `'logos'` to `'bimodal'`; removed logos-specific subtheory handling in `ask_generate()`
3. `builder/serialize.py` - Updated docstring to use bimodal module path example
4. `builder/module.py` - Removed jupyter-only save check (`only_notebook` variable); simplified setup code
5. `output/manager.py` - Deleted `_generate_notebook()` method; removed notebook format check in `finalize()`; simplified `set_module_context()`; removed `FORMAT_NOTEBOOK` and `DEFAULT_NOTEBOOK_FILE` imports
6. `output/config.py` - Removed `'notebook'` from all-formats default; deleted `'notebook'`/`'jupyter'` format parsing branches; updated docstrings
7. `output/formatters/__init__.py` - Removed `NotebookFormatter` import; deleted `output/formatters/notebook.py`
8. `theory_lib/errors.py` - Removed logos-specific `WitnessSemanticError`, `LogosSubtheoryError`, `LogosProtocolError`, `LogosOperatorError`; removed `ImpositionSemanticError`, `ImpositionOperationError`, `ImpositionModelError`, `ImpositionHelperError`; kept `WitnessRegistryError`, `WitnessConstraintError`, `WitnessPredicateError` (used by bimodal tests) as direct subclasses of `WitnessError`
9. `theory_lib/types.py` - Removed `ImpositionSemantics` protocol class; removed `SubtheoryProtocol` (logos-specific)
10. `theory_lib/tests/test_meta_data.py` - Updated expected theories list to `["bimodal"]`
11. `model_checker/__main__.py` - Updated help text to `'bimodal'`; removed `--subtheory` argument

## Deviations

- **theory_lib/errors.py**: Plan said to remove `WitnessSemanticError` and `WitnessPredicateError`. These classes were actually used by bimodal's semantic/witness_registry.py and tests. Kept `WitnessRegistryError`, `WitnessConstraintError`, `WitnessPredicateError` but made them direct subclasses of `WitnessError` (removing the exclusion-theory-specific `WitnessSemanticError` parent). This was the correct approach.
- Also deleted `output/formatters/notebook.py` which was missed in Phase 3 (it imported from deleted `output/notebook` package).

## Next Phase

Phase 5: Clean Test Files — delete logos-specific test files from `code/tests/` and `builder/tests/`, strip logos references from mixed files.
