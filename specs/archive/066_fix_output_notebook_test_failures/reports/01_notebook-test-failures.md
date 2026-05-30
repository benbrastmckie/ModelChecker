# Research Report: Fix output/notebook test failures

**Task**: 66 - Fix output/notebook test failures
**Date**: 2026-03-30
**Session**: sess_1774916194_ea117d

## Test Results Summary

14 tests collected, 6 failures, 8 passes.

| Test | Status | Error Type |
|------|--------|------------|
| test_generate_notebook_raises_on_missing_template | FAIL | ValueError (test design issue) |
| test_generate_notebook_stream_creates_file | FAIL | AttributeError (wrong mock path) |
| test_template_loading_for_different_theories | FAIL | AttributeError (stale API) |
| test_template_placeholder_substitution | FAIL | AttributeError (wrong mock path) |
| test_get_template_for_imposition_semantics | FAIL | ModuleNotFoundError |
| test_get_template_for_witness_semantics | FAIL | ModuleNotFoundError |

## Root Cause Analysis

### Failure Type 1: Missing Template Modules (2 tests)

**Affected tests**:
- `test_get_template_for_imposition_semantics`
- `test_get_template_for_witness_semantics`

**Root cause**: The `TemplateLoader.get_template_for_class()` method references two template modules that do not exist:
- `model_checker.output.notebook.templates.exclusion` (for WitnessSemantics)
- `model_checker.output.notebook.templates.imposition` (for ImpositionSemantics)

**Current template files** in `src/model_checker/output/notebook/templates/`:
- `__init__.py`
- `base.py` - Contains `DirectNotebookTemplate` (base class)
- `logos.py` - Contains `LogosNotebookTemplate` (extends base)

The `exclusion.py` and `imposition.py` template modules were never created. The `TemplateLoader` (lines 32-36) imports `ExclusionNotebookTemplate` from `templates.exclusion` and `ImpositionNotebookTemplate` from `templates.imposition`, but these files do not exist.

**Fix options**:
- **Option A (create stubs)**: Create `exclusion.py` and `imposition.py` following the same pattern as `logos.py`, subclassing `DirectNotebookTemplate`.
- **Option B (use fallback)**: Modify `TemplateLoader` to fall through to the `DirectNotebookTemplate` fallback for these cases instead of importing non-existent modules. Update tests to expect `DirectNotebookTemplate`.

**Recommendation**: Option A. The semantics types (`WitnessSemantics`, `ImpositionSemantics`) are defined as protocols in `theory_lib/types.py` (lines 88 and 116), indicating they are real theory types that deserve dedicated templates. Creating stub templates that subclass `DirectNotebookTemplate` is straightforward and future-proofs the architecture.

### Failure Type 2: Stale API Name (1 test)

**Affected test**: `test_template_loading_for_different_theories`

**Root cause**: The test calls `loader.get_template_class(theory_name)` (line 211 of `test_notebook_generation.py`), but the actual method is `loader.get_template_for_class(semantics_class)`. The error message confirms this: `'TemplateLoader' object has no attribute 'get_template_class'. Did you mean: 'get_template_for_class'?`

Additionally, the test passes a theory name string (e.g., `'logos'`) as the argument, but `get_template_for_class()` expects a class object with a `__name__` attribute, not a string. The entire test design needs updating.

**Fix**: Change `loader.get_template_class(theory_name)` to `loader.get_template_for_class(mock_semantics_class)` where `mock_semantics_class` has the appropriate `__name__` set. Also fix the expected template names (currently `'LogosTemplate'`, `'ExclusionTemplate'`, `'ImpositionTemplate'` but actual class names are `'LogosNotebookTemplate'`, etc.).

### Failure Type 3: Wrong Mock Path (2 tests)

**Affected tests**:
- `test_generate_notebook_stream_creates_file`
- `test_template_placeholder_substitution`

**Root cause**: Both tests use `@patch('model_checker.notebook.streaming_generator.json.load')` but the correct module path is `model_checker.output.notebook.streaming_generator`. The `model_checker` package has no direct `notebook` submodule -- it is under `output.notebook`.

The error: `AttributeError: module 'model_checker' has no attribute 'notebook'`

**Fix**: Change mock paths from `model_checker.notebook.streaming_generator` to `model_checker.output.notebook.streaming_generator`.

### Failure Type 4: Test Design Issue (1 test)

**Affected test**: `test_generate_notebook_raises_on_missing_template`

**Root cause**: The test expects a `FileNotFoundError` but gets `ValueError: Could not locate theory_lib from /tmp/...`. The streaming generator's `_discover_template_path()` method navigates up from the source path looking for a `theory_lib` directory. Since the test uses `tempfile.NamedTemporaryFile` in `/tmp/`, it never finds `theory_lib` and raises `ValueError` before it can check if the template file exists.

**Fix**: Either (a) mock `_discover_template_path` to return a non-existent template path so `FileNotFoundError` is raised from `_load_template_sections`, or (b) restructure the temp file path to include `theory_lib` in its hierarchy.

## Current TemplateLoader API

The `TemplateLoader` class (in `template_loader.py`) has one public method:

```python
def get_template_for_class(self, semantics_class: Any) -> DirectNotebookTemplate
```

- Input: A semantics class object with a `__name__` attribute
- Returns: A template instance (subclass of `DirectNotebookTemplate`)
- Dispatches based on `class_name`:
  - `'LogosSemantics'` -> `LogosNotebookTemplate()`
  - `'WitnessSemantics'` -> `ExclusionNotebookTemplate()` (MISSING MODULE)
  - `'ImpositionSemantics'` -> `ImpositionNotebookTemplate()` (MISSING MODULE)
  - Anything else -> `DirectNotebookTemplate()` (fallback)

There is no `get_template_class()` method. The integration test references a stale API.

## Current State of Template Modules

| File | Class | Status |
|------|-------|--------|
| `templates/base.py` | `DirectNotebookTemplate` | EXISTS, working |
| `templates/logos.py` | `LogosNotebookTemplate` | EXISTS, working |
| `templates/exclusion.py` | `ExclusionNotebookTemplate` | MISSING |
| `templates/imposition.py` | `ImpositionNotebookTemplate` | MISSING |

## Recommended Fixes

### Fix 1: Create missing template modules

Create `exclusion.py` and `imposition.py` in `src/model_checker/output/notebook/templates/`, each containing a class that subclasses `DirectNotebookTemplate`. These can be minimal stubs that override `get_required_imports()` and `generate_theory_setup()` with theory-appropriate content. Follow the pattern established by `logos.py`.

### Fix 2: Fix stale API call in integration test

In `test_notebook_generation.py` line 211, change:
- `loader.get_template_class(theory_name)` to `loader.get_template_for_class(mock_class)`
- Create mock class objects with appropriate `__name__` values
- Fix expected template names (`'LogosTemplate'` -> `'LogosNotebookTemplate'`, etc.)

### Fix 3: Fix wrong mock paths in integration test

In `test_notebook_generation.py`, change mock decorator paths:
- Line 46: `model_checker.notebook.streaming_generator.json.load` -> `model_checker.output.notebook.streaming_generator.json.load`
- Line 142: Same fix

### Fix 4: Fix test design for missing template test

In `test_generate_notebook_raises_on_missing_template`, mock `_discover_template_path` to return a controlled path so the test can properly exercise the `FileNotFoundError` code path in `_load_template_sections`.

## Effort Estimate

| Fix | Effort | Complexity |
|-----|--------|------------|
| Create exclusion.py template | ~30 min | Low (copy logos.py pattern) |
| Create imposition.py template | ~30 min | Low (copy logos.py pattern) |
| Fix stale API call in test | ~10 min | Low |
| Fix wrong mock paths | ~5 min | Trivial |
| Fix missing template test design | ~15 min | Medium |
| **Total** | **~1.5 hours** | **Low-Medium** |

## Files to Modify

1. **CREATE**: `src/model_checker/output/notebook/templates/exclusion.py`
2. **CREATE**: `src/model_checker/output/notebook/templates/imposition.py`
3. **MODIFY**: `src/model_checker/output/notebook/tests/integration/test_notebook_generation.py`
   - Fix mock paths (lines 46, 142)
   - Fix stale API call (line 211)
   - Fix expected template class names (line 212)
   - Fix missing template test to mock `_discover_template_path`
