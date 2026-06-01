# Task 100: Strip Non-Bimodal Code — Codebase Audit

**Session**: sess_1780208200_22f2ee
**Date**: 2026-06-01
**Researcher**: python-research-agent

---

## 1. Executive Summary

This audit maps every file to delete, every coupling point to fix, every dependency to remove from pyproject.toml, and provides a risk assessment for the stripping operation. The gate condition (175 bimodal tests passing) is currently green.

**Key finding**: `theory_lib/imposition/` and `theory_lib/exclusion/` do not exist as separate directories — they were already removed or never created as standalone theories. The `output/notebook/templates/` directory contains exclusion and imposition template files but those are part of the notebook module being deleted.

**Critical dependency**: `theory_lib/bimodal/iterate.py` imports `BaseModelIterator` from `model_checker.iterate.core`. Deleting the `iterate/` module will break the bimodal `iterate.py` unless it is refactored to be self-contained first.

---

## 2. Files to Delete

### 2.1 theory_lib/logos/ (entire directory tree)

```
code/src/model_checker/theory_lib/logos/
  __init__.py
  iterate.py
  docs/
  subtheories/
    constitutive/  (with tests/, notebooks/)
    counterfactual/ (with tests/, notebooks/, report/)
    extensional/   (with tests/, notebooks/)
    first-order/   (with tests/, unit/)  [note: hyphen variant]
    first_order/   (with tests/, unit/, output/)  [note: underscore variant]
    modal/         (with tests/, notebooks/)
    relevance/     (with tests/, notebooks/)
    spatial/
  tests/
    e2e/
    fixtures/
    integration/
    unit/
    utils/
  __pycache__/
```

### 2.2 theory_lib/imposition/ and theory_lib/exclusion/

**Status**: Neither `theory_lib/imposition/` nor `theory_lib/exclusion/` exist as separate top-level theory directories. They appear only as references inside other modules (jupyter adapters, output notebook templates, errors.py). These are safe to skip from the delete list.

### 2.3 jupyter/ (entire directory)

```
code/src/model_checker/jupyter/
  __init__.py
  adapters.py
  builder_utils.py
  display.py
  environment.py
  exceptions.py
  interactive.py
  notebook_helpers.py
  types.py
  ui_builders.py
  unicode.py
  utils.py
  debug/
    debug_error_capture.py
    debug_notebook.py
    fix_jupyter_integration.py
    jupyter_test.py
    DEBUGGING.md  README.md
  notebooks/
    basic_demo.ipynb  options_demo.ipynb
  tests/
    fixtures/  integration/  unit/
  NixOS_jupyter.md  README.md  TROUBLESHOOTING.md
  __pycache__/
```

### 2.4 output/notebook/ (entire subdirectory)

```
code/src/model_checker/output/notebook/
  __init__.py
  generator.py
  notebook_writer.py
  streaming_generator.py
  template_loader.py
  README.md
  templates/
    __init__.py  base.py  exclusion.py  imposition.py  logos.py
  tests/
    integration/  unit/
  __pycache__/
```

### 2.5 iterate/ (entire directory)

```
code/src/model_checker/iterate/
  __init__.py
  base.py
  build_example.py
  constraints.py
  core.py
  errors.py
  graph.py
  iterator.py
  metrics.py
  models.py
  statistics.py
  types.py
  tests/
    conftest.py  __init__.py
    e2e/
    fixtures/
    integration/
    unit/
  __pycache__/
```

**WARNING**: `theory_lib/bimodal/iterate.py` imports `from model_checker.iterate.core import BaseModelIterator`. This must be resolved before deleting the `iterate/` module. See Section 6 (Risk Assessment).

### 2.6 Top-level code/tests/ files with logos-specific tests

The following files in `code/tests/` are logos-specific or primarily logos-focused and should be deleted or heavily modified:

**Delete entirely** (logos-specific):
- `code/tests/unit/theory_lib/logos/subtheories/first_order/test_constraints.py`
- `code/tests/unit/theory_lib/logos/subtheories/first_order/test_denotation.py`
- `code/tests/unit/theory_lib/logos/subtheories/first_order/test_operators.py`
- `code/tests/unit/theory_lib/logos/subtheories/first_order/__init__.py`
- `code/tests/unit/theory_lib/logos/subtheories/__init__.py`
- `code/tests/unit/test_first_order_propositions.py` (imports `LogosProposition`, `LogosOperatorRegistry`)
- `code/tests/integration/test_cli_subtheory.py` (logos and exclusion --subtheory flag tests)
- `code/tests/fixtures/example_data.py` (imports `logos.get_theory`)

**Modify** (have both logos and bimodal references, need logos parts stripped):
- `code/tests/conftest.py:140-143` (imports `logos`, calls `logos.get_theory`)
- `code/tests/integration/test_error_handling.py` (multiple logos imports)
- `code/tests/integration/test_performance.py` (logos imports)
- `code/tests/integration/test_system_imports.py:28-31` (imports `logos, bimodal`, asserts logos not None)
- `code/tests/integration/test_timeout_resources.py` (logos imports)
- `code/tests/e2e/test_project_creation.py:118` (references `['logos', 'bimodal']`)
- `code/tests/utils/helpers.py` (logos-defaulting helper functions)
- `code/tests/utils/base.py` (logos as default theory)

---

## 3. Hard Coupling Points (with File:Line References)

### 3.1 theory_lib/__init__.py

| Line | Code | Action |
|------|------|--------|
| 52 | `from model_checker.theory_lib import logos` | **DELETE**: unconditional hard import |
| 63-66 | `AVAILABLE_THEORIES = ['logos', 'bimodal']` | **REPLACE**: reduce to `['bimodal']` |
| 84-105 | `get_examples()` docstring example using 'logos' | **UPDATE**: replace with bimodal example |
| 113-136 | `get_test_examples()` with logos reference | **UPDATE**: docstring cleanup |
| 145-166 | `get_semantic_theories()` | Keep but update docstrings |

**Key action**: Remove line 52 (`from model_checker.theory_lib import logos`) and update `AVAILABLE_THEORIES` to `['bimodal']` only. The `__getattr__` lazy loader at line 366 will still work because it uses `AVAILABLE_THEORIES`.

### 3.2 builder/example.py

| Line | Code | Action |
|------|------|--------|
| 34 | `from ..theory_lib.logos import semantic` | **DELETE**: unused after logos removal |
| 266 | `from .iterate import ModelIterator` | **DELETE**: iterate module being removed |

**Note**: Line 34 imports `semantic` but the symbol appears unused in the rest of the file — the import was likely pulled in for logos-specific initialization that was already refactored away. Verify that `semantic` is not referenced elsewhere in the file before deleting.

### 3.3 builder/runner.py

| Line | Code | Action |
|------|------|--------|
| 82 | `if 'Logos' in semantics_class.__name__:` | **DELETE**: logos-specific branch in `try_single_N_static` |
| 83 | `semantics = semantics_class(combined_settings=settings)` | **DELETE**: logos init pattern |
| 84 | `else:` | **SIMPLIFY**: keep `semantics = semantics_class(settings)` as the only path |
| 206 | `if hasattr(semantics_class, '__name__') and 'Logos' in semantics_class.__name__:` | **DELETE**: in `try_single_N` method |
| 207 | `semantics = semantics_class(combined_settings=settings)` | **DELETE** |
| 208 | `else:` | **SIMPLIFY**: keep `semantics = semantics_class(settings)` |
| 653 | `from model_checker.iterate.metrics import ResultFormatter` | **DELETE**: iterate module gone |

### 3.4 builder/loader.py

| Line | Code | Action |
|------|------|--------|
| 168 | docstring: `"logos", "exclusion"` | **UPDATE**: docstring only |
| 186 | `'LogosProposition': 'logos'` | **DELETE**: logos entry from mapping |
| 198 | `'Logos': 'logos'` | **DELETE**: logos entry from mapping |

### 3.5 builder/project.py

| Line | Code | Action |
|------|------|--------|
| 42 | `def __init__(self, theory: str = 'logos', ...)` | **CHANGE**: default to `'bimodal'` |
| 47 | `subtheories: List of subtheories to load (logos only)` | **UPDATE**: docstring |
| 86 | `if self.theory == 'logos' and self.subtheories:` | **DELETE**: logos-specific subtheory handling |
| 87 | `subtheory_desc = ...` | **DELETE** |

### 3.6 builder/serialize.py

| Line | Code | Action |
|------|------|--------|
| 26 | docstring: `"module_name": "model_checker.theory_lib.logos.operators"` | **UPDATE**: docstring to bimodal |

### 3.7 builder/module.py

| Line | Code | Action |
|------|------|--------|
| 142 | `self.module_flags.save == ['jupyter']` | **UPDATE**: remove jupyter save option check |

### 3.8 builder/tests/ (all logos-specific test files)

These test files reference logos and should be deleted or rewritten to use bimodal:
- `builder/tests/conftest.py:67-70` — imports `logos`, creates theory from logos
- `builder/tests/e2e/test_full_pipeline.py:62,96` — imports from `theory_lib.logos`
- `builder/tests/e2e/test_project_edge_cases.py` — multiple `BuildProject('logos')` calls
- `builder/tests/fixtures/temp_resources.py:107` — imports from `theory_lib.logos`
- `builder/tests/fixtures/test_data.py` — multiple logos imports
- `builder/tests/integration/test_build_module_theories.py` — deeply coupled to logos
- `builder/tests/integration/test_component_integration.py:126-132` — imports logos and bimodal
- `builder/tests/integration/test_generated_projects.py` — logos project generation tests
- `builder/tests/integration/test_package_imports.py` — logos package import tests
- `builder/tests/integration/test_performance.py` — logos performance tests

### 3.9 model_checker/__init__.py

| Line | Code | Action |
|------|------|--------|
| 32 | `"model", "syntactic", "jupyter"` in `__all__` | **REMOVE**: `"jupyter"` |
| 42-53 | `try: from .jupyter import has_jupyter_dependencies ...` | **DELETE**: entire jupyter import block |
| 88-112 | `try: from .jupyter import has_jupyter_dependencies ...` | **DELETE**: entire jupyter import block |

### 3.10 model_checker/__main__.py

| Line | Code | Action |
|------|------|--------|
| 77 | `help='Load semantic theory: logos, exclusion, imposition, bimodal.'` | **UPDATE**: change to bimodal only |

### 3.11 output/__init__.py

| Line | Code | Action |
|------|------|--------|
| 21 | `from .notebook import StreamingNotebookGenerator, NotebookWriter, TemplateLoader` | **DELETE** |
| 38-40 | notebook exports in `__all__` | **DELETE** |

### 3.12 output/manager.py

| Lines | Code | Action |
|-------|------|--------|
| 56-57 | `_module_vars`, `_source_path` (notebook context) | **ASSESS**: may keep or remove |
| 73-86 | `set_module_context()` method with notebook formatter | **SIMPLIFY**: remove notebook parts |
| 206-208 | `if self.config.is_format_enabled(FORMAT_NOTEBOOK):` | **DELETE** |
| 277-304 | `_generate_notebook()` method | **DELETE** |

### 3.13 output/config.py

| Line | Code | Action |
|------|------|--------|
| 10 | docstring: "notebook" | **UPDATE** |
| 34 | `format_name: Format to check ('markdown', 'json', 'notebook')` | **UPDATE** |
| 65 | `formats = ['markdown', 'json', 'notebook']` | **UPDATE**: remove 'notebook' |
| 73-74 | `elif fmt in ('notebook', 'jupyter'): formats.append('notebook')` | **DELETE** |

### 3.14 theory_lib/bimodal/iterate.py (CRITICAL)

| Line | Code | Action |
|------|------|--------|
| 13 | `from model_checker.iterate.core import BaseModelIterator` | **REFACTOR**: inline BaseModelIterator or copy it into bimodal/iterate.py |

**Decision required**: Either (a) inline the `BaseModelIterator` class into `bimodal/iterate.py`, making it self-contained, or (b) delete `bimodal/iterate.py` as well (since the task says OracleProvider needs one countermodel, not iteration). Option (b) is simpler but requires also removing `test_iterate.py` from bimodal tests.

### 3.15 theory_lib/bimodal/__init__.py

| Line | Code | Action |
|------|------|--------|
| 59 | `from .iterate import BimodalModelIterator, iterate_example` | **DELETE or KEEP**: depends on whether bimodal iterate is preserved |

### 3.16 theory_lib/errors.py

| Lines | Code | Action |
|-------|------|--------|
| 164-189 | `WitnessSemanticError`, `WitnessPredicateError` (exclusion-specific) | **REMOVE**: exclusion theory errors |
| 217-224 | `ImpositionSemanticError`, `ImpositionOperationError` | **REMOVE**: imposition theory errors |

### 3.17 theory_lib/types.py

| Line | Code | Action |
|------|------|--------|
| 117-123 | `class ImpositionSemantics(Protocol):` | **REMOVE**: imposition protocol |

### 3.18 theory_lib/__init__.py (registry functions)

The functions `get_examples()`, `get_test_examples()`, `get_semantic_theories()` use an AVAILABLE_THEORIES list — update to bimodal-only. The unused registry+lazy-loading infrastructure can be simplified.

### 3.19 theory_lib/tests/test_meta_data.py

| Line | Code | Action |
|------|------|--------|
| 95 | `["logos", "exclusion", "imposition", "bimodal"]` | **UPDATE**: update expected theories |

---

## 4. Dependency Analysis (pyproject.toml)

### Current Dependencies

```toml
dependencies = [
    "z3-solver>=4.8.0",  # Keep — core dependency
    "networkx>=2.0",     # REMOVE — only used in iterate/graph.py and jupyter/adapters.py
]

[project.optional-dependencies]
jupyter = [
    "ipywidgets>=7.0.0",  # REMOVE — jupyter module being deleted
    "matplotlib>=3.0.0",  # REMOVE — only in jupyter/display.py
    "networkx>=2.0",      # REMOVE
    "jupyter",            # REMOVE
    "ipython",            # REMOVE
]
cvc5 = [
    "cvc5>=1.1.0",        # REMOVE — only used in iterate/constraints.py and builder/example.py:108
]
all = [
    # REMOVE all entries except z3-solver
]
```

### Dependencies to Remove

| Dependency | Current Use | Action |
|------------|-------------|--------|
| `networkx` | `iterate/graph.py`, `jupyter/adapters.py` | **REMOVE**: both consuming modules deleted |
| `matplotlib` | `jupyter/display.py` | **REMOVE**: jupyter module deleted |
| `ipywidgets` | `jupyter/interactive.py`, `jupyter/__init__.py` | **REMOVE**: jupyter deleted |
| `jupyter` | jupyter module | **REMOVE** |
| `ipython` | jupyter display | **REMOVE** |
| `cvc5` | `iterate/constraints.py`, `builder/example.py:108` | **REMOVE**: iterate deleted; also remove `if requested_solver in ("z3", "cvc5")` check |

### Post-Cleanup pyproject.toml Structure

```toml
dependencies = [
    "z3-solver>=4.8.0",
]

# Remove all optional-dependencies sections
# Remove pytest markers for notebook/jupyter tests
```

---

## 5. Preservation Verification

### theory_lib/bimodal/ — Confirmed to Exist

```
code/src/model_checker/theory_lib/bimodal/
  __init__.py          (preserve, but strip iterate import if bimodal/iterate.py deleted)
  examples.py          (PRESERVE — 43 example evaluation suite)
  iterate.py           (DECISION NEEDED — depends on BaseModelIterator from iterate/)
  operators.py         (PRESERVE)
  profile_abundance.py (minor utility, safe to keep or delete)
  semantic.py          (PRESERVE — all Z3 constraint builders)
  CITATION.md  LICENSE.md  README.md  VERSION
  docs/                (docs only, safe to keep or delete)
  semantic/
    __init__.py
    witness_constraints.py  (PRESERVE — used by bimodal tests)
    witness_registry.py     (PRESERVE — used by bimodal tests)
  tests/               (PRESERVE ENTIRE TEST SUITE)
    __init__.py
    e2e/test_cli_execution.py
    integration/
      test_api_consistency.py
      test_data_extraction.py
      test_injection.py
      test_iterate.py         (KEEP or DELETE — depends on iterate decision)
      test_strict_semantics.py
      test_until_since_integration.py
    unit/
      test_bimodal.py         (43 examples)
      test_foralltime.py
      test_frame_constraints.py
      test_modal_witness_integration.py
      test_until_since.py
      test_witness_constraints.py
      test_witness_registry.py
```

---

## 6. Risk Assessment

### HIGH Risk: bimodal/iterate.py → model_checker.iterate.core dependency

- `theory_lib/bimodal/iterate.py:13`: `from model_checker.iterate.core import BaseModelIterator`
- `theory_lib/bimodal/__init__.py:59`: `from .iterate import BimodalModelIterator, iterate_example`
- `bimodal/tests/integration/test_iterate.py` imports and tests `BimodalModelIterator`

**Impact**: If `iterate/` is deleted without first handling this, the entire bimodal package will fail to import (including ALL 175 tests).

**Mitigation options**:

**Option A** (Simplest — recommended): Delete `bimodal/iterate.py`, remove from `bimodal/__init__.py`, and delete `bimodal/tests/integration/test_iterate.py`. The remaining 172 tests don't use iterate. The 43 example tests in `test_bimodal.py` (which form the correctness gate) do not use iterate.

**Option B** (Self-contained): Copy `BaseModelIterator` implementation from `iterate/core.py` into `bimodal/iterate.py`. This preserves the iteration feature but adds ~400 lines of code to maintain.

The task description says "OracleProvider needs one countermodel, not iteration" — this confirms **Option A is correct**.

### HIGH Risk: output/__init__.py imports notebook module

- `output/__init__.py:21`: `from .notebook import StreamingNotebookGenerator, NotebookWriter, TemplateLoader`
- Any code importing from `model_checker.output` will fail if this line exists after notebook/ is deleted
- Must update `output/__init__.py` before or simultaneously with deleting `output/notebook/`

### MEDIUM Risk: model_checker/__init__.py jupyter imports

- Lines 42-53 and 88-112 import from `.jupyter`
- After jupyter/ is deleted, any import of `model_checker` will fail silently in try/except or loudly if the import guard is incomplete
- Must remove these import blocks before deleting `jupyter/`

### MEDIUM Risk: builder/example.py line 266

- `from .iterate import ModelIterator` — note this imports from `.iterate` (within builder package), not `model_checker.iterate`
- There is no `builder/iterate.py` currently; this import will already fail at runtime
- Safe to remove (the `find_next_model` method at line 250 calls this — that whole method should be removed)

### LOW Risk: builder/tests/ and code/tests/ test failures

- All builder tests import logos theory — they will fail with ImportError after logos removal
- These tests need to be rewritten for bimodal or deleted
- They are NOT part of the correctness gate

### LOW Risk: output/manager.py notebook formatter registration

- `output/manager.py` registers a notebook formatter in `_initialize_formatters()`
- The formatter is initialized from `output/notebook/__init__.py`
- Check `manager.py` for where `FORMAT_NOTEBOOK` is used as a dict key in formatters initialization

### LOW Risk: theory_lib/errors.py removing exclusion/imposition classes

- Some builder tests import `WitnessSemanticError` or `ImpositionSemanticError`
- These are in `theory_lib/errors.py` — safe to remove error classes since they reference deleted theories
- Check test imports before removing

---

## 7. Current Test Baseline

### Gate Test: bimodal/tests/ — ALL PASS

```
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v
175 passed, 2 warnings in 62.30s
```

### Test Breakdown by Subdirectory

| Directory | Count | Notes |
|-----------|-------|-------|
| `tests/unit/test_bimodal.py` | 43 | Example-based tests (core correctness gate) |
| `tests/unit/test_foralltime.py` | ~10 | ForAll time operator tests |
| `tests/unit/test_frame_constraints.py` | ~15 | Frame constraint tests |
| `tests/unit/test_modal_witness_integration.py` | ~15 | Witness modal integration |
| `tests/unit/test_until_since.py` | ~20 | Until/Since operator tests |
| `tests/unit/test_witness_constraints.py` | ~20 | Witness constraint tests |
| `tests/unit/test_witness_registry.py` | ~20 | Witness registry tests |
| `tests/integration/test_api_consistency.py` | ~5 | API consistency tests |
| `tests/integration/test_data_extraction.py` | ~10 | Data extraction tests |
| `tests/integration/test_injection.py` | ~5 | Z3 injection tests |
| `tests/integration/test_iterate.py` | 3 | Iteration tests (depends on iterate/) |
| `tests/integration/test_strict_semantics.py` | ~10 | Strict semantics tests |
| `tests/integration/test_until_since_integration.py` | ~10 | Until/Since integration |
| `tests/e2e/test_cli_execution.py` | 1 | CLI execution test |
| **Total** | **175** | |

### Iterate-dependent tests (to be deleted under Option A)

`tests/integration/test_iterate.py` (3 tests):
- `test_basic_iteration`
- `test_iterate_example_function`
- `test_bimodal_specific_differences`

After deletion: **172 tests** must still pass.

---

## 8. Recommended Implementation Order

To avoid breaking the test gate at any intermediate step:

1. **Phase 1 — Core coupling fixes** (most dangerous, do first with tests running after each):
   a. Fix `theory_lib/__init__.py:52` — remove `from model_checker.theory_lib import logos`
   b. Fix `builder/example.py:34` — remove `from ..theory_lib.logos import semantic`
   c. Fix `builder/runner.py:82,206` — remove `if 'Logos' in semantics_class.__name__` branches
   d. Fix `model_checker/__init__.py` — remove jupyter import blocks
   e. Fix `output/__init__.py:21` — remove notebook import line

2. **Phase 2 — Remove bimodal iterate dependency** (before deleting iterate/):
   a. Delete `bimodal/iterate.py`
   b. Remove iterate import from `bimodal/__init__.py:59`
   c. Delete `bimodal/tests/integration/test_iterate.py`

3. **Phase 3 — Delete modules** (after coupling fixes):
   a. Delete `iterate/` entire directory
   b. Delete `jupyter/` entire directory
   c. Delete `output/notebook/` entire directory
   d. Delete `theory_lib/logos/` entire directory

4. **Phase 4 — Clean up references** (after deletions):
   a. Update `theory_lib/__init__.py` — AVAILABLE_THEORIES = ['bimodal']
   b. Update `output/__init__.py` — remove notebook exports
   c. Update `output/manager.py` — remove notebook generation
   d. Update `output/config.py` — remove notebook format
   e. Update `builder/loader.py` — remove logos mappings
   f. Update `builder/project.py` — change default theory to 'bimodal'
   g. Update `theory_lib/errors.py` — remove exclusion/imposition error classes
   h. Update `theory_lib/types.py` — remove ImpositionSemantics protocol
   i. Update `model_checker/__main__.py` — update help text

5. **Phase 5 — Clean tests** (last):
   a. Delete/rewrite `code/tests/` logos-specific files
   b. Delete/rewrite `builder/tests/` logos-specific files
   c. Run full bimodal gate test

6. **Phase 6 — pyproject.toml**:
   a. Remove networkx, matplotlib, ipywidgets, jupyter, ipython, cvc5 dependencies
   b. Remove optional-dependencies sections

---

## 9. Summary Statistics

| Category | Count |
|----------|-------|
| Directories to delete | 5 (logos, iterate, jupyter, output/notebook, logos subtheories) |
| Files to delete (top-level tests) | ~15 files in code/tests/ |
| Files to modify (source) | ~12 source files |
| Files to modify (tests) | ~20 test files in builder/tests and code/tests |
| Coupling points | 30+ specific file:line references |
| Dependencies to remove from pyproject.toml | 5 packages (networkx, matplotlib, ipywidgets, jupyter, ipython, cvc5) |
| Current test baseline | 175 passing |
| Post-cleanup target | 172 passing (3 iterate tests removed) |
