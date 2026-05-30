# Implementation Plan: Fix output/notebook test failures

**Task**: 66 - Fix output/notebook test failures (6 failing tests)
**Date**: 2026-03-30
**Session**: sess_1774916194_ea117d

## Phase 1: Create missing template modules [COMPLETED]

Create `exclusion.py` and `imposition.py` in `templates/` directory, each subclassing `DirectNotebookTemplate` following the pattern of `logos.py`.

**Files**:
- CREATE: `code/src/model_checker/output/notebook/templates/exclusion.py`
- CREATE: `code/src/model_checker/output/notebook/templates/imposition.py`

**Fixes**: `test_get_template_for_witness_semantics`, `test_get_template_for_imposition_semantics`

## Phase 2: Fix stale API call in integration test [COMPLETED]

Fix `test_template_loading_for_different_theories` to use correct method name `get_template_for_class()` with mock class objects instead of strings, and fix expected template class names.

**Files**:
- MODIFY: `code/src/model_checker/output/notebook/tests/integration/test_notebook_generation.py` (lines 188-212)

**Fixes**: `test_template_loading_for_different_theories`

## Phase 3: Fix wrong mock paths in integration test [COMPLETED]

Change mock decorator paths from `model_checker.notebook.streaming_generator` to `model_checker.output.notebook.streaming_generator`.

**Files**:
- MODIFY: `code/src/model_checker/output/notebook/tests/integration/test_notebook_generation.py` (lines 46, 142)

**Fixes**: `test_generate_notebook_stream_creates_file`, `test_template_placeholder_substitution`

## Phase 4: Fix test design for missing template test [COMPLETED]

Mock `_discover_template_path` to return a controlled non-existent path so the `FileNotFoundError` code path is exercised instead of hitting `ValueError` from theory_lib discovery.

**Files**:
- MODIFY: `code/src/model_checker/output/notebook/tests/integration/test_notebook_generation.py` (lines 91-118)

**Fixes**: `test_generate_notebook_raises_on_missing_template`

## Phase 5: Verification [COMPLETED]

Run the full notebook test suite and confirm all 14 tests pass.
