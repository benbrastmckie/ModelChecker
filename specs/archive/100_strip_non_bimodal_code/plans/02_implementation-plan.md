# Implementation Plan: Strip Non-Bimodal Code

- **Task**: 100 - Strip non-bimodal code and fix coupling
- **Status**: [COMPLETED]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: specs/100_strip_non_bimodal_code/reports/01_codebase-audit.md
- **Artifacts**: plans/02_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Strip all non-bimodal theories (logos, iterate, jupyter, output/notebook) from the ModelChecker codebase and fix all hard coupling points that reference deleted modules. The operation follows a strict ordering: fix coupling points first (so imports survive), remove the bimodal iterate dependency, delete module directories, clean residual references, clean tests, and finally clean pyproject.toml dependencies. The definition of done is: 172 bimodal tests pass (175 baseline minus 3 iterate tests removed) and all unit tests in `theory_lib/bimodal/tests/unit/` pass.

### Research Integration

The codebase audit (01_codebase-audit.md) mapped 30+ coupling points with exact file:line references, identified 5 module directories to delete, confirmed that `imposition/` and `exclusion/` do not exist as standalone directories, and flagged the critical `bimodal/iterate.py -> iterate/core.py` dependency. The recommended resolution is Option A: delete `bimodal/iterate.py` entirely since the OracleProvider needs single countermodels, not iteration. The current bimodal test baseline is 175 passing tests; 3 are iterate-dependent and will be removed, leaving a target of 172 tests.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No actionable ROADMAP.md items found (template only).

## Goals & Non-Goals

**Goals**:
- Remove all logos theory code and its subtheories
- Remove jupyter module, output/notebook module, and iterate module
- Fix all hard coupling points so the package imports cleanly
- Remove unused dependencies from pyproject.toml
- Preserve the bimodal theory, its tests, examples, operators, and Z3 constraint builders
- Pass the gate: 172 bimodal tests and all bimodal unit tests

**Non-Goals**:
- Restructuring the package as bmlogic-oracle (task 101)
- Implementing OracleProvider (task 103)
- Adding new tests or features
- Modifying bimodal theory logic or Z3 constraints
- Cleaning builder/ beyond coupling fixes (task 104 scope)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Deleting iterate/ before removing bimodal/iterate.py dependency breaks all bimodal imports | H | H | Phase 2 removes bimodal iterate dependency BEFORE Phase 3 deletes iterate/ |
| Deleting output/notebook/ before fixing output/__init__.py breaks all output imports | H | H | Phase 1 fixes output/__init__.py BEFORE Phase 3 deletes notebook/ |
| Deleting jupyter/ before fixing model_checker/__init__.py breaks package import | H | M | Phase 1 removes jupyter import blocks BEFORE Phase 3 deletes jupyter/ |
| Test files import logos theory and cause import errors | M | H | Phase 5 cleans test files after source deletions |
| Undiscovered coupling point breaks bimodal tests | M | L | Run gate tests after each phase; roll back phase if tests fail |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel. This plan is fully sequential because each phase depends on the prior phase to maintain import integrity.

---

### Phase 1: Fix Hard Coupling Points [COMPLETED]

**Goal**: Remove all hard imports and references to logos, jupyter, and notebook from source files so that module deletions in Phase 3 do not break imports.

**Tasks**:
- [x] **theory_lib/__init__.py**: Delete line 52 (`from model_checker.theory_lib import logos`)
- [x] **theory_lib/__init__.py**: Update `AVAILABLE_THEORIES` (lines 63-66) to `['bimodal']` only
- [x] **theory_lib/__init__.py**: Update docstrings (module docstring, `get_examples()`, `get_test_examples()`) to remove logos references and use bimodal examples
- [x] **builder/example.py**: Delete line 34 (`from ..theory_lib.logos import semantic`)
- [x] **builder/example.py**: Delete line 266 (`from .iterate import ModelIterator`) and the `find_next_model` method that uses it
- [x] **builder/runner.py**: Simplify lines 82-85 -- remove `if 'Logos' in semantics_class.__name__:` branch, keep only `semantics = semantics_class(settings)`
- [x] **builder/runner.py**: Simplify lines 206-209 -- remove `if hasattr(semantics_class, '__name__') and 'Logos' in semantics_class.__name__:` branch, keep only `semantics = semantics_class(settings)`
- [x] **builder/runner.py**: Delete line 653 (`from model_checker.iterate.metrics import ResultFormatter`) and surrounding block that uses it
- [x] **model_checker/__init__.py**: Remove `"jupyter"` from `__all__` list (line 32)
- [x] **model_checker/__init__.py**: Delete jupyter import block lines 42-54 (try/except with `has_jupyter_dependencies`)
- [x] **model_checker/__init__.py**: Delete jupyter import block lines 88-112 (conditional jupyter imports)
- [x] **output/__init__.py**: Delete line 21 (`from .notebook import StreamingNotebookGenerator, NotebookWriter, TemplateLoader`)
- [x] **output/__init__.py**: Delete notebook entries from `__all__` (lines 37-40)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `code/src/model_checker/theory_lib/__init__.py` - Remove logos import, update AVAILABLE_THEORIES, update docstrings
- `code/src/model_checker/builder/example.py` - Remove logos import, remove iterate import and find_next_model
- `code/src/model_checker/builder/runner.py` - Remove Logos-specific branching (2 locations), remove iterate metrics import
- `code/src/model_checker/__init__.py` - Remove jupyter from __all__ and both jupyter import blocks
- `code/src/model_checker/output/__init__.py` - Remove notebook import and exports

**Verification**:
- `PYTHONPATH=code/src python -c "from model_checker.theory_lib import bimodal; print('theory_lib OK')"` succeeds
- `PYTHONPATH=code/src python -c "from model_checker.output import OutputManager; print('output OK')"` succeeds
- `PYTHONPATH=code/src python -c "import model_checker; print('package OK')"` succeeds
- Bimodal gate tests still pass: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`

---

### Phase 2: Remove Bimodal Iterate Dependency [COMPLETED]

**Goal**: Sever the bimodal package's dependency on the iterate module so that iterate/ can be safely deleted in Phase 3.

**Tasks**:
- [x] **theory_lib/bimodal/iterate.py**: Delete this file entirely (per Option A from research -- OracleProvider needs one countermodel, not iteration)
- [x] **theory_lib/bimodal/__init__.py**: Remove line 59 (`from .iterate import BimodalModelIterator, iterate_example`) and any other iterate references
- [x] **theory_lib/bimodal/tests/integration/test_iterate.py**: Delete this file entirely (3 tests removed)

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/iterate.py` - Delete
- `code/src/model_checker/theory_lib/bimodal/__init__.py` - Remove iterate import
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` - Delete

**Verification**:
- `PYTHONPATH=code/src python -c "from model_checker.theory_lib.bimodal import BimodalSemantics; print('bimodal OK')"` succeeds
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` passes (target: 172 tests)

---

### Phase 3: Delete Module Directories [COMPLETED]

**Goal**: Remove all non-bimodal module directories from the codebase.

**Tasks**:
- [x] Delete `code/src/model_checker/theory_lib/logos/` entire directory tree
- [x] Delete `code/src/model_checker/iterate/` entire directory tree
- [x] Delete `code/src/model_checker/jupyter/` entire directory tree
- [x] Delete `code/src/model_checker/output/notebook/` entire directory tree

**Timing**: 15 minutes

**Depends on**: 2

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/` - Delete entire directory
- `code/src/model_checker/iterate/` - Delete entire directory
- `code/src/model_checker/jupyter/` - Delete entire directory
- `code/src/model_checker/output/notebook/` - Delete entire directory

**Verification**:
- Directories no longer exist: `ls code/src/model_checker/theory_lib/logos/ code/src/model_checker/iterate/ code/src/model_checker/jupyter/ code/src/model_checker/output/notebook/` all return "No such file or directory"
- `PYTHONPATH=code/src python -c "import model_checker; print('package OK')"` succeeds
- Bimodal gate tests still pass: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` (172 tests)

---

### Phase 4: Clean Residual Source References [COMPLETED]

**Goal**: Update all remaining source files that reference deleted theories, modules, or features.

**Tasks**:
- [x] **builder/loader.py**: Remove `'LogosProposition': 'logos'` (line 186) and `'Logos': 'logos'` (line 198) from mapping dicts; update docstring (line 168) to remove logos/exclusion references
- [x] **builder/project.py**: Change default theory from `'logos'` to `'bimodal'` (line 42); remove logos-specific subtheory handling (lines 86-87); update docstring
- [x] **builder/serialize.py**: Update docstring (line 26) to use bimodal example instead of logos
- [x] **builder/module.py**: Remove jupyter save option check (line 142) if it only applies to notebook/jupyter output
- [x] **output/manager.py**: Delete `_generate_notebook()` method (lines 277-304); delete notebook format check (lines 206-208); simplify `set_module_context()` to remove notebook parts (lines 73-86)
- [x] **output/config.py**: Remove `'notebook'` from formats list (line 65); delete notebook/jupyter format handling (lines 73-74); update docstrings
- [x] **theory_lib/errors.py**: Remove logos-specific `WitnessSemanticError` parent class and `ImpositionSemanticError`, `ImpositionOperationError`; keep bimodal-used `WitnessRegistryError`, `WitnessConstraintError`, `WitnessPredicateError` as direct subclasses of `WitnessError`
- [x] **theory_lib/types.py**: Remove `ImpositionSemantics` protocol class (lines 117-123) and `SubtheoryProtocol`
- [x] **theory_lib/__init__.py**: Simplify registry functions that use AVAILABLE_THEORIES; remove dead code paths for non-existent theories
- [x] **theory_lib/tests/test_meta_data.py**: Update expected theories list (line 95) from `["logos", "exclusion", "imposition", "bimodal"]` to `["bimodal"]`
- [x] **model_checker/__main__.py**: Update help text (line 77) from `'logos, exclusion, imposition, bimodal'` to `'bimodal'`

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `code/src/model_checker/builder/loader.py` - Remove logos mappings, update docstrings
- `code/src/model_checker/builder/project.py` - Change default theory, remove subtheory handling
- `code/src/model_checker/builder/serialize.py` - Update docstring
- `code/src/model_checker/builder/module.py` - Remove jupyter save option
- `code/src/model_checker/output/manager.py` - Remove notebook generation
- `code/src/model_checker/output/config.py` - Remove notebook format
- `code/src/model_checker/theory_lib/errors.py` - Remove exclusion/imposition error classes
- `code/src/model_checker/theory_lib/types.py` - Remove ImpositionSemantics protocol
- `code/src/model_checker/theory_lib/__init__.py` - Simplify registry
- `code/src/model_checker/theory_lib/tests/test_meta_data.py` - Update expected theories
- `code/src/model_checker/__main__.py` - Update help text

**Verification**:
- `PYTHONPATH=code/src python -c "from model_checker.builder.loader import TheoryLoader; print('loader OK')"` succeeds
- `PYTHONPATH=code/src python -c "from model_checker.output.manager import OutputManager; print('manager OK')"` succeeds
- Bimodal gate tests still pass: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` (172 tests)

---

### Phase 5: Clean Test Files [COMPLETED]

**Goal**: Remove or rewrite test files that reference logos, iterate, jupyter, or other deleted modules.

**Tasks**:
- [x] **Delete entirely** (logos-specific test files in code/tests/):
  - `code/tests/unit/theory_lib/logos/` (entire directory tree including subtheories/)
  - `code/tests/unit/test_first_order_propositions.py`
  - `code/tests/integration/test_cli_subtheory.py`
  - `code/tests/fixtures/example_data.py`
- [x] **Modify** (strip logos references, keep bimodal):
  - `code/tests/conftest.py` - Remove logos imports (lines 140-143); update to use bimodal as default theory
  - `code/tests/integration/test_error_handling.py` - Remove logos imports and tests
  - `code/tests/integration/test_performance.py` - Remove logos imports and tests
  - `code/tests/integration/test_system_imports.py` - Remove logos import assertion (lines 28-31); keep bimodal assertion
  - `code/tests/integration/test_timeout_resources.py` - Remove logos imports
  - `code/tests/e2e/test_project_creation.py` - Remove logos from theory list (line 118)
  - `code/tests/utils/helpers.py` - Change logos defaults to bimodal
  - `code/tests/utils/base.py` - Change logos defaults to bimodal
- [x] **Delete or rewrite** (builder test files):
  - `code/src/model_checker/builder/tests/conftest.py` - Remove logos imports (lines 67-70), use bimodal
  - `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` - Remove logos imports
  - `code/src/model_checker/builder/tests/e2e/test_project_edge_cases.py` - Change `BuildProject('logos')` to `BuildProject('bimodal')`
  - `code/src/model_checker/builder/tests/fixtures/temp_resources.py` - Remove logos imports
  - `code/src/model_checker/builder/tests/fixtures/test_data.py` - Remove logos imports
  - `code/src/model_checker/builder/tests/integration/test_build_module_theories.py` - Rewrite for bimodal
  - `code/src/model_checker/builder/tests/integration/test_component_integration.py` - Remove logos references
  - `code/src/model_checker/builder/tests/integration/test_generated_projects.py` - Remove logos project tests
  - `code/src/model_checker/builder/tests/integration/test_package_imports.py` - Remove logos import tests
  - `code/src/model_checker/builder/tests/integration/test_performance.py` - Remove logos performance tests

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- Multiple files in `code/tests/` - Delete logos-specific files, modify mixed files
- Multiple files in `code/src/model_checker/builder/tests/` - Remove logos references

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` passes (172 tests)
- `PYTHONPATH=code/src pytest code/tests/ -v --ignore=code/tests/unit/theory_lib/logos` runs without ImportError (some tests may fail for non-logos reasons; logos ImportErrors must be zero)

---

### Phase 6: Clean pyproject.toml Dependencies [COMPLETED]

**Goal**: Remove all dependencies that are only used by deleted modules.

**Tasks**:
- [x] Remove `networkx>=2.0` from `dependencies` list
- [x] Remove entire `[project.optional-dependencies]` `jupyter` group (ipywidgets, matplotlib, networkx, jupyter, ipython)
- [x] Remove entire `[project.optional-dependencies]` `cvc5` group
- [x] Update `[project.optional-dependencies]` `all` group to only include z3-solver
- [x] Remove any pytest markers for notebook/jupyter tests (none existed)
- [x] Also remove `cvc5` import check in `builder/example.py` line 108 (`if requested_solver in ("z3", "cvc5")` changed to `== "z3"`)
- [x] Verify `z3-solver>=4.8.0` remains as the core dependency

**Timing**: 30 minutes

**Depends on**: 5

**Files to modify**:
- `code/pyproject.toml` - Remove unused dependencies and optional-dependency groups
- `code/src/model_checker/builder/example.py` - Remove cvc5 solver check if present

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` passes (172 tests)
- `pip install -e code/` succeeds with only z3-solver as dependency
- `python -c "import model_checker"` succeeds after fresh install

## Testing & Validation

- [ ] Gate test: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` -- 172 tests pass
- [ ] Unit test gate: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/ -v` -- all pass
- [ ] Package import: `PYTHONPATH=code/src python -c "import model_checker"` succeeds
- [ ] Theory import: `PYTHONPATH=code/src python -c "from model_checker.theory_lib import bimodal"` succeeds
- [ ] No logos/iterate/jupyter directories exist under `code/src/model_checker/`
- [ ] No logos imports in any remaining source file: `grep -r "from.*logos" code/src/model_checker/ --include="*.py"` returns empty
- [ ] No iterate imports in any remaining source file: `grep -r "from.*iterate" code/src/model_checker/ --include="*.py"` returns empty
- [ ] No jupyter imports in any remaining source file: `grep -r "from.*jupyter" code/src/model_checker/ --include="*.py"` returns empty (except maybe conditional checks that guard against missing packages)

## Artifacts & Outputs

- `specs/100_strip_non_bimodal_code/plans/02_implementation-plan.md` (this file)
- `specs/100_strip_non_bimodal_code/summaries/02_strip-non-bimodal-summary.md` (on completion)

## Rollback/Contingency

All deletions are tracked by git. If any phase breaks the bimodal gate tests:
1. `git stash` or `git checkout -- .` to revert the current phase
2. Investigate which coupling point was missed
3. Fix the coupling point before re-attempting the phase

For complete rollback: `git log` to find the commit before task 100 implementation began, and `git revert` the relevant commits.
