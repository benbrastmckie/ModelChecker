# Implementation Plan: Restructure as bimodal-logic pip package

- **Task**: 101 - Restructure as bimodal-logic pip package
- **Status**: [COMPLETED]
- **Effort**: 2.5 hours
- **Dependencies**: 100 (completed)
- **Research Inputs**: specs/101_restructure_pip_package/reports/01_restructure-research.md
- **Artifacts**: plans/01_restructure-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Restructure the ModelChecker codebase as a pip-installable `bimodal-logic` package by overhauling `code/pyproject.toml` metadata, creating a thin `bimodal_logic/` facade package under `code/src/`, and narrowing pytest test paths. The existing `model_checker/` package and all its internal imports remain unchanged (ADR Decision 3 Rec 1). The result is a dual-package layout where `pip install bimodal-logic` installs both `model_checker` (infrastructure) and `bimodal_logic` (public facade with stubs for tasks 102/103).

### Research Integration

Research report `01_restructure-research.md` provided:
- Complete current pyproject.toml audit (name, version, classifiers, dependencies already clean after task 100)
- Directory structure map confirming dual-package layout under `code/src/`
- Import dependency analysis: 58 absolute `from model_checker...` imports must stay unchanged
- Risk assessment: 8 risks identified, all LOW except console script naming (MEDIUM, deferred to task 104)
- Proposed pyproject.toml content with all fields specified
- Verification steps for editable install and import testing

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Rename pip package from `model-checker` to `bimodal-logic` with updated metadata
- Create thin `bimodal_logic/` package with stub files for tasks 102/103
- Add `bimodal_harness.oracle_providers` entry point stub
- Narrow pytest testpaths to bimodal-only tests
- Verify editable install succeeds and `import bimodal_logic` works
- Clean up stale egg-info and redundant optional dependency groups

**Non-Goals**:
- Modifying any existing `model_checker/` imports or directory structure
- Implementing Z3OracleProvider (task 103)
- Implementing translation/serialization logic (task 102)
- Removing the `model-checker` console script (deferred to task 104)
- Fixing the pre-existing BM_CM_1 test failure
- Cleaning up jupyter/cvc5 references in runtime code (cosmetic, not blocking)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Dual-package discovery failure | H | L | Verify both packages appear in `pip show`; `packages.find where=["src"]` handles this automatically |
| Stale egg-info causes confusion | L | M | Delete `code/src/model_checker.egg-info/` before editable install |
| Entry point stub import error | M | L | Verify `from bimodal_logic.provider import Z3OracleProvider` works after install |
| Test path narrowing hides failures | M | L | Run full bimodal test suite; non-bimodal theory_lib tests are secondary |
| Python version bump breaks CI | L | L | System is Python 3.12; >=3.10 is safe |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Overhaul pyproject.toml [COMPLETED]

**Goal**: Update all package metadata, entry points, dependencies, and pytest config in `code/pyproject.toml`.

**Tasks**:
- [x] Change `name` from `"model-checker"` to `"bimodal-logic"`
- [x] Change `version` from `"1.2.12"` to `"0.1.0"`
- [x] Update `description` to: `"Z3-based bimodal logic oracle: temporal and modal reasoning for the bimodal_harness."`
- [x] Update `classifiers` to include Python 3.10, 3.11, 3.12 and add `Topic :: Scientific/Engineering :: Mathematics` and `Topic :: Software Development :: Libraries :: Python Modules`
- [x] Update `keywords` to bimodal-specific terms: `["bimodal logic", "temporal logic", "modal logic", "Z3", "SMT", "model checking", "oracle", "theorem prover"]`
- [x] Change `requires-python` from `">=3.8"` to `">=3.10"`
- [x] Remove the `[project.optional-dependencies]` section (the `all` group is redundant with core deps)
- [x] Add entry point group: `[project.entry-points."bimodal_harness.oracle_providers"]` with `z3_base = "bimodal_logic.provider:Z3OracleProvider"`
- [x] Update `testpaths` from `["src/model_checker/theory_lib"]` to `["src/model_checker/theory_lib/bimodal/tests"]`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `code/pyproject.toml` - Full metadata overhaul

**Verification**:
- `python -c "import tomllib; t = tomllib.load(open('code/pyproject.toml', 'rb')); assert t['project']['name'] == 'bimodal-logic'"` (or manual inspection)
- All required fields present in the TOML file

---

### Phase 2: Create bimodal_logic package stubs [COMPLETED]

**Goal**: Create the thin `bimodal_logic/` facade package with 4 stub files under `code/src/`.

**Tasks**:
- [x] Create `code/src/bimodal_logic/` directory
- [x] Create `code/src/bimodal_logic/__init__.py` with docstring, import of `Z3OracleProvider` from `.provider`, and `__all__ = ["Z3OracleProvider"]`
- [x] Create `code/src/bimodal_logic/provider.py` with docstring and stub `Z3OracleProvider` class (empty `pass` body, docstring noting task 103)
- [x] Create `code/src/bimodal_logic/translation.py` with docstring only (stub for task 102)
- [x] Create `code/src/bimodal_logic/serialization.py` with docstring only (stub for task 102)

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `code/src/bimodal_logic/__init__.py` - Create new file
- `code/src/bimodal_logic/provider.py` - Create new file
- `code/src/bimodal_logic/translation.py` - Create new file
- `code/src/bimodal_logic/serialization.py` - Create new file

**Verification**:
- All 4 files exist under `code/src/bimodal_logic/`
- `python -c "import sys; sys.path.insert(0, 'code/src'); from bimodal_logic.provider import Z3OracleProvider; print(Z3OracleProvider)"` succeeds

---

### Phase 3: Clean up stale artifacts [COMPLETED]

**Goal**: Remove the stale `model_checker.egg-info` directory so it does not conflict with the new package metadata.

**Tasks**:
- [x] Delete `code/src/model_checker.egg-info/` directory (stale from pre-task-100 era; will be regenerated as `bimodal_logic.egg-info` on install)
- [x] Verify no other stale `.egg-info` directories exist under `code/src/`

**Timing**: 5 minutes

**Depends on**: 2

**Files to modify**:
- `code/src/model_checker.egg-info/` - Delete entire directory

**Verification**:
- `ls code/src/*.egg-info` returns nothing or only expected entries
- No import errors from lingering metadata

---

### Phase 4: Editable install and full verification [COMPLETED]

**Goal**: Verify the complete restructure by performing an editable install and running all verification checks.

**Tasks**:
- [x] Run `cd code && pip install -e .` (editable install)
- [x] Verify `import bimodal_logic` works: `python -c "import bimodal_logic; print(bimodal_logic.__all__)"`
- [x] Verify `from bimodal_logic.provider import Z3OracleProvider` works
- [x] Verify `import model_checker` still works: `python -c "import model_checker"`
- [x] Verify `pip show bimodal-logic` shows correct metadata (name, version 0.1.0)
- [x] Run bimodal test suite: `cd code && PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal/tests/ -v` and confirm 171 pass, 1 pre-existing failure (BM_CM_1)
- [x] Verify the narrowed testpaths work: `cd code && pytest` runs only bimodal tests
- [x] Verify entry point is registered: `python -c "from importlib.metadata import entry_points; eps = entry_points(group='bimodal_harness.oracle_providers'); print([ep.name for ep in eps])"` should include `z3_base`

**Timing**: 45 minutes (includes test run time)

**Depends on**: 3

**Files to modify**:
- None (verification only)

**Verification**:
- All 8 verification checks pass
- No import errors or missing module errors
- Test suite results match expected counts (171 pass, 1 known failure)

## Testing & Validation

- [x] `pip install -e .` succeeds from `code/` directory without errors
- [x] `import bimodal_logic` works and exposes `Z3OracleProvider`
- [x] `import model_checker` still works (existing package not broken)
- [x] `pip show bimodal-logic` shows name=bimodal-logic, version=0.1.0
- [x] Entry point `z3_base` discoverable via `importlib.metadata.entry_points`
- [x] `pytest` from `code/` runs only bimodal tests (testpaths narrowed)
- [x] Full bimodal test suite: 171 pass, 1 pre-existing failure (BM_CM_1)
- [x] No stale `model_checker.egg-info` remains after install

## Artifacts & Outputs

- `specs/101_restructure_pip_package/plans/01_restructure-plan.md` (this file)
- `code/pyproject.toml` (modified)
- `code/src/bimodal_logic/__init__.py` (new)
- `code/src/bimodal_logic/provider.py` (new)
- `code/src/bimodal_logic/translation.py` (new)
- `code/src/bimodal_logic/serialization.py` (new)
- `code/src/model_checker.egg-info/` (deleted)

## Rollback/Contingency

All changes are reversible via git:
- `git checkout -- code/pyproject.toml` restores original pyproject.toml
- `rm -rf code/src/bimodal_logic/` removes the new package
- `pip install -e .` from `code/` reinstalls under the old `model-checker` name
- If editable install fails, check for syntax errors in pyproject.toml first, then verify the `bimodal_logic/` stubs have no import errors
