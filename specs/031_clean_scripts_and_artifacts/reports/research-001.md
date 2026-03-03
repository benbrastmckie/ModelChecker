# Research Report: Task #31

**Task**: 31 - clean_scripts_and_artifacts
**Started**: 2026-03-03T12:00:00Z
**Completed**: 2026-03-03T12:30:00Z
**Effort**: Medium (2-4 hours implementation)
**Dependencies**: None
**Sources/Inputs**: Codebase exploration via Glob, Grep, Read
**Artifacts**: specs/031_clean_scripts_and_artifacts/reports/research-001.md
**Standards**: report-format.md

## Executive Summary

- Found 12 scripts requiring review (4 shell scripts, 8 Python scripts in code/scripts/)
- Identified 4 active development utilities at root level worth keeping
- Discovered substantial boneyard directory with archived theories (exclusion, imposition)
- Located debug directory with Jupyter debugging tools that appear active
- Found various build artifacts (__pycache__, .egg-info, .pytest_cache, .ipynb_checkpoints) that should be cleaned periodically

## Context & Scope

This research examines all scripts and artifacts in the `code/` subdirectory to:
1. Identify unnecessary scripts that can be removed
2. Find scripts that should be documented or reorganized
3. Catalog build artifacts that need periodic cleanup
4. Assess the boneyard directory contents

## Findings

### 1. Root-Level Scripts (code/)

These are essential development utilities that should be **KEPT**:

| Script | Purpose | Status | Documentation |
|--------|---------|--------|---------------|
| `dev_cli.py` | Development CLI entry point for local testing without installation | ACTIVE | Has docstring |
| `run_tests.py` | Unified test runner for theories and components | ACTIVE | Excellent docstring with usage examples |
| `run_jupyter.sh` | Wrapper to start Jupyter with ModelChecker support | ACTIVE | Brief comments |
| `jupyter_link.py` | Sets up ModelChecker symlinks for Jupyter notebooks | ACTIVE | Full docstring with usage |
| `run_update.py` | Package release script for PyPI | ACTIVE | Full docstring |
| `test_update.py` | Test PyPI release script | ACTIVE | Full docstring |

**Scripts to REMOVE** (one-off fix utilities):

| Script | Purpose | Reason for Removal |
|--------|---------|-------------------|
| `fix_output_tests.py` | One-time migration script for OutputManager | Likely completed, no longer needed |

### 2. Scripts Directory (code/scripts/)

| Script | Purpose | Status | Recommendation |
|--------|---------|--------|----------------|
| `test_refactoring.sh` | Baseline capture/comparison for model.py refactoring | OUTDATED | REMOVE - refactoring is complete |
| `dual_test_refactoring.sh` | Dual testing for ModelChecker refactoring | OUTDATED | REMOVE - refactoring is complete |
| `compare_baseline.sh` | Compare baseline outputs after refactoring | OUTDATED | REMOVE - depends on missing capture_baseline_simple.py |
| `test_iterator_regression.py` | Iterator regression testing | OUTDATED | REMOVE - hardcoded path to wrong location |
| `capture_baseline_v2.py` | Capture baseline outputs | OUTDATED | REMOVE - references exclusion/imposition theories |
| `final_validation.py` | Validate theory_lib refactor completion | OUTDATED | REMOVE - refactoring is complete |
| `check_type_coverage.py` | Analyze type hint coverage in theory_lib | POTENTIALLY USEFUL | Consider keeping for periodic quality checks |
| `test_type_hints.py` | Validate type hints work correctly | POTENTIALLY USEFUL | Consider keeping for periodic quality checks |

**Recommendation**: Remove the entire `code/scripts/` directory as most scripts reference completed refactorings or archived theories. If type coverage analysis is desired, integrate it into the main test suite or create a new quality check script.

### 3. Debug Directory (code/src/model_checker/jupyter/debug/)

This directory contains **active debugging tools** that should be **KEPT**:

| File | Purpose |
|------|---------|
| `README.md` | Documentation for debugging tools |
| `DEBUGGING.md` | Comprehensive debugging workflow (30KB) |
| `jupyter_test.py` | Environment and path diagnostic script |
| `debug_notebook.py` | Component-by-component testing |
| `debug_error_capture.py` | Error capture utilities |
| `fix_jupyter_integration.py` | Jupyter integration fixes |

**Recommendation**: Keep all debug tools - they are documented and useful for troubleshooting.

### 4. Boneyard Directory (code/boneyard/)

Contains archived theories:
- `theory_lib/exclusion/` - Archived truthmaker semantics theory
- `theory_lib/imposition/` - Archived alternative truthmaker semantics

**Contents include**:
- Full source code (semantic.py, operators.py, examples.py, iterate.py)
- Tests (unit and integration)
- Documentation (docs/, history/)
- Jupyter notebooks with .ipynb_checkpoints
- __pycache__ directories

**Recommendation**: The boneyard is properly documented with a README.md explaining restoration procedures. Consider:
1. Removing __pycache__ directories within boneyard
2. Removing .ipynb_checkpoints directories within boneyard
3. Keeping the source code and documentation for historical reference

### 5. Build Artifacts (Periodic Cleanup Needed)

| Artifact Type | Location | Recommendation |
|---------------|----------|----------------|
| `__pycache__/` | Throughout code/ | Add to .gitignore, clean periodically |
| `.pytest_cache/` | code/.pytest_cache | Add to .gitignore if not already |
| `.egg-info/` | code/src/model_checker.egg-info | Add to .gitignore |
| `.ipynb_checkpoints/` | In notebooks directories | Add to .gitignore |

### 6. Jupyter Notebooks

Active notebooks found in:
- `code/src/model_checker/jupyter/notebooks/` - Demo notebooks
- `code/src/model_checker/theory_lib/logos/subtheories/*/notebooks/` - Theory examples

These are **active and should be kept**.

## Decisions

1. **Remove `code/scripts/` directory entirely** - All scripts reference completed refactorings or archived theories
2. **Remove `code/fix_output_tests.py`** - One-time migration script no longer needed
3. **Keep root-level scripts** - `dev_cli.py`, `run_tests.py`, `run_jupyter.sh`, `jupyter_link.py`, `run_update.py`, `test_update.py`
4. **Keep debug directory** - Active and documented debugging tools
5. **Keep boneyard directory structure** - But clean __pycache__ and .ipynb_checkpoints within it
6. **Add cleanup entries to .gitignore** if not already present

## Implementation Recommendations

### Phase 1: Clean Scripts
1. Remove `code/scripts/` directory
2. Remove `code/fix_output_tests.py`
3. Document remaining root-level scripts in `code/README.md`

### Phase 2: Clean Build Artifacts
1. Remove all `__pycache__` directories
2. Remove all `.ipynb_checkpoints` directories
3. Verify `.gitignore` includes these patterns

### Phase 3: Documentation
1. Update `code/README.md` to document available development scripts
2. Consider adding a `DEVELOPMENT.md` or section explaining script purposes

## Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| Removing scripts that are still needed | All scripts are in git history and can be restored |
| Breaking CI/CD pipelines | Review any CI configuration that might reference these scripts |
| Losing useful type coverage analysis | Consider integrating `check_type_coverage.py` functionality into test suite |

## Appendix

### Search Patterns Used
- `code/**/*.sh` - Shell scripts
- `code/**/scripts/**` - Scripts directories
- `code/**/*.py` - Python files
- `code/**/boneyard/**` - Archived code
- `code/**/__pycache__/**` - Python cache
- `code/**/debug/**` - Debug directories

### Files Reviewed
- 4 shell scripts
- 8 Python scripts in code/scripts/
- 6 root-level Python scripts
- 6 debug directory files
- Boneyard directory structure
- Build artifact directories
