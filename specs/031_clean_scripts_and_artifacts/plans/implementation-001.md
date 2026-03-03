# Implementation Plan: Task #31

- **Task**: 31 - clean_scripts_and_artifacts
- **Status**: [IMPLEMENTING]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/031_clean_scripts_and_artifacts/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

This plan removes outdated scripts from `code/scripts/` and `code/fix_output_tests.py`, cleans build artifacts from the boneyard directory, updates `.gitignore` for better artifact exclusion, and documents the remaining development utilities in `code/README.md`. The research report identified 8 outdated scripts referencing completed refactorings plus one one-off migration script that can be safely removed.

### Research Integration

Key findings from research-001.md:
- **Remove entirely**: `code/scripts/` directory (8 scripts referencing completed refactorings or archived theories)
- **Remove**: `code/fix_output_tests.py` (one-time OutputManager migration script)
- **Keep**: 6 root-level development utilities (`dev_cli.py`, `run_tests.py`, `run_jupyter.sh`, `jupyter_link.py`, `run_update.py`, `test_update.py`)
- **Keep**: Debug directory (`code/src/model_checker/jupyter/debug/`) - active and documented
- **Clean**: Build artifacts in boneyard (`__pycache__`, `.ipynb_checkpoints`)
- **Update**: `.gitignore` needs `.pytest_cache/` pattern

## Goals & Non-Goals

**Goals**:
- Remove outdated scripts that reference completed refactorings
- Clean transient build artifacts from boneyard
- Ensure `.gitignore` prevents future artifact accumulation
- Document remaining development utilities for discoverability

**Non-Goals**:
- Restructuring the debug directory (already well-organized)
- Modifying the boneyard source code (historical reference)
- Creating new utility scripts

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing script still in use | Medium | Low | All scripts in git history; verify no CI references |
| Breaking development workflow | Medium | Low | Keeping all active root-level scripts documented |
| Incomplete artifact cleanup | Low | Low | Using find with specific patterns; verify with git status |

## Implementation Phases

### Phase 1: Remove Outdated Scripts [COMPLETED]

**Goal**: Remove the `code/scripts/` directory and `code/fix_output_tests.py`

**Tasks**:
- [ ] Verify no references to `code/scripts/` in CI configuration
- [ ] Remove `code/scripts/` directory entirely (8 scripts)
- [ ] Remove `code/fix_output_tests.py` (one-off migration)
- [ ] Verify removal with `git status`

**Timing**: 0.5 hours

**Files to remove**:
- `code/scripts/test_refactoring.sh` - outdated refactoring test
- `code/scripts/dual_test_refactoring.sh` - outdated dual testing
- `code/scripts/compare_baseline.sh` - depends on missing capture_baseline_simple.py
- `code/scripts/test_iterator_regression.py` - hardcoded wrong path
- `code/scripts/capture_baseline_v2.py` - references archived theories
- `code/scripts/final_validation.py` - refactoring validation complete
- `code/scripts/check_type_coverage.py` - outdated type coverage
- `code/scripts/test_type_hints.py` - outdated type hint validation
- `code/fix_output_tests.py` - one-time OutputManager migration

**Verification**:
- `git status` shows expected removals
- No broken imports in remaining codebase
- No CI failures (if applicable)

---

### Phase 2: Clean Build Artifacts [COMPLETED]

**Goal**: Remove transient build artifacts from boneyard and verify `.gitignore` coverage

**Tasks**:
- [ ] Find and remove `__pycache__` directories in boneyard
- [ ] Find and remove `.ipynb_checkpoints` directories in boneyard
- [ ] Update `.gitignore` to add `.pytest_cache/` pattern
- [ ] Fix `.ipynb_checkpoints` pattern to use directory glob
- [ ] Verify all artifact patterns are properly excluded

**Timing**: 0.5 hours

**Files to modify**:
- `.gitignore` - add `**/.pytest_cache/` pattern, fix `*.ipynb_checkpoints` to `**/.ipynb_checkpoints/`

**Directories to clean**:
- `code/boneyard/**/__pycache__/` - Python bytecode caches
- `code/boneyard/**/.ipynb_checkpoints/` - Jupyter notebook checkpoints

**Verification**:
- `find code/boneyard -name '__pycache__' -type d` returns empty
- `find code/boneyard -name '.ipynb_checkpoints' -type d` returns empty
- `git check-ignore code/boneyard/test/__pycache__/` confirms exclusion

---

### Phase 3: Document Development Scripts [COMPLETED]

**Goal**: Add Development Scripts section to `code/README.md` documenting the 6 root-level utilities

**Tasks**:
- [ ] Add "Development Scripts" section to `code/README.md`
- [ ] Document each script's purpose, usage, and typical invocation
- [ ] Ensure documentation matches existing docstrings

**Timing**: 1.0 hour

**Files to modify**:
- `code/README.md` - Add Development Scripts section after Quick Start

**Scripts to document**:

| Script | Purpose |
|--------|---------|
| `dev_cli.py` | Development CLI entry point for local testing without installation |
| `run_tests.py` | Unified test runner for theories and components |
| `run_jupyter.sh` | Wrapper to start Jupyter with ModelChecker support |
| `jupyter_link.py` | Sets up ModelChecker symlinks for Jupyter notebooks |
| `run_update.py` | Package release script for PyPI |
| `test_update.py` | Test PyPI release script |

**Verification**:
- README renders correctly (preview in editor)
- All scripts mentioned match actual files in `code/`
- Usage examples are accurate

---

### Phase 4: Final Verification [NOT STARTED]

**Goal**: Verify cleanup is complete and no regressions introduced

**Tasks**:
- [ ] Run test suite to confirm no broken imports
- [ ] Verify `code/` directory structure is clean
- [ ] Confirm `.gitignore` prevents artifact tracking
- [ ] Review git status for expected changes only

**Timing**: 0.5 hours

**Commands**:
```bash
# Run tests
PYTHONPATH=code/src pytest code/tests/ -v --tb=short

# Check for remaining artifacts
find code -name '__pycache__' -type d 2>/dev/null
find code -name '.ipynb_checkpoints' -type d 2>/dev/null

# Verify gitignore
git check-ignore code/boneyard/test/__pycache__/
```

**Verification**:
- All tests pass
- No unexpected `__pycache__` or `.ipynb_checkpoints` directories
- Git status shows only expected changes

## Testing & Validation

- [ ] Test suite passes after script removal
- [ ] No broken imports in codebase
- [ ] `.gitignore` patterns work correctly
- [ ] Documentation is accurate and readable

## Artifacts & Outputs

- Removed: `code/scripts/` directory (8 files)
- Removed: `code/fix_output_tests.py`
- Cleaned: Build artifacts in `code/boneyard/`
- Updated: `.gitignore` with improved patterns
- Updated: `code/README.md` with Development Scripts section

## Rollback/Contingency

All removed files are preserved in git history. To restore:
```bash
# Restore scripts directory
git checkout HEAD~1 -- code/scripts/

# Restore individual file
git checkout HEAD~1 -- code/fix_output_tests.py
```

If documentation changes cause issues, revert the README changes and adjust accordingly.
