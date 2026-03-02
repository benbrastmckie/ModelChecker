# Research Report: Task #17

**Task**: 17 - Fix remaining uppercase directory references missed by task 16
**Started**: 2026-03-02T12:00:00Z
**Completed**: 2026-03-02T12:15:00Z
**Effort**: Low-Medium
**Dependencies**: Task 16 (completed)
**Sources/Inputs**: Codebase exploration (grep, find), neovim config analysis
**Artifacts**: This report
**Standards**: report-format.md

## Executive Summary

- **Primary Issue Found**: Neovim keybinding `<leader>rm` error originates from `~/.config/nvim/lua/neotex/plugins/editor/which-key.lua` (lines 104-121) which searches for `Code/dev_cli.py`
- **Repository Files**: 5 categories of files still contain uppercase references (mostly cached/generated content)
- **External Dependency**: The neovim config is OUTSIDE the ModelChecker repository but needs updating
- Recommended approach: Fix neovim config first (external), then clean up generated files

## Context & Scope

Task 16 updated references from uppercase directories (`Code/`, `Docs/`, `Images/`) to lowercase (`code/`, `docs/`, `images/`). However, the neovim keybinding `<leader>rm` reports "Could not find Code/dev_cli.py in project", indicating some references were missed.

**Search Strategy**:
1. Grep for `Code/`, `Docs/`, `Images/` excluding `specs/` and `.git/`
2. Check hidden directories (`.claude/`, `.gitignore`)
3. Check external neovim configuration
4. Identify generated/cached content vs. source files

## Findings

### Category 1: Neovim Configuration (CRITICAL - External Dependency)

**File**: `~/.config/nvim/lua/neotex/plugins/editor/which-key.lua`
**Lines**: 104-121

This file contains the `RunModelChecker` function that causes the error. It searches for:
- `current_dir .. "/Code/dev_cli.py"` (line 104-105)
- `parent .. "/Code/dev_cli.py"` (lines 109-110)
- `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/dev_cli.py` (line 113-114)
- Error message: `"Could not find Code/dev_cli.py in project"` (line 121)

**Also in neovim**:
- `~/.config/nvim/lua/neotex/plugins/editor/README.md:167` - Example documentation
- `~/.config/nvim/sessions/__home__benjamin__Projects__ModelChecker` - Session file with old paths (lines 20-25)

**Note**: This is OUTSIDE the ModelChecker repository. The user needs to update their neovim configuration separately.

### Category 2: .gitignore File (In Repository)

**File**: `.gitignore`
**Lines**: 21-23

```
Code/src/new_checker/__pycache__/exposed_things.cpython-312.pyc
Code/src/new_checker/__pycache__/hidden_helpers.cpython-312.pyc
Code/.venv
```

These entries reference non-existent paths (the Code/ directory is now code/).

### Category 3: Jupyter Notebook Cached Output (In Repository)

**Files with cached execution output containing old paths**:

| File | Type | Issue |
|------|------|-------|
| `code/src/model_checker/jupyter/debug/.ipynb_checkpoints/demo_notebook-checkpoint.ipynb` | Checkpoint | 8+ references |
| `code/src/model_checker/jupyter/notebooks/basic_demo.ipynb` | Notebook | Traceback with old paths |
| `code/src/model_checker/jupyter/notebooks/options_demo.ipynb` | Notebook | 6+ references |
| `code/src/model_checker/jupyter/notebooks/.ipynb_checkpoints/options_demo-checkpoint.ipynb` | Checkpoint | 5+ references |

These are **cached execution outputs** showing absolute paths from when the notebooks were run. The paths appear in cell outputs, not in code. Clearing notebook outputs or re-running notebooks would update these.

### Category 4: PKG-INFO (Generated File)

**File**: `code/src/model_checker.egg-info/PKG-INFO`

This file contains ~20 references to GitHub URLs with uppercase paths:
- `github.com/benbrastmckie/ModelChecker/blob/master/Docs/README.md`
- `github.com/benbrastmckie/ModelChecker/blob/master/Code/docs/README.md`
- `github.com/benbrastmckie/ModelChecker/tree/master/Code/src/model_checker/theory_lib`
- etc.

**Note**: PKG-INFO is auto-generated from README.md during package build. Rebuilding the package (`python -m build`) will regenerate this file with updated paths. However, the GitHub repository itself still has branches/tags with old paths in history.

### Category 5: LaTeX Auxiliary Files (.fls)

**File**: `talks/truthmaker_adv_II/handout.fls`
**Line 1**: `PWD /home/benjamin/Documents/Philosophy/Projects/ModelChecker/Docs/talks/truthmaker_adv_II`

This is a LaTeX auxiliary file generated during compilation. It records the working directory at compile time. These files are typically regenerated on each compile and can be safely deleted or ignored.

### Category 6: Documentation Plan (Historical Reference)

**File**: `docs/specs/plans/documentation_revision_plan.md`

Contains historical references to `Docs/` directory structure. This is a completed plan document and the references are descriptive of past state, not active paths. May or may not need updating depending on whether historical accuracy is desired.

## Summary Table

| Category | Location | Priority | Action Required |
|----------|----------|----------|-----------------|
| Neovim Config | `~/.config/nvim/lua/neotex/plugins/editor/which-key.lua` | **HIGH** | Update 4 path references |
| .gitignore | `.gitignore` | **HIGH** | Update 3 entries |
| Jupyter Notebooks | `code/src/model_checker/jupyter/**/*.ipynb` | LOW | Clear outputs or ignore |
| PKG-INFO | `code/src/model_checker.egg-info/PKG-INFO` | LOW | Regenerate with `python -m build` |
| LaTeX .fls | `talks/truthmaker_adv_II/handout.fls` | NONE | Delete or ignore |
| Documentation Plan | `docs/specs/plans/documentation_revision_plan.md` | LOW | Consider updating for consistency |
| Neovim Session | `~/.config/nvim/sessions/*` | NONE | Auto-updates on session save |

## Decisions

1. **Neovim config is external**: The `<leader>rm` error source is in the user's neovim configuration, not in the ModelChecker repository
2. **Generated files**: PKG-INFO and .ipynb_checkpoints are generated content; source changes cascade to them
3. **.gitignore needs fixing**: The entries reference paths that no longer exist
4. **Jupyter outputs are cosmetic**: They show old paths in output cells but don't affect functionality

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Neovim config is external to this repo | User must manually update their nvim config | Document location and changes needed |
| GitHub history still has old paths | Links in old releases/commits won't work | This is unavoidable; document in release notes |
| PKG-INFO regeneration requires package rebuild | Stale paths until rebuild | Run `python -m build` after updating README |

## Recommendations

### Immediate Actions (This Task)

1. **Update `.gitignore`** - Change `Code/` to `code/` on lines 21-23
2. **Document neovim fix** - The user needs to update their external neovim config

### User Actions Required (External)

Update `~/.config/nvim/lua/neotex/plugins/editor/which-key.lua`:
- Line 104: `"/Code/dev_cli.py"` -> `"/code/dev_cli.py"`
- Line 105: same
- Line 109: `"/Code/dev_cli.py"` -> `"/code/dev_cli.py"`
- Line 110: same
- Line 113: `"/Code/dev_cli.py"` -> `"/code/dev_cli.py"`
- Line 114: same
- Line 121: error message (optional, for clarity)

### Optional Cleanup

1. Clear Jupyter notebook outputs: `jupyter nbconvert --clear-output --inplace *.ipynb`
2. Rebuild package: `cd code && python -m build`
3. Delete LaTeX auxiliary files: `rm talks/truthmaker_adv_II/handout.fls`
4. Update documentation plan if historical accuracy desired

## Appendix

### Search Commands Used

```bash
# Find all Code/ references excluding specs
grep -rn "Code/" --exclude-dir=specs --exclude-dir=.git .

# Find all Docs/ references excluding specs
grep -rn "Docs/" --exclude-dir=specs --exclude-dir=.git .

# Find Code/dev_cli references
grep -rn "Code/dev_cli" .

# Search neovim config
grep -rn "Code/" ~/.config/nvim/

# Search jupyter notebooks
grep -rn "Code/\|Docs/\|Images/" . --include="*.ipynb"
```

### Files Changed Summary

| File | Lines to Change | Change Type |
|------|-----------------|-------------|
| `.gitignore` | 3 | `Code/` -> `code/` |
| `~/.config/nvim/.../which-key.lua` | 6 | `Code/` -> `code/` (external) |
