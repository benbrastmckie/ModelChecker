# Research Report: Task #16

**Task**: 16 - Update all references to renamed lowercase directories
**Started**: 2026-03-02T00:00:00Z
**Completed**: 2026-03-02T00:30:00Z
**Effort**: Small-Medium
**Dependencies**: None
**Sources/Inputs**: Git history, codebase grep analysis
**Artifacts**: This report
**Standards**: report-format.md

## Executive Summary

- Three top-level directories were renamed to lowercase in commit `0161871f`: `Code/` -> `code/`, `Docs/` -> `docs/`, `Images/` -> `images/`
- **83 files** contain references to the old uppercase paths that need updating
- References are primarily in markdown documentation, with some in Python files and configuration
- Fix involves systematic find-and-replace across documentation and source files

## Context & Scope

Recent commit `0161871f` (task 12: supplementary research on syntax changes) renamed the top-level directories from TitleCase to lowercase:

| Old Path | New Path |
|----------|----------|
| `Code/` | `code/` |
| `Docs/` | `docs/` |
| `Images/` | `images/` |

The directory structure change was applied, but internal references within files were not updated. This creates broken links and inconsistent documentation.

## Findings

### Directory Rename Details

From git history analysis:
```
git show 0161871f --stat | grep "=>" | sed 's/.*{//' | sed 's/}.*//' | sort -u
```

Results:
- `Code => code` - Main implementation directory (hundreds of files)
- `Docs => docs` - User documentation
- `Images => images` - Visual assets

### Files with `Code/` References (83 files total)

#### High-Priority Files (core documentation)
1. **`README.md`** - 20+ references to `Code/`
2. **`CLAUDE.md`** - 20+ references (testing commands, structure)
3. **`code/README.md`** - GitHub URLs and links

#### Documentation in `docs/` directory (25 files)
- `docs/architecture/*.md` - Architecture documentation
- `docs/installation/*.md` - Setup guides
- `docs/maintenance/*.md` - Quality standards
- `docs/theory/*.md` - Theory documentation
- `docs/usage/*.md` - User guides

#### Documentation in `code/docs/` directory (10 files)
- `code/docs/core/TESTING_GUIDE.md` - Extensive PYTHONPATH references
- `code/docs/development/*.md` - Development guides
- `code/docs/templates/*.py` - Template files

#### Source code with hardcoded paths (5 files)
- `code/src/model_checker/theory_lib/*/__init__.py` - Print statements with `Docs/usage/README.md`
- `code/scripts/*.py` - Path references

#### Claude Code configuration (4 files)
- `.claude/agents/python-*.md` - PYTHONPATH and test commands
- `.claude/agents/z3-*.md` - Similar commands
- `.claude/context/project/python/*.md` - Python context docs

#### Other files
- `.github/workflows/README.md` - CI/CD documentation
- `TODO.md` - Project tasks (historical references, may be intentional)

### Files with `Docs/` References (32 files total)

Primarily in:
- `code/src/model_checker/**/README.md` - Cross-references to user docs
- `code/src/model_checker/**/__init__.py` - Help text
- `docs/installation/*.md` - Internal docs links
- GitHub URLs in `code/README.md`

### Files with `Images/` References (1 file)

- `README.md` - Directory tree description and link

### Reference Categories

| Category | Count | Examples |
|----------|-------|----------|
| Relative paths (local links) | ~150 | `[link](Code/README.md)` |
| PYTHONPATH commands | ~30 | `PYTHONPATH=Code/src pytest...` |
| `cd` commands | ~12 | `cd Code` |
| GitHub URLs | ~20 | `github.com/.../Code/...` |
| Directory trees (visual) | ~10 | `├── Code/` |
| Print statements | ~5 | `print("...Docs/usage...")` |

### GitHub URL Pattern

Many GitHub URLs use the old paths:
```
https://github.com/benbrastmckie/ModelChecker/blob/master/Code/...
https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/...
```

These need updating to:
```
https://github.com/benbrastmckie/ModelChecker/blob/master/code/...
https://github.com/benbrastmckie/ModelChecker/blob/master/docs/...
```

## Recommendations

### Implementation Approach

1. **Phase 1: High-Impact Files**
   - `README.md` (root)
   - `CLAUDE.md` (Claude Code config)
   - `code/README.md` (package docs)

2. **Phase 2: Documentation Directories**
   - `docs/**/*.md` files
   - `code/docs/**/*.md` files

3. **Phase 3: Source Code**
   - `code/src/**/__init__.py` (print statements)
   - `code/scripts/*.py`

4. **Phase 4: Claude Code Configuration**
   - `.claude/agents/*.md`
   - `.claude/context/**/*.md`

5. **Phase 5: Verification**
   - Run `grep -rn "Code/" .` to verify no remaining references
   - Run `grep -rn "Docs/" .` to verify no remaining references
   - Test markdown link validity

### Find/Replace Patterns

| Find | Replace |
|------|---------|
| `Code/` | `code/` |
| `Docs/` | `docs/` |
| `Images/` | `images/` |
| `cd Code` | `cd code` |
| `PYTHONPATH=Code/src` | `PYTHONPATH=code/src` |
| `/master/Code/` | `/master/code/` |
| `/master/Docs/` | `/master/docs/` |

### Exclusions

- `specs/` directory - Contains historical artifacts, may reference old paths intentionally
- `.git/` directory - Git internal files
- `TODO.md` - May contain historical task descriptions (review manually)

## Decisions

1. **Include all file types**: Update `.md`, `.py`, and configuration files
2. **Preserve specs/ history**: Don't update historical artifacts in specs/
3. **Manual review for TODO.md**: Some references may be historical
4. **Test after update**: Verify no broken links

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Broken links after update | Low | Medium | Verify with grep after each phase |
| Missed references | Low | Low | Comprehensive grep patterns |
| Git history issues | Very Low | Low | Changes are all content, not structure |
| Test failures | Low | Medium | Run test suite after Python file changes |

## Appendix

### Search Commands Used

```bash
# Find Code/ references
grep -rln "Code/" --include="*.md" --include="*.py" --exclude-dir=".git" --exclude-dir="specs"

# Find Docs/ references
grep -rln "Docs/" --include="*.md" --include="*.py" --exclude-dir=".git" --exclude-dir="specs"

# Find Images/ references
grep -rln "Images/" --include="*.md" --exclude-dir=".git" --exclude-dir="specs"

# Find GitHub URLs
grep -rn "github.com.*/(Code|Docs|Images)/" --include="*.md"

# Find PYTHONPATH references
grep -rn "PYTHONPATH=Code" --include="*.md" --include="*.sh"

# Find cd commands
grep -rn "cd Code" --include="*.md" --include="*.sh"
```

### Full File Lists

**Files with `Code/` references (83 files):**
- `.claude/agents/python-implementation-agent.md`
- `.claude/agents/python-research-agent.md`
- `.claude/agents/z3-implementation-agent.md`
- `.claude/agents/z3-research-agent.md`
- `.claude/context/core/formats/frontmatter.md`
- `.claude/context/project/python/domain/model-checker-api.md`
- `.claude/context/project/python/README.md`
- `.claude/context/project/python/standards/code-style.md`
- `CLAUDE.md`
- `code/docs/core/TESTING_GUIDE.md`
- `code/docs/development/ENVIRONMENT_SETUP.md`
- `code/docs/development/FEATURE_IMPLEMENTATION.md`
- `code/docs/development/PACKAGE_TESTING.md`
- `code/docs/development/PYPI_RELEASE_GUIDE.md`
- `code/docs/development/README.md`
- `code/docs/quality/MANUAL_TESTING.md`
- `code/docs/templates/EXAMPLES_TEMPLATE.py`
- `code/docs/templates/README.md`
- `code/docs/templates/TEST_TEMPLATE.py`
- `code/docs/templates/THEORY_TEMPLATE.py`
- `code/README.md`
- `code/run_update.py`
- `code/scripts/check_type_coverage.py`
- `code/scripts/final_validation.py`
- `code/scripts/test_type_hints.py`
- `code/src/model_checker/jupyter/debug/DEBUGGING.md`
- `code/src/model_checker/jupyter/environment.py`
- `code/src/model_checker/jupyter/NixOS_jupyter.md`
- `code/src/model_checker/jupyter/README.md`
- `code/src/model_checker/__main__.py`
- `code/src/model_checker/theory_lib/bimodal/README.md`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`
- `code/src/model_checker/theory_lib/docs/CONTRIBUTING.md`
- `code/src/model_checker/theory_lib/docs/usage_guide.md`
- `code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/__init__.py`
- `code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/test_first_order_examples.py`
- `code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/unit/test_exists_duality.py`
- `code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/unit/test_forall_arity1.py`
- `code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/unit/test_parser_desugar.py`
- `code/src/model_checker/theory_lib/logos/subtheories/first-order/tests/unit/test_validation.py`
- `code/src/model_checker/theory_lib/logos/TODO.md`
- `code/src/model_checker/theory_lib/tests/integration/test_refactored_workflows.py`
- `code/tests/README.md`
- `docs/architecture/BUILDER.md`
- `docs/architecture/ITERATE.md`
- `docs/architecture/JUPYTER.md`
- `docs/architecture/MODELS.md`
- `docs/architecture/OUTPUT.md`
- `docs/architecture/PIPELINE.md`
- `docs/architecture/README.md`
- `docs/architecture/SEMANTICS.md`
- `docs/architecture/SETTINGS.md`
- `docs/architecture/SYNTACTIC.md`
- `docs/architecture/THEORY_LIB.md`
- `docs/architecture/UTILS.md`
- `docs/installation/DEVELOPER_SETUP.md`
- `docs/installation/GETTING_STARTED.md`
- `docs/installation/JUPYTER_SETUP.md`
- `docs/installation/README.md`
- `docs/installation/VIRTUAL_ENVIRONMENTS.md`
- `docs/maintenance/AUDIENCE.md`
- `docs/maintenance/quality/README_STANDARDS.md`
- `docs/maintenance/README.md`
- `docs/maintenance/VERSION_CONTROL.md`
- `docs/README.md`
- `docs/theory/HYPERINTENSIONAL.md`
- `docs/theory/IMPLEMENTATION.md`
- `docs/theory/README.md`
- `docs/theory/REFERENCES.md`
- `docs/usage/OPERATORS.md`
- `docs/usage/OUTPUT.md`
- `docs/usage/PROJECT.md`
- `docs/usage/README.md`
- `docs/usage/SEMANTICS.md`
- `docs/usage/SETTINGS.md`
- `docs/usage/TOOLS.md`
- `docs/usage/WORKFLOW.md`
- `.github/RELEASE_SETUP.md`
- `.github/workflows/README.md`
- `latex/markdown/paper_overview.md`
- `README.md`
- `TODO.md`

**Files with `Docs/` references (32 files):**
- `CLAUDE.md`
- `code/docs/core/DOCUMENTATION.md`
- `code/README.md`
- `code/src/model_checker/builder/README.md`
- `code/src/model_checker/iterate/README.md`
- `code/src/model_checker/jupyter/debug/README.md`
- `code/src/model_checker/jupyter/README.md`
- `code/src/model_checker/models/README.md`
- `code/src/model_checker/README.md`
- `code/src/model_checker/settings/README.md`
- `code/src/model_checker/syntactic/README.md`
- `code/src/model_checker/theory_lib/bimodal/docs/README.md`
- `code/src/model_checker/theory_lib/bimodal/__init__.py`
- `code/src/model_checker/theory_lib/docs/USAGE_GUIDE.md`
- `code/src/model_checker/theory_lib/exclusion/__init__.py`
- `code/src/model_checker/theory_lib/exclusion/notebooks/README.md`
- `code/src/model_checker/theory_lib/exclusion/README.md`
- `code/src/model_checker/theory_lib/imposition/__init__.py`
- `code/src/model_checker/theory_lib/imposition/reports/imposition_comparison/modals_defined.md`
- `code/src/model_checker/theory_lib/imposition/reports/imposition_comparison/README.md`
- `code/src/model_checker/theory_lib/logos/__init__.py`
- `code/src/model_checker/theory_lib/logos/README.md`
- `code/src/model_checker/theory_lib/README.md`
- `code/src/model_checker/utils/README.md`
- `docs/installation/CLAUDE_CODE.md`
- `docs/installation/CLAUDE_TEMPLATE.md`
- `docs/installation/DEVELOPER_SETUP.md`
- `docs/installation/GETTING_STARTED.md`
- `docs/maintenance/quality/DOCUMENTATION_STANDARDS.md`
- `docs/README.md`
- `README.md`
- `TODO.md`

**Files with `Images/` references (1 file):**
- `README.md`
