# Implementation Plan: Task #16

- **Task**: 16 - Update all references to renamed lowercase directories
- **Status**: [COMPLETED]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/016_update_references_to_renamed_lowercase_directories/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md
- **Type**: general
- **Lean Intent**: false

## Overview

Systematically update 83+ files containing references to old uppercase directory names (`Code/`, `Docs/`, `Images/`) to use the new lowercase paths (`code/`, `docs/`, `images/`). The approach groups files by category (high-impact documentation, user docs, developer docs, source code, Claude configuration) to enable focused verification after each phase.

### Research Integration

Key findings from research:
- Three directories renamed: `Code/` -> `code/`, `Docs/` -> `docs/`, `Images/` -> `images/`
- 83 files with `Code/` references, 32 with `Docs/`, 1 with `Images/`
- Reference types: relative paths (~150), PYTHONPATH commands (~30), cd commands (~12), GitHub URLs (~20), directory trees (~10), print statements (~5)
- Exclusions: `specs/` directory (historical artifacts), `.git/` (internal)

## Goals & Non-Goals

**Goals**:
- Update all references to match new lowercase directory structure
- Preserve functional integrity of documentation links
- Maintain consistency across codebase

**Non-Goals**:
- Updating specs/ directory (historical artifacts preserved)
- Changing any actual directory structure (already renamed)
- Modifying git history

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Broken documentation links | Medium | Low | Verify with grep after each phase |
| Test failures after Python changes | Medium | Low | Run test suite after Phase 4 |
| Missed references | Low | Low | Final comprehensive grep scan in Phase 6 |
| Unintended changes in TODO.md | Low | Medium | Manual review before editing |

## Implementation Phases

### Phase 1: High-Impact Root Files [COMPLETED]

**Goal**: Update the most visible and frequently-accessed documentation files

**Tasks**:
- [ ] Update `README.md` (root) - ~20 `Code/` references, 1 `Images/` reference
- [ ] Update `CLAUDE.md` - ~20 `Code/` references, multiple `Docs/` references
- [ ] Verify links resolve correctly

**Timing**: 0.5 hours

**Files to modify**:
- `README.md` - Replace `Code/` -> `code/`, `Docs/` -> `docs/`, `Images/` -> `images/`
- `CLAUDE.md` - Replace `Code/` -> `code/`, `Docs/` -> `docs/`

**Verification**:
- `grep -n "Code/\|Docs/\|Images/" README.md CLAUDE.md` returns empty
- Directory tree displays in README show lowercase paths

---

### Phase 2: User Documentation (docs/) [COMPLETED]

**Goal**: Update all user-facing documentation in the docs/ directory

**Tasks**:
- [ ] Update `docs/README.md`
- [ ] Update architecture documentation (`docs/architecture/*.md` - 12 files)
- [ ] Update installation guides (`docs/installation/*.md` - 7 files)
- [ ] Update maintenance documentation (`docs/maintenance/*.md` - 4 files)
- [ ] Update theory documentation (`docs/theory/*.md` - 4 files)
- [ ] Update usage guides (`docs/usage/*.md` - 8 files)

**Timing**: 0.5 hours

**Files to modify**:
- `docs/README.md`
- `docs/architecture/BUILDER.md`, `ITERATE.md`, `JUPYTER.md`, `MODELS.md`, `OUTPUT.md`, `PIPELINE.md`, `README.md`, `SEMANTICS.md`, `SETTINGS.md`, `SYNTACTIC.md`, `THEORY_LIB.md`, `UTILS.md`
- `docs/installation/CLAUDE_CODE.md`, `CLAUDE_TEMPLATE.md`, `DEVELOPER_SETUP.md`, `GETTING_STARTED.md`, `JUPYTER_SETUP.md`, `README.md`, `VIRTUAL_ENVIRONMENTS.md`
- `docs/maintenance/AUDIENCE.md`, `README.md`, `VERSION_CONTROL.md`, `quality/DOCUMENTATION_STANDARDS.md`, `quality/README_STANDARDS.md`
- `docs/theory/HYPERINTENSIONAL.md`, `IMPLEMENTATION.md`, `README.md`, `REFERENCES.md`
- `docs/usage/OPERATORS.md`, `OUTPUT.md`, `PROJECT.md`, `README.md`, `SEMANTICS.md`, `SETTINGS.md`, `TOOLS.md`, `WORKFLOW.md`

**Verification**:
- `grep -rn "Code/\|Docs/" docs/` returns empty (excluding any intentional historical references)

---

### Phase 3: Developer Documentation (code/docs/) [COMPLETED]

**Goal**: Update internal developer documentation and templates

**Tasks**:
- [ ] Update core documentation (`code/docs/core/*.md`)
- [ ] Update development guides (`code/docs/development/*.md`)
- [ ] Update quality documentation (`code/docs/quality/*.md`)
- [ ] Update template files (`code/docs/templates/*.py`)

**Timing**: 0.25 hours

**Files to modify**:
- `code/docs/core/TESTING_GUIDE.md`, `DOCUMENTATION.md`
- `code/docs/development/ENVIRONMENT_SETUP.md`, `FEATURE_IMPLEMENTATION.md`, `PACKAGE_TESTING.md`, `PYPI_RELEASE_GUIDE.md`, `README.md`
- `code/docs/quality/MANUAL_TESTING.md`
- `code/docs/templates/EXAMPLES_TEMPLATE.py`, `README.md`, `TEST_TEMPLATE.py`, `THEORY_TEMPLATE.py`
- `code/README.md`

**Verification**:
- `grep -rn "Code/\|Docs/" code/docs/` returns empty
- `grep -n "Code/\|Docs/" code/README.md` returns empty

---

### Phase 4: Source Code Files [COMPLETED]

**Goal**: Update Python source files with hardcoded path references

**Tasks**:
- [ ] Update theory library `__init__.py` files (print statements with `Docs/`)
- [ ] Update jupyter module files
- [ ] Update scripts with path references
- [ ] Update test files with path references
- [ ] Update module README files

**Timing**: 0.5 hours

**Files to modify**:
- `code/src/model_checker/__main__.py`
- `code/src/model_checker/jupyter/environment.py`, `README.md`, `NixOS_jupyter.md`, `debug/DEBUGGING.md`, `debug/README.md`
- `code/src/model_checker/theory_lib/bimodal/__init__.py`, `README.md`, `docs/README.md`, `tests/unit/test_bimodal.py`
- `code/src/model_checker/theory_lib/exclusion/__init__.py`, `README.md`, `notebooks/README.md`
- `code/src/model_checker/theory_lib/imposition/__init__.py`, `reports/imposition_comparison/*.md`
- `code/src/model_checker/theory_lib/logos/__init__.py`, `README.md`, `TODO.md`, `subtheories/first-order/tests/*.py`
- `code/src/model_checker/theory_lib/docs/CONTRIBUTING.md`, `usage_guide.md`, `USAGE_GUIDE.md`
- `code/src/model_checker/theory_lib/README.md`, `tests/integration/test_refactored_workflows.py`
- `code/src/model_checker/builder/README.md`
- `code/src/model_checker/iterate/README.md`
- `code/src/model_checker/models/README.md`
- `code/src/model_checker/README.md`
- `code/src/model_checker/settings/README.md`
- `code/src/model_checker/syntactic/README.md`
- `code/src/model_checker/utils/README.md`
- `code/tests/README.md`
- `code/run_update.py`
- `code/scripts/check_type_coverage.py`, `final_validation.py`, `test_type_hints.py`

**Verification**:
- `grep -rn "Code/\|Docs/" code/src/` returns empty
- `grep -rn "Code/\|Docs/" code/scripts/` returns empty
- Run basic test: `cd code && PYTHONPATH=src pytest tests/ -v --collect-only` succeeds

---

### Phase 5: Claude Code Configuration [COMPLETED]

**Goal**: Update Claude Code agent and context files

**Tasks**:
- [ ] Update agent definitions (`.claude/agents/*.md`)
- [ ] Update context files (`.claude/context/**/*.md`)
- [ ] Verify PYTHONPATH commands are correct

**Timing**: 0.25 hours

**Files to modify**:
- `.claude/agents/python-implementation-agent.md`
- `.claude/agents/python-research-agent.md`
- `.claude/agents/z3-implementation-agent.md`
- `.claude/agents/z3-research-agent.md`
- `.claude/context/core/formats/frontmatter.md`
- `.claude/context/project/python/domain/model-checker-api.md`
- `.claude/context/project/python/README.md`
- `.claude/context/project/python/standards/code-style.md`

**Verification**:
- `grep -rn "Code/\|Docs/" .claude/` returns empty

---

### Phase 6: Miscellaneous Files and Final Verification [COMPLETED]

**Goal**: Update remaining files and perform comprehensive verification

**Tasks**:
- [ ] Update GitHub workflow documentation
- [ ] Update LaTeX markdown files
- [ ] Manual review of `TODO.md` (historical references may be intentional)
- [ ] Run comprehensive grep to find any missed references
- [ ] Verify no regressions with test suite

**Timing**: 0.5 hours

**Files to modify**:
- `.github/RELEASE_SETUP.md`
- `.github/workflows/README.md`
- `latex/markdown/paper_overview.md`
- `TODO.md` (manual review - some references may be intentional historical context)

**Verification**:
- `grep -rn "Code/" --include="*.md" --include="*.py" . | grep -v "specs/" | grep -v ".git/"` returns empty
- `grep -rn "Docs/" --include="*.md" --include="*.py" . | grep -v "specs/" | grep -v ".git/"` returns empty
- `grep -rn "Images/" --include="*.md" . | grep -v "specs/" | grep -v ".git/"` returns empty
- Full test suite passes: `cd code && PYTHONPATH=src pytest tests/ -v`

---

## Testing & Validation

- [ ] All grep verification commands pass (no remaining uppercase references)
- [ ] Test suite passes: `PYTHONPATH=code/src pytest code/tests/ -v`
- [ ] Documentation links are functional (spot-check 5-10 links)
- [ ] GitHub URL references use lowercase paths

## Artifacts & Outputs

- Updated documentation files (83+ files)
- No new files created (updates only)
- Implementation summary upon completion

## Rollback/Contingency

If issues are discovered after implementation:
1. Use `git diff` to review all changes
2. Use `git checkout -- <file>` to revert individual files
3. If widespread issues: `git reset --hard HEAD~1` to revert entire commit
4. Keep each phase as a separate commit for granular rollback capability
