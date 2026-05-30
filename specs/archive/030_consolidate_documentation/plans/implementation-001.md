# Implementation Plan: Task #30

- **Task**: 30 - consolidate_documentation
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: Task #27 (completed)
- **Research Inputs**: specs/030_consolidate_documentation/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md
- **Type**: general
- **Lean Intent**: false

## Overview

Consolidate documentation by moving developer-targeted content from `docs/maintenance/` to `code/docs/standards/`. Research found that the existing dual structure (`docs/` for users, `code/docs/` for developers) is appropriate, but `docs/maintenance/` contains contributor standards that belong in `code/docs/`. This involves moving 11 files, creating new directory structure, and updating approximately 90+ cross-references.

### Research Integration

Key findings from research:
- 5 documentation directories exist; theory-specific docs should stay co-located with implementations
- `docs/maintenance/` (9 files) targets contributors, not users - move to `code/docs/standards/`
- Architecture docs in `docs/` vs `code/docs/` serve different audiences - keep both
- ~90+ cross-references need updating after reorganization

## Goals & Non-Goals

**Goals**:
- Move `docs/maintenance/` content to `code/docs/standards/` and `code/docs/templates/documentation/`
- Update all cross-references to point to new locations
- Ensure documentation navigation remains functional
- Preserve all content (no deletions without explicit decision)

**Non-Goals**:
- Merging theory-specific documentation (stays co-located)
- Merging architecture documentation (different audiences)
- Rewriting or improving documentation content
- Changing `docs/` user-facing organization

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Broken cross-references | Medium | High | Systematic grep-based search; verify all links post-move |
| Lost content during move | High | Low | Use git mv for history; verify file counts before/after |
| Incomplete reference updates | Medium | Medium | Create checklist of files moved; search for old paths |
| README navigation breaks | Medium | Medium | Update READMEs in same commit as moves |

## Implementation Phases

### Phase 1: Create Directory Structure [COMPLETED]

**Goal**: Establish new directory hierarchy in `code/docs/` before moving files

**Tasks**:
- [ ] Create `code/docs/standards/` directory
- [ ] Create `code/docs/standards/documentation/` subdirectory
- [ ] Create `code/docs/templates/documentation/` subdirectory
- [ ] Verify existing `code/docs/templates/` structure

**Timing**: 0.25 hours

**Files to modify**:
- `code/docs/standards/` - create directory
- `code/docs/standards/documentation/` - create directory
- `code/docs/templates/documentation/` - create directory

**Verification**:
- Run `ls -la code/docs/standards/` confirms directory exists
- Run `ls -la code/docs/templates/` shows documentation subdirectory

---

### Phase 2: Move Documentation Standards Files [COMPLETED]

**Goal**: Move files from `docs/maintenance/` to their new locations in `code/docs/`

**Tasks**:
- [ ] Move `docs/maintenance/README.md` to `code/docs/standards/README.md`
- [ ] Move `docs/maintenance/AUDIENCE.md` to `code/docs/standards/AUDIENCE.md`
- [ ] Move `docs/maintenance/VERSION_CONTROL.md` to `code/docs/standards/VERSION_CONTROL.md`
- [ ] Move `docs/maintenance/quality/README.md` to `code/docs/standards/documentation/README.md`
- [ ] Move `docs/maintenance/quality/DOCUMENTATION_STANDARDS.md` to `code/docs/standards/documentation/DOCUMENTATION_STANDARDS.md`
- [ ] Move `docs/maintenance/quality/README_STANDARDS.md` to `code/docs/standards/documentation/README_STANDARDS.md`
- [ ] Move `docs/maintenance/quality/CONTINUOUS_IMPROVEMENT.md` to `code/docs/standards/documentation/CONTINUOUS_IMPROVEMENT.md`
- [ ] Move `docs/maintenance/templates/README.md` to `code/docs/templates/documentation/README.md`
- [ ] Move `docs/maintenance/templates/README_TEMPLATE.md` to `code/docs/templates/documentation/README_TEMPLATE.md`
- [ ] Move `docs/maintenance/templates/THEORY_README.md` to `code/docs/templates/documentation/THEORY_README.md`
- [ ] Move `docs/maintenance/templates/SUBTHEORY_README.md` to `code/docs/templates/documentation/SUBTHEORY_README.md`
- [ ] Remove empty `docs/maintenance/` directory tree

**Timing**: 0.5 hours

**Files to modify**:
- All 11 files in `docs/maintenance/` hierarchy - move to new locations
- `docs/maintenance/`, `docs/maintenance/quality/`, `docs/maintenance/templates/` - remove empty directories

**Verification**:
- Run `ls -R code/docs/standards/` shows all moved files
- Run `ls -R code/docs/templates/documentation/` shows template files
- Confirm `docs/maintenance/` no longer exists
- Verify file count: 11 files should exist in new locations

---

### Phase 3: Update Internal References in Moved Files [COMPLETED]

**Goal**: Fix relative paths within the moved files that reference other documentation

**Tasks**:
- [ ] Update `code/docs/standards/README.md` - fix paths to quality/, templates/ subdirectories
- [ ] Update `code/docs/standards/documentation/README.md` - fix parent/sibling references
- [ ] Update template files - fix example paths and references
- [ ] Update any remaining relative path references in moved files

**Timing**: 0.5 hours

**Files to modify**:
- `code/docs/standards/README.md` - update internal navigation
- `code/docs/standards/documentation/*.md` - update relative paths
- `code/docs/templates/documentation/*.md` - update example paths

**Verification**:
- Grep for `maintenance/` in `code/docs/standards/` returns no results
- Grep for `../maintenance/` returns no results
- Manual review of README navigation links

---

### Phase 4: Update Cross-References Throughout Codebase [COMPLETED]

**Goal**: Update all references to `docs/maintenance/` across the entire codebase

**Tasks**:
- [ ] Search for `docs/maintenance` references in all markdown files
- [ ] Update references in `docs/README.md` (main documentation hub)
- [ ] Update references in `code/docs/README.md` (add standards section)
- [ ] Update references in `CLAUDE.md` and `.claude/CLAUDE.md` if present
- [ ] Update references in any other documentation files
- [ ] Search for and update any GitHub URL references to moved files

**Timing**: 1 hour

**Files to modify**:
- `docs/README.md` - remove maintenance section, add link to code/docs/standards
- `code/docs/README.md` - add Standards section with links to new content
- Any files containing `docs/maintenance/` paths

**Verification**:
- `grep -r "docs/maintenance" --include="*.md" .` returns no results
- `grep -r "maintenance/quality" --include="*.md" .` returns no results
- `grep -r "maintenance/templates" --include="*.md" .` returns no results

---

### Phase 5: Update Navigation and Finalize [COMPLETED]

**Goal**: Ensure documentation navigation is complete and consistent

**Tasks**:
- [ ] Update `docs/README.md` to reflect new structure (remove Maintenance section)
- [ ] Update `code/docs/README.md` to include Standards section
- [ ] Verify all README.md files have valid navigation
- [ ] Create implementation summary documenting all changes

**Timing**: 0.75 hours

**Files to modify**:
- `docs/README.md` - restructure navigation
- `code/docs/README.md` - add navigation to standards and templates/documentation

**Verification**:
- Review `docs/README.md` has no broken internal links
- Review `code/docs/README.md` has complete navigation
- All moved files are discoverable from documentation root

## Testing & Validation

- [ ] All 11 files successfully moved to new locations
- [ ] No references to `docs/maintenance/` remain in codebase
- [ ] `docs/README.md` navigation works correctly
- [ ] `code/docs/README.md` navigation includes new standards section
- [ ] Git history preserved for moved files (use `git mv`)
- [ ] No empty directories remain in `docs/`

## Artifacts & Outputs

- Moved files: 11 files from `docs/maintenance/` to `code/docs/standards/` and `code/docs/templates/documentation/`
- Updated files: `docs/README.md`, `code/docs/README.md`, plus any files with cross-references
- Deleted: `docs/maintenance/` directory (after contents moved)
- Implementation summary: `specs/030_consolidate_documentation/summaries/implementation-summary-{DATE}.md`

## Rollback/Contingency

If implementation fails or causes issues:
1. Use `git checkout HEAD~1 -- docs/ code/docs/` to restore previous state
2. Git history preserves all original file locations
3. No data loss possible since files are moved, not deleted
4. Can incrementally roll back individual phases if needed
