# Consolidate specs/ Directories Implementation Plan

## Metadata
- **Date**: 2025-09-30
- **Feature**: Consolidate all specs/ directories into project root
- **Scope**: Directory reorganization and documentation update
- **Estimated Phases**: 3
- **Standards File**: /home/benjamin/Documents/Philosophy/Projects/ModelChecker/CLAUDE.md
- **Related Research**: specs/research/101_slash_command_document_placement.md

## Overview

This plan consolidates all `specs/` directories scattered throughout the project into a single, canonical location at the project root (`./specs/`). This simplifies the specs organization and ensures all slash commands (`/report`, `/plan`, `/debug`, etc.) consistently use the same location.

### Current State

The project has 4 `specs/` directories:
1. `./specs/` (root) - 7 subdirectories with ~80+ documents
2. `./Code/specs/` - 5 documents (1 plan, 3 reports, 1 summary)
3. `./Code/src/model_checker/theory_lib/specs/` - 10 documents (1 plan, 2 prompts, 6 reports, 1 guide)
4. `./Docs/specs/` - 1 document (1 plan)

**Total non-root documents**: 16 files to migrate

### Desired State

- Single `./specs/` directory at project root
- All documents consolidated with proper numbering
- Updated documentation reflecting single location
- No duplicate or conflicting directory structures

## Success Criteria

- [ ] All documents from non-root specs/ moved to ./specs/
- [ ] Sequential numbering maintained without conflicts
- [ ] All cross-references updated to new locations
- [ ] Empty specs/ directories removed
- [ ] Documentation (CLAUDE.md, specs/README.md) updated
- [ ] Slash commands verified to work with single location
- [ ] Git history preserved with `git mv` commands

## Technical Design

### Migration Strategy

1. **Preserve Numbering**: Documents with sequential numbers keep their numbers
2. **Prevent Conflicts**: Check for number collisions before moving
3. **Update References**: Find and update any hard-coded paths
4. **Atomic Operations**: Use `git mv` to preserve history
5. **Validation**: Verify no broken links after migration

### Document Categories

The root `./specs/` already has:
- `baselines/` - Test regression baselines
- `debug/` - Debugging analyses (22 files)
- `findings/` - Lessons learned (16 files)
- `fixes/` - Bug fix documentation (9 files)
- `implementation/` - Implementation summaries (2 files)
- `plans/` - Implementation plans (51 files)
- `research/` - Research reports (101 files including newly created)

### Migration Mapping

| Source | Destination | Count |
|--------|------------|-------|
| `Code/specs/plans/` | `specs/plans/` | 1 file |
| `Code/specs/reports/` | `specs/research/` | 3 files |
| `Code/specs/summaries/` | `specs/implementation/` | 1 file |
| `Code/src/model_checker/theory_lib/specs/plans/` | `specs/plans/` | 1 file |
| `Code/src/model_checker/theory_lib/specs/prompts/` | `specs/prompts/` (new) | 2 files |
| `Code/src/model_checker/theory_lib/specs/reports/` | `specs/research/` | 6 files |
| `Code/src/model_checker/theory_lib/specs/*.md` | `specs/guides/` (new) | 1 file |
| `Docs/specs/plans/` | `specs/plans/` | 1 file |

**Note**: "reports" → "research" mapping follows existing root convention

## Implementation Phases

### Phase 1: Pre-Migration Analysis and Setup
**Objective**: Prepare for migration by analyzing numbering conflicts and creating necessary directories
**Complexity**: Low

Tasks:
- [ ] List all numbered files in non-root specs/ directories
- [ ] Check for numbering conflicts with existing ./specs/ files
- [ ] Create new subdirectories if needed: `specs/prompts/`, `specs/guides/`
- [ ] Document the migration mapping in a temporary migration log
- [ ] Create backup of current state: `git stash` or tag current commit

Testing:
```bash
# Verify all source files are accounted for
find ./Code/specs ./Code/src/model_checker/theory_lib/specs ./Docs/specs -type f -name "*.md" | wc -l
# Should show 16 files

# Check for numbering conflicts
for file in $(find ./Code/specs -name "[0-9][0-9][0-9]_*.md"); do
    basename "$file"
done | sort
# Compare against existing specs/plans/ and specs/research/ numbers

# Verify target directories exist
ls -ld ./specs/plans ./specs/research ./specs/implementation
```

### Phase 2: Execute Migration
**Objective**: Move all files from non-root specs/ to ./specs/ using git mv
**Complexity**: Medium

Tasks:
- [ ] Migrate Code/specs/plans/001_fix_test_failures.md → specs/plans/
- [ ] Migrate Code/specs/reports/00{1,2,3}_*.md → specs/research/ with renumbering
- [ ] Migrate Code/specs/summaries/001_implementation_summary.md → specs/implementation/
- [ ] Migrate theory_lib/specs/plans/001_complete_theory_refactoring.md → specs/plans/
- [ ] Create specs/prompts/ directory
- [ ] Migrate theory_lib/specs/prompts/*.md → specs/prompts/
- [ ] Migrate theory_lib/specs/reports/*.md → specs/research/ with renumbering
- [ ] Create specs/guides/ directory
- [ ] Migrate theory_lib/specs/subagent-refactoring-guide.md → specs/guides/
- [ ] Migrate Docs/specs/plans/documentation_revision_plan.md → specs/plans/
- [ ] Remove empty specs/ directories: Code/specs/, theory_lib/specs/, Docs/specs/

Testing:
```bash
# Verify all files moved successfully
find ./Code/specs ./Code/src/model_checker/theory_lib/specs ./Docs/specs -type f -name "*.md" 2>/dev/null
# Should return nothing

# Verify files in new locations
ls ./specs/plans/ | wc -l
ls ./specs/research/ | wc -l
ls ./specs/prompts/
ls ./specs/guides/

# Check git status shows moves, not deletions+additions
git status
# Should show "renamed:" entries
```

### Phase 3: Update Documentation and Validation
**Objective**: Update all references to specs/ directories and validate the consolidation
**Complexity**: Medium

Tasks:
- [ ] Update CLAUDE.md to reference single ./specs/ directory
- [ ] Update specs/README.md to remove multi-level structure documentation
- [ ] Add specs/prompts/README.md to explain prompt templates
- [ ] Add specs/guides/README.md to explain development guides
- [ ] Search for hardcoded paths to removed specs/ directories and update
- [ ] Verify slash commands work correctly with consolidated structure
- [ ] Update recent research report (101_slash_command_document_placement.md) with note about consolidation
- [ ] Test /report, /plan, /debug commands to ensure they use ./specs/
- [ ] Commit all changes with descriptive message

Testing:
```bash
# Search for remaining references to old paths
grep -r "Code/specs" --include="*.md" .
grep -r "theory_lib/specs" --include="*.md" .
grep -r "Docs/specs" --include="*.md" .

# Test slash commands (manual verification)
# 1. Run: /list-plans
# 2. Run: /list-reports
# 3. Verify all documents are found

# Final validation
git status
git diff --staged
# Review all changes before committing
```

## Detailed File Migration Plan

### From Code/specs/

| File | Target | Action |
|------|--------|--------|
| `plans/001_fix_test_failures.md` | `specs/plans/` | Check if 001 exists; renumber if needed |
| `reports/001_debug_test_failures.md` | `specs/research/` | Renumber to next available (102) |
| `reports/002_remaining_test_failures.md` | `specs/research/` | Renumber to next available (103) |
| `reports/003_comprehensive_test_fixes.md` | `specs/research/` | Renumber to next available (104) |
| `summaries/001_implementation_summary.md` | `specs/implementation/` | Renumber to next available (003) |

### From Code/src/model_checker/theory_lib/specs/

| File | Target | Action |
|------|--------|--------|
| `plans/001_complete_theory_refactoring.md` | `specs/plans/` | Renumber if 001 conflicts |
| `prompts/refactor_theories_prompt.md` | `specs/prompts/` | Keep name |
| `prompts/analyze_theories_prompt.md` | `specs/prompts/` | Keep name |
| `reports/imposition_analysis.md` | `specs/research/` | Add number (105) |
| `reports/001_refactoring_implementation_status.md` | `specs/research/` | Renumber (106) |
| `reports/summary_analysis.md` | `specs/research/` | Add number (107) |
| `reports/logos_analysis.md` | `specs/research/` | Add number (108) |
| `reports/002_theory_lib_refactor_compliance_assessment.md` | `specs/research/` | Renumber (109) |
| `reports/exclusion_analysis.md` | `specs/research/` | Add number (110) |
| `subagent-refactoring-guide.md` | `specs/guides/` | Keep name |

### From Docs/specs/

| File | Target | Action |
|------|--------|--------|
| `plans/documentation_revision_plan.md` | `specs/plans/` | Add number if unnumbered |

## Numbering Resolution

### Current Highest Numbers
- `specs/plans/`: 051 (subtheory-cli-implementation.md is unnumbered)
- `specs/research/`: 101 (just created)
- `specs/implementation/`: 019

### Assigned Numbers
- Code/specs/plans/001 → **Keep 001** or renumber to 052 (check conflict)
- theory_lib/specs/plans/001 → **Renumber to 053**
- Docs/specs/plans/documentation_revision_plan → **Assign 054**
- Code/specs/reports/001 → **Renumber to 102**
- Code/specs/reports/002 → **Renumber to 103**
- Code/specs/reports/003 → **Renumber to 104**
- theory_lib reports (unnumbered) → **105-110**
- theory_lib reports (numbered) → **Renumber accordingly**
- Code/specs/summaries/001 → **Renumber to 020**

## Testing Strategy

### Pre-Migration Tests
1. Count all files to be migrated
2. Verify no uncommitted changes that could be lost
3. Check for external references to specs/ paths

### Post-Migration Tests
1. Verify all source directories are empty
2. Confirm all files present in ./specs/
3. Check git history preserved with `git log --follow`
4. Test slash commands:
   - `/list-plans` shows all plans
   - `/list-reports` shows all research
   - `/plan "test feature"` creates in ./specs/plans/
   - `/report "test topic"` creates in ./specs/research/

### Validation Criteria
- Zero files remain in non-root specs/ directories
- All migrated files accessible and readable
- Git history shows "renamed" not "deleted + added"
- Documentation updated to reflect new structure
- No broken cross-references between documents

## Documentation Requirements

### Files to Update

1. **CLAUDE.md**
   - Update "Specs Directory Protocol" section
   - Remove references to multi-level specs/
   - Clarify single location policy

2. **specs/README.md**
   - Remove "Multi-Level Specs Organization" section
   - Update directory structure listing
   - Add new subdirectories: prompts/, guides/

3. **New Files to Create**
   - `specs/prompts/README.md` - Explain prompt template usage
   - `specs/guides/README.md` - Explain development guides

4. **Update Existing Research**
   - Add note to `specs/research/101_slash_command_document_placement.md`
   - Document that consolidation supersedes original recommendations

## Dependencies

- Git for version control (mv commands)
- Bash for scripting and file operations
- No external dependencies

## Risk Assessment

### Low Risk
- File operations are reversible with git
- Small number of files (16 total)
- No code changes, only file moves

### Mitigation Strategies
1. **Backup**: Create git tag before migration
2. **Atomic Commits**: Commit moves in logical groups
3. **Validation**: Test after each phase before proceeding
4. **Rollback Plan**: If issues arise, use `git reset --hard <tag>`

## Notes

### Why Consolidate?

**Reasons for single specs/ directory:**
1. **Simplicity**: Easier to find all documentation in one place
2. **Consistency**: All slash commands use same location
3. **Discoverability**: New developers check one location, not four
4. **Tooling**: Simpler patterns for /list-plans and /list-reports
5. **Maintenance**: Single README to keep updated

### Alternative Considered (and Rejected)

The research report (101) originally recommended multi-level specs/ with automatic location detection. However:
- Adds complexity to slash command prompts
- Requires sophisticated path calculation algorithms
- Benefits unclear for this project size
- Single location is more maintainable

### Future Considerations

If project grows significantly, could reconsider multi-level approach. For now, single location provides best balance of simplicity and organization.

## Git Commit Message Template

```
Consolidate specs/ directories to project root

- Migrate 5 documents from Code/specs/ to ./specs/
- Migrate 10 documents from theory_lib/specs/ to ./specs/
- Migrate 1 document from Docs/specs/ to ./specs/
- Create new subdirectories: prompts/, guides/
- Renumber documents to avoid conflicts (001-110 in research/)
- Update CLAUDE.md and specs/README.md
- Remove empty specs/ directories

All files moved with `git mv` to preserve history.
Refs: specs/research/101_slash_command_document_placement.md

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
```

## Success Metrics

- **Migration Completeness**: 16/16 files successfully moved
- **History Preservation**: 100% of files show "renamed" in git log
- **Broken Links**: 0 broken cross-references
- **Command Functionality**: All slash commands work correctly
- **Documentation Accuracy**: All docs reflect new structure

## Post-Implementation Actions

1. Monitor for any issues with slash commands
2. Update any external documentation (if exists)
3. Notify collaborators of new structure
4. Consider updating .gitignore if it mentions old specs/ paths
