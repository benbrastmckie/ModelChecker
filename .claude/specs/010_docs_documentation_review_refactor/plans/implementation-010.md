# Implementation Plan: Task #10

**Task**: Docs Documentation Review and Refactor
**Version**: 001
**Created**: 2026-01-11
**Language**: general

## Overview

Systematically refactor the Docs/ documentation (~19,400 lines across 49 files) to eliminate ghost file references, fix broken links, consolidate redundant content, and condense overly long files. Work proceeds in phases from critical fixes to structural improvements, with verification at each stage.

## Phases

### Phase 1: Fix Critical Broken References

**Status**: [NOT STARTED]

**Objectives**:
1. Remove ghost file references from maintenance/README.md
2. Fix incorrect filename references in Docs/README.md
3. Update directory structure displays to match reality

**Files to modify**:
- `Docs/maintenance/README.md` - Remove 7 non-existent file references
- `Docs/README.md` - Fix SYNTAX.md → SYNTACTIC.md, ITERATOR.md → ITERATE.md

**Steps**:
1. Edit Docs/maintenance/README.md:
   - Remove CODE_ORGANIZATION.md, ERROR_HANDLING.md, EXAMPLES_STRUCTURE.md, FORMULA_FORMATTING.md, PERFORMANCE.md, TESTING_STANDARDS.md, UNICODE_GUIDELINES.md from directory tree
   - Update file counts and descriptions to match actual 3 files + 2 subdirectories
   - Remove references to non-existent files in Documentation section
2. Edit Docs/README.md:
   - Fix architecture/SYNTAX.md → architecture/SYNTACTIC.md
   - Fix architecture/ITERATOR.md → architecture/ITERATE.md
3. Verify all internal links in both files are valid

**Verification**:
- All file references in maintenance/README.md exist
- All file references in Docs/README.md exist
- No broken navigation links

---

### Phase 2: Consolidate Redundant Settings Documentation

**Status**: [NOT STARTED]

**Objectives**:
1. Clearly differentiate architecture vs usage perspectives for Settings
2. Remove duplicate content while preserving both documents' value
3. Establish cross-reference pattern for similar overlaps

**Files to modify**:
- `Docs/architecture/SETTINGS.md` (1,322 lines) - Condense to architecture focus
- `Docs/usage/SETTINGS.md` (336 lines) - Ensure practical focus, remove architecture overlap

**Steps**:
1. Analyze content overlap between the two files
2. In architecture/SETTINGS.md:
   - Keep: Inheritance architecture, component diagrams, design decisions
   - Remove: User-facing configuration examples (covered in usage/)
   - Target: ~600 lines (halve current length)
3. In usage/SETTINGS.md:
   - Keep: Practical configuration, CLI flags, common configurations
   - Add clear "Architecture Deep Dive" link for those wanting more
   - Ensure no redundant diagrams
4. Verify cross-references are correct

**Verification**:
- architecture/SETTINGS.md under 700 lines
- No duplicate diagrams between files
- Clear scope distinction documented at top of each file

---

### Phase 3: Consolidate Output Documentation

**Status**: [NOT STARTED]

**Objectives**:
1. Eliminate redundancy between architecture/OUTPUT.md and usage/OUTPUT.md
2. Apply same pattern as Settings consolidation

**Files to modify**:
- `Docs/architecture/OUTPUT.md` (460 lines) - Focus on architecture
- `Docs/usage/OUTPUT.md` (459 lines) - Focus on practical usage

**Steps**:
1. Compare content of both OUTPUT.md files
2. Deduplicate shared content, keeping architecture in architecture/ and usage in usage/
3. Add clear cross-references between files
4. Target combined reduction of ~200 lines

**Verification**:
- No duplicate content between files
- Each file has distinct purpose documented
- Cross-references work correctly

---

### Phase 4: Condense Oversized Architecture Files

**Status**: [NOT STARTED]

**Objectives**:
1. Reduce MODELS.md from 1,375 to under 800 lines
2. Reduce SEMANTICS.md from 1,362 to under 800 lines
3. Reduce ITERATE.md from 1,141 to under 700 lines

**Files to modify**:
- `Docs/architecture/MODELS.md` - Condense
- `Docs/architecture/SEMANTICS.md` - Condense
- `Docs/architecture/ITERATE.md` - Condense

**Steps**:
1. For each file:
   - Remove excessive ASCII diagrams (keep essential ones)
   - Consolidate repetitive explanations
   - Move implementation details to Code/docs references
   - Remove code examples (architecture docs should be conceptual per stated goals)
2. MODELS.md: Focus on model structure concepts, remove detailed constraint explanations
3. SEMANTICS.md: Focus on semantic framework, defer implementation to Code/docs
4. ITERATE.md: Focus on iteration concepts, condense algorithm explanations

**Verification**:
- MODELS.md under 800 lines
- SEMANTICS.md under 800 lines
- ITERATE.md under 700 lines
- All files still convey key concepts

---

### Phase 5: Clean Up Installation Directory

**Status**: [NOT STARTED]

**Objectives**:
1. Evaluate and reorganize peripheral installation files
2. Update installation/README.md to accurately reflect contents

**Files to review**:
- `Docs/installation/CLAUDE_TEMPLATE.md` (217 lines) - Evaluate necessity
- `Docs/installation/GIT_GOING.md` (474 lines) - Consider moving/removing
- `Docs/installation/README.md` - Update if files change

**Steps**:
1. Review CLAUDE_TEMPLATE.md:
   - If superseded by CLAUDE_CODE.md, remove or merge
   - If distinct purpose, clarify in installation/README.md
2. Review GIT_GOING.md:
   - This is a general Git tutorial, tangential to ModelChecker
   - Either condense to ModelChecker-specific Git usage or remove
   - If kept, add clear note that it's supplementary material
3. Update installation/README.md directory listing if changes made

**Verification**:
- Each file in installation/ has clear, documented purpose
- No redundant overlapping tutorials
- README accurately reflects directory contents

---

### Phase 6: Update Maintenance Documentation Structure

**Status**: [NOT STARTED]

**Objectives**:
1. Align maintenance/README.md with actual available content
2. Decide on future of aspirational standards files

**Files to modify**:
- `Docs/maintenance/README.md` - Already partially fixed in Phase 1
- `Docs/maintenance/AUDIENCE.md` - Review for relevance
- `Docs/maintenance/VERSION_CONTROL.md` - Review for relevance

**Steps**:
1. Review what maintenance/README.md promises vs delivers
2. Evaluate if AUDIENCE.md and VERSION_CONTROL.md are actively used
3. If standards are aspirational but unimplemented:
   - Either create minimal versions
   - Or remove references entirely
   - Or mark as "Planned: Not yet implemented"
4. Ensure quality/ and templates/ subdirectories are properly documented

**Verification**:
- maintenance/README.md describes only what exists
- Clear distinction between implemented and planned standards
- No broken internal links

---

### Phase 7: Final Verification and Link Check

**Status**: [NOT STARTED]

**Objectives**:
1. Verify all internal links across Docs/
2. Verify cross-references to Code/docs/
3. Update file counts and statistics in README files

**Files to review**:
- All README.md files in Docs/
- Key cross-reference files

**Steps**:
1. Scan all markdown files for internal links
2. Verify each link target exists
3. Update any stale Code/docs references
4. Update file/line counts in hub README files
5. Archive or update Docs/specs/plans/documentation_revision_plan.md

**Verification**:
- Zero broken internal links
- All README file counts accurate
- Cross-references to Code/docs verified

---

## Dependencies

- None - this is documentation-only refactoring
- No code changes required
- No external dependencies

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing content users rely on | Med | Low | Keep original in git history, can restore |
| Breaking external links | Med | Low | Only modifying internal structure |
| Condensing removes important info | Med | Med | Focus on removing redundancy, not content |

## Success Criteria

- [ ] Zero ghost file references in any README
- [ ] All internal links verified working
- [ ] Total Docs/ line count reduced by 15-25% (~3,000-5,000 lines)
- [ ] No file over 1,000 lines (except possibly MODELS.md)
- [ ] Clear content separation between architecture/ and usage/
- [ ] maintenance/README.md accurately describes available files

## Rollback Plan

All changes are to markdown files tracked in git. If any phase causes issues:
1. Identify problematic commit with `git log`
2. Revert specific files with `git checkout <commit> -- <file>`
3. Or full rollback with `git revert <commit>`
