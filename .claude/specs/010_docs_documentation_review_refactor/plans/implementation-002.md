# Implementation Plan: Task #10

**Task**: Docs Documentation Review and Refactor
**Version**: 002
**Created**: 2026-01-11
**Revision of**: implementation-010.md
**Reason**: Rename GIT_GOING.md to USING_GIT.md; prioritize preserving important content; focus on reducing redundancy, eliminating inconsistencies and broken links, and adding useful cross-links.

## Revision Summary

### Key Changes from Version 001
1. **Preserve content**: Removed aggressive line count targets; focus on removing duplicates and inconsistencies, not content reduction for its own sake
2. **GIT_GOING.md**: Rename to USING_GIT.md instead of evaluating removal
3. **Cross-linking emphasis**: Added explicit cross-link additions throughout phases
4. **Link verification**: Moved to per-phase verification instead of final-only check
5. **Softer targets**: Changed "reduce to X lines" to "remove redundant content" with verification

## Overview

Refactor the Docs/ documentation to eliminate ghost file references, fix broken links, reduce redundancy (not content), and improve navigation through strategic cross-links. The goal is clarity and consistency, not minimizing line counts.

## Phases

### Phase 1: Fix Critical Broken References

**Status**: [NOT STARTED]

**Objectives**:
1. Remove ghost file references from maintenance/README.md
2. Fix incorrect filename references in Docs/README.md
3. Update directory structure displays to match reality
4. Verify all links work before proceeding

**Files to modify**:
- `Docs/maintenance/README.md` - Remove 7 non-existent file references
- `Docs/README.md` - Fix SYNTAX.md → SYNTACTIC.md, ITERATOR.md → ITERATE.md

**Steps**:
1. Edit Docs/maintenance/README.md:
   - Remove from directory tree: CODE_ORGANIZATION.md, ERROR_HANDLING.md, EXAMPLES_STRUCTURE.md, FORMULA_FORMATTING.md, PERFORMANCE.md, TESTING_STANDARDS.md, UNICODE_GUIDELINES.md
   - Update to show actual structure: 3 files (README.md, AUDIENCE.md, VERSION_CONTROL.md) + 2 subdirectories (quality/, templates/)
   - Remove references to non-existent files in Documentation section
   - Preserve all existing content about standards, just remove broken references
2. Edit Docs/README.md:
   - Fix architecture/SYNTAX.md → architecture/SYNTACTIC.md
   - Fix architecture/ITERATOR.md → architecture/ITERATE.md
3. Verify all internal links in both files are valid

**Verification**:
- All file references in maintenance/README.md exist
- All file references in Docs/README.md exist
- Run: `grep -r "\.md" Docs/README.md Docs/maintenance/README.md | grep -v "^#"` and verify each target

---

### Phase 2: Rename GIT_GOING.md and Update References

**Status**: [NOT STARTED]

**Objectives**:
1. Rename GIT_GOING.md to USING_GIT.md for clearer naming
2. Update all references to the renamed file
3. Add cross-link from maintenance/VERSION_CONTROL.md

**Files to modify**:
- `Docs/installation/GIT_GOING.md` → `Docs/installation/USING_GIT.md` (rename)
- `Docs/installation/README.md` - Update reference
- `Docs/maintenance/VERSION_CONTROL.md` - Add cross-link to USING_GIT.md

**Steps**:
1. Rename file: `git mv Docs/installation/GIT_GOING.md Docs/installation/USING_GIT.md`
2. Search for all references to GIT_GOING.md:
   - `grep -r "GIT_GOING" Docs/`
3. Update each reference to USING_GIT.md
4. In installation/README.md:
   - Update directory listing
   - Update any descriptive text mentioning the file
5. In maintenance/VERSION_CONTROL.md:
   - Add "See Also" section with link: `[Using Git](../installation/USING_GIT.md)` for practical Git commands

**Verification**:
- `grep -r "GIT_GOING" Docs/` returns no results
- `Docs/installation/USING_GIT.md` exists
- Cross-link from VERSION_CONTROL.md works

---

### Phase 3: Consolidate Redundant Settings Documentation

**Status**: [NOT STARTED]

**Objectives**:
1. Remove duplicate diagrams and explanations between architecture/SETTINGS.md and usage/SETTINGS.md
2. Keep both files with their distinct purposes
3. Add clear cross-references between them

**Files to modify**:
- `Docs/architecture/SETTINGS.md` (1,322 lines)
- `Docs/usage/SETTINGS.md` (336 lines)

**Steps**:
1. Identify duplicated content:
   - Compare the 5-level hierarchy diagrams
   - Compare code examples showing same configurations
2. In architecture/SETTINGS.md:
   - Keep: Inheritance diagrams, component architecture, design rationale
   - Remove: User-facing configuration examples that duplicate usage/SETTINGS.md
   - Add at top: "For practical configuration, see [Settings Guide](../usage/SETTINGS.md)"
3. In usage/SETTINGS.md:
   - Keep all practical content (this is the user-facing reference)
   - Add at top: "For architecture details, see [Settings Architecture](../architecture/SETTINGS.md)"
   - Remove any architecture diagrams that duplicate the architecture version
4. Verify both files have distinct, complementary content

**Verification**:
- No identical diagrams appear in both files
- Each file has clear scope statement at top
- Cross-references link correctly
- No information is lost, only duplicates removed

---

### Phase 4: Consolidate Redundant Output Documentation

**Status**: [NOT STARTED]

**Objectives**:
1. Remove duplicate content between architecture/OUTPUT.md and usage/OUTPUT.md
2. Add cross-references between files

**Files to modify**:
- `Docs/architecture/OUTPUT.md` (460 lines)
- `Docs/usage/OUTPUT.md` (459 lines)

**Steps**:
1. Compare the two OUTPUT.md files for overlap
2. Determine which content belongs where:
   - Architecture: Output system design, component interaction, format extensibility
   - Usage: How to use output options, save formats, command examples
3. Remove duplicates (keep in appropriate file)
4. Add cross-reference headers:
   - architecture/OUTPUT.md: "For practical usage, see [Output Guide](../usage/OUTPUT.md)"
   - usage/OUTPUT.md: "For output architecture, see [Output Architecture](../architecture/OUTPUT.md)"

**Verification**:
- No significant duplicate content
- Cross-references work
- Both files remain useful for their intended audience

---

### Phase 5: Review and Cross-link Semantics Documentation

**Status**: [NOT STARTED]

**Objectives**:
1. Review architecture/SEMANTICS.md and usage/SEMANTICS.md for redundancy
2. Add cross-references without removing important content

**Files to modify**:
- `Docs/architecture/SEMANTICS.md` (1,362 lines)
- `Docs/usage/SEMANTICS.md` (528 lines)

**Steps**:
1. Review both files:
   - architecture/SEMANTICS.md: Likely covers semantic framework design
   - usage/SEMANTICS.md: Likely covers constraint testing methodology
2. These may have minimal overlap (different purposes)
3. Add cross-references if not already present:
   - Each file should reference the other for complementary information
4. Only remove content if clearly duplicated (not just similar topics)

**Verification**:
- Cross-references exist between files
- No broken links
- Important content preserved

---

### Phase 6: Update Maintenance Documentation

**Status**: [NOT STARTED]

**Objectives**:
1. Ensure maintenance/README.md accurately describes available content
2. Add cross-links where useful
3. Keep existing AUDIENCE.md and VERSION_CONTROL.md content

**Files to modify**:
- `Docs/maintenance/README.md` (from Phase 1, further review)
- `Docs/maintenance/AUDIENCE.md` - Review and add cross-links
- `Docs/maintenance/VERSION_CONTROL.md` - Already modified in Phase 2

**Steps**:
1. Verify maintenance/README.md now matches reality after Phase 1
2. In AUDIENCE.md:
   - Verify content is accurate and useful
   - Add cross-links to relevant usage/ or architecture/ docs if helpful
3. Verify quality/ and templates/ subdirectories are properly referenced
4. Add any missing cross-links between maintenance docs and main docs

**Verification**:
- maintenance/README.md directory tree matches `ls Docs/maintenance/`
- All internal links work
- Cross-links to related docs exist

---

### Phase 7: Review Installation Directory

**Status**: [NOT STARTED]

**Objectives**:
1. Ensure all installation files have clear purpose
2. Add cross-links where useful
3. Evaluate CLAUDE_TEMPLATE.md relationship to CLAUDE_CODE.md

**Files to review**:
- `Docs/installation/CLAUDE_TEMPLATE.md` (217 lines)
- `Docs/installation/CLAUDE_CODE.md` (325 lines)
- `Docs/installation/README.md`

**Steps**:
1. Review CLAUDE_TEMPLATE.md:
   - Determine if it's a template or a guide
   - If it complements CLAUDE_CODE.md, add cross-references
   - If it duplicates content, merge into CLAUDE_CODE.md
2. Ensure installation/README.md accurately describes all files
3. Add cross-links between related installation guides:
   - BASIC_INSTALLATION.md ↔ TROUBLESHOOTING.md
   - DEVELOPER_SETUP.md ↔ VIRTUAL_ENVIRONMENTS.md
   - JUPYTER_SETUP.md ↔ GETTING_STARTED.md (if relevant)

**Verification**:
- Each file's purpose is clear
- Cross-links improve navigation
- README accurately lists all files

---

### Phase 8: Final Link Verification

**Status**: [NOT STARTED]

**Objectives**:
1. Comprehensive verification of all internal links in Docs/
2. Verify cross-references to Code/docs/
3. Update any outdated file counts in README files

**Steps**:
1. Extract all markdown links from Docs/:
   ```bash
   grep -roh '\[.*\](.*\.md)' Docs/ | sort -u
   ```
2. Verify each link target exists
3. Check Code/docs references are valid
4. Update Docs/README.md file counts if changed
5. Archive or update Docs/specs/plans/documentation_revision_plan.md

**Verification**:
- Zero broken internal links
- All Code/docs references valid
- File counts in README files are accurate

---

## Dependencies

- None - documentation-only refactoring
- No code changes required

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing important content accidentally | High | Low | Focus on duplicates only; git history preserves original |
| Breaking links during rename | Med | Med | Grep for old names immediately after rename |
| Missing cross-link opportunities | Low | Med | Final verification phase catches issues |

## Success Criteria

- [ ] Zero ghost file references
- [ ] Zero broken internal links
- [ ] GIT_GOING.md renamed to USING_GIT.md
- [ ] No duplicate diagrams between architecture/ and usage/ counterparts
- [ ] Cross-references added between related architecture/ and usage/ files
- [ ] maintenance/README.md accurately describes available files
- [ ] All important content preserved (redundancy reduced, not information)

## Rollback Plan

All changes are markdown files tracked in git:
1. Identify problematic commit: `git log --oneline Docs/`
2. Revert specific files: `git checkout <commit> -- Docs/path/to/file.md`
3. For rename rollback: `git mv Docs/installation/USING_GIT.md Docs/installation/GIT_GOING.md`
