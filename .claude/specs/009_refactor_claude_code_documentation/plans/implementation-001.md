# Implementation Plan: Task #9

**Task**: Refactor CLAUDE_CODE.md documentation
**Version**: 001
**Created**: 2026-01-11
**Language**: general

## Overview

Restructure CLAUDE_CODE.md to provide a clear progression for new users: install Claude Code, install ModelChecker, set up agent system, use GitHub CLI. Reduce document from 765 lines to ~400-500 lines by consolidating examples, removing duplicates, and linking to specialized guides. This also addresses task #7 by adding gh CLI for issue creation.

## Phases

### Phase 1: Restructure Document with New Section Order

**Status**: [COMPLETED]

**Objectives**:
1. Rewrite CLAUDE_CODE.md with numbered sections showing progression
2. Move agent system setup to section 4 (after install/test)
3. Condense Claude Code installation sections
4. Keep authentication section compact

**Files to modify**:
- `Docs/installation/CLAUDE_CODE.md` - Complete rewrite with new structure

**Target Structure**:
```
1. Getting Started (intro, what is Claude Code, prerequisites)
2. Install Claude Code (platform-specific, condensed)
3. Install ModelChecker (automated install, test example)
4. Set Up the Agent System (.claude/ copy, restart, link to docs)
5. Using gh CLI for GitHub (install gh, create issues, submit PRs)
6. Tips and Troubleshooting (condensed)
7. Next Steps (links to guides)
```

**Steps**:
1. Create new document structure with numbered sections
2. Write Section 1 (Getting Started) - 30 lines
3. Write Section 2 (Install Claude Code) - 80 lines (from 75 lines, condense)
4. Write Section 3 (Install ModelChecker) - 80 lines (from 80 lines, keep)
5. Write Section 4 (Agent System) - 60 lines (moved and expanded from end)
6. Preserve header/footer navigation links

**Verification**:
- Document has clear numbered sections
- Agent system setup is in Section 4
- First 4 sections complete

---

### Phase 2: Consolidate GitHub Section and Add Issue Creation

**Status**: [COMPLETED]

**Objectives**:
1. Write Section 5 (gh CLI for GitHub) - consolidated from multiple sections
2. Add issue creation workflow (addresses task #7)
3. Keep only 2-3 focused examples
4. Remove duplicate/similar PR examples

**Files to modify**:
- `Docs/installation/CLAUDE_CODE.md` - Section 5

**Steps**:
1. Write gh CLI installation subsection (ask Claude to install)
2. Write authentication subsection
3. Write "Creating Issues" subsection - emphasize for reporting problems
4. Write "Creating Pull Requests" subsection - one focused example
5. Add link to GIT_GOING.md for comprehensive Git/GitHub info
6. Remove: "Viewing and Managing Pull Requests", "Collaborating on Main Repository", "Syncing Fork", redundant PR examples

**Verification**:
- Section 5 covers: install gh, auth, create issue, create PR
- Links to GIT_GOING.md for full GitHub docs
- No more than 3 workflow examples total

---

### Phase 3: Finalize Tips, Troubleshooting, and Cross-Links

**Status**: [COMPLETED]

**Objectives**:
1. Write Section 6 (Tips and Troubleshooting) - condensed
2. Write Section 7 (Next Steps) - clean links section
3. Verify all cross-links work
4. Remove CLAUDE.md template section (relocated concept)

**Files to modify**:
- `Docs/installation/CLAUDE_CODE.md` - Sections 6-7, final cleanup

**Steps**:
1. Condense "Tips for Effective Use" to 3-4 key tips
2. Keep essential troubleshooting (Claude Code, auth, Python, gh)
3. Remove "Advanced Features" section (CLAUDE.md template - out of scope)
4. Write "Next Steps" with clear links:
   - GETTING_STARTED.md - Using ModelChecker
   - GIT_GOING.md - Git/GitHub details
   - BASIC_INSTALLATION.md - Manual installation
   - .claude/docs/README.md - Agent system docs
5. Verify all internal links are valid
6. Check document length is in 400-500 line range

**Verification**:
- Document is 400-500 lines (from 765)
- All cross-links work
- No CLAUDE.md template section
- Clean progression from start to finish

---

## Dependencies

- Research report completed (done)
- Current CLAUDE_CODE.md content understood
- Related docs: GETTING_STARTED.md, GIT_GOING.md, copy-claude-directory.md

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Document too short | Med | Low | Keep all essential content, just reorganize |
| Broken links | Med | Med | Verify each link after editing |
| Missing content | Med | Low | Reference original during rewrite |

## Success Criteria

- [ ] Document follows numbered progression (1-7 sections)
- [ ] Agent system setup is Section 4 (prominent)
- [ ] gh CLI includes issue creation workflow
- [ ] Document is 400-500 lines (reduced from 765)
- [ ] All cross-links verified working
- [ ] No CLAUDE.md template section (removed)

## Rollback Plan

Git revert to previous commit if new structure is rejected. Original content is preserved in git history.

## Note on Task #7

This implementation addresses Task #7 ("Document gh CLI setup and issue creation") as part of Section 5. After this task completes, Task #7 should be marked as completed or abandoned with a note that it was absorbed into Task #9.
