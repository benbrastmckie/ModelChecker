# Implementation Plan: Task #4

**Task**: Reorganize Claude Code documentation to avoid redundancy
**Version**: 001
**Created**: 2026-01-10
**Language**: general

## Overview

Consolidate Claude Code documentation by merging the unique "Agent Commands" section from `.claude/docs/guides/user-installation.md` into `Docs/installation/CLAUDE_CODE.md`, then deleting the redundant file and updating all cross-references.

## Phases

### Phase 1: Enhance CLAUDE_CODE.md

**Estimated effort**: 30 minutes
**Status**: [COMPLETED]

**Objectives**:
1. Add Homebrew installation note for macOS
2. Add "Setting Up Claude Agent Commands" section

**Files to modify**:
- `Docs/installation/CLAUDE_CODE.md` - Add new content

**Steps**:
1. Add Homebrew installation instructions under macOS section (like user-installation.md has)
2. Add new section "Setting Up Claude Agent Commands (Optional)" after "Advanced Features" section
3. Include agent system description, installation instructions, command table
4. Add links to `.claude/` documentation (copy-claude-directory.md, commands/README.md)

**Verification**:
- CLAUDE_CODE.md contains agent commands section
- Links to .claude/ docs are correct (use relative paths from Docs/installation/)

---

### Phase 2: Delete user-installation.md

**Estimated effort**: 5 minutes
**Status**: [COMPLETED]

**Objectives**:
1. Remove the redundant file

**Files to modify**:
- `.claude/docs/guides/user-installation.md` - Delete

**Steps**:
1. Delete `.claude/docs/guides/user-installation.md`
2. Stage deletion in git

**Verification**:
- File no longer exists

---

### Phase 3: Update cross-references

**Estimated effort**: 20 minutes
**Status**: [COMPLETED]

**Objectives**:
1. Update all files that referenced user-installation.md
2. Point them to CLAUDE_CODE.md instead

**Files to modify**:
- `.claude/docs/guides/copy-claude-directory.md` - Update navigation links
- `.claude/docs/README.md` - Update guides list and references
- `.claude/context/project/modelchecker/installation.md` - Update table

**Steps**:
1. In copy-claude-directory.md: Change "User Installation" links to "Claude Code Guide" pointing to CLAUDE_CODE.md
2. In .claude/docs/README.md: Remove user-installation.md from guides list, update references
3. In installation.md context: Update table entry

**Verification**:
- Grep for "user-installation" returns no matches
- All links to CLAUDE_CODE.md are valid

---

## Dependencies

- None

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Broken links | Medium | Low | Grep for references before/after |
| Missing content | Medium | Low | Carefully merge unique content first |

## Success Criteria

- [ ] CLAUDE_CODE.md has agent commands section
- [ ] CLAUDE_CODE.md has Homebrew note for macOS
- [ ] user-installation.md is deleted
- [ ] No references to user-installation.md remain
- [ ] All links to CLAUDE_CODE.md work

## Rollback Plan

Revert changes via git if any phase fails.
