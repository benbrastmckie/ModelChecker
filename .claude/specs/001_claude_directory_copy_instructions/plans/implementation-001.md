# Implementation Plan: Task #1

**Task**: Create .claude/ directory copy instructions for Claude Code users
**Version**: 001
**Created**: 2026-01-10
**Language**: general

## Overview

Create documentation that enables Claude Code users to copy the `.claude/` agent system directory from the ModelChecker repository into their own projects. This involves creating a new guide file and updating the existing user-installation.md with appropriate links and instructions.

The implementation uses a Claude Code-friendly approach: users paste a URL into Claude Code, which then follows the instructions to clone and copy the directory automatically.

## Phases

### Phase 1: Create copy-claude-directory.md Guide

**Estimated effort**: 1 hour
**Status**: [COMPLETED]

**Objectives**:
1. Create comprehensive guide for copying .claude/ directory
2. Include platform-specific instructions (macOS/Linux and Windows)
3. Provide verification steps to confirm successful setup

**Files to modify**:
- `.claude/docs/guides/copy-claude-directory.md` - Create new file

**Steps**:
1. Create file with frontmatter/metadata section
2. Write introduction explaining what the .claude/ system provides:
   - Task management commands (/task, /research, /plan, /implement)
   - Specialized skills for different languages
   - Context files for domain knowledge
   - State tracking for projects
3. Add prerequisites section:
   - Git installed
   - Claude Code authenticated
   - Target project directory exists
4. Write macOS/Linux instructions:
   - Full clone method (primary)
   - Sparse checkout method (alternative for minimal download)
5. Write Windows instructions (PowerShell):
   - Equivalent commands using Windows paths
   - Note about xcopy vs cp
6. Add verification section:
   - Check .claude/ directory exists
   - Verify key files present (specs/TODO.md, specs/state.json)
   - Test a command (/task --help or similar)
7. Add troubleshooting section:
   - Permission issues
   - Git not installed
   - Directory already exists

**Verification**:
- File exists at `.claude/docs/guides/copy-claude-directory.md`
- Instructions are clear and executable
- Both platforms covered

---

### Phase 2: Update user-installation.md

**Estimated effort**: 30 minutes
**Status**: [COMPLETED]

**Objectives**:
1. Add new section for Claude Agent System setup
2. Use full GitHub URLs (not relative paths) for Claude Code compatibility
3. Link to commands documentation for testing

**Files to modify**:
- `.claude/docs/guides/user-installation.md` - Update existing file

**Steps**:
1. Identify insertion point (after "Installing ModelChecker with Claude Code" section, before "Creating Logos Projects")
2. Add new section "## Setting Up Claude Agent Commands"
3. Write brief explanation of what the agent system provides
4. Add instruction to paste URL into Claude Code:
   ```
   https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/.claude/docs/guides/copy-claude-directory.md
   ```
5. Include prompt template for users:
   ```
   Please follow the instructions at [URL] to copy the .claude/ directory into my project.
   ```
6. Add restart instruction: "Restart Claude Code after copying"
7. Add testing section with link to commands documentation:
   ```
   https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/.claude/docs/commands/README.md
   ```
8. Update table of contents if present

**Verification**:
- New section appears in correct location
- All URLs are full URLs (not relative paths)
- Links to commands/README.md included
- Instructions mention restarting Claude Code

---

### Phase 3: Verification and Testing

**Estimated effort**: 30 minutes
**Status**: [COMPLETED]

**Objectives**:
1. Verify all links work correctly
2. Test instructions manually (if possible)
3. Ensure documentation is consistent with existing style

**Files to modify**:
- None (verification only)

**Steps**:
1. Verify GitHub raw URLs are correctly formatted:
   - https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/.claude/docs/guides/copy-claude-directory.md
   - https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/.claude/docs/commands/README.md
2. Check internal links between documents work
3. Review for consistency with existing documentation style
4. Verify all code blocks have correct syntax highlighting
5. Check that Windows and macOS/Linux instructions are both complete

**Verification**:
- All URLs accessible (after merge to master)
- Documentation follows existing style conventions
- No broken internal links

---

## Dependencies

- None - this is a documentation-only task

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Raw GitHub URLs may not work until merged to master | Medium | High | Note in docs that URLs work after merge; test with current branch if possible |
| Windows instructions may have edge cases | Low | Medium | Provide PowerShell examples; note alternatives |
| Users may have .claude/ already | Low | Low | Add instructions for backing up existing directory |

## Success Criteria

- [ ] copy-claude-directory.md created with complete instructions
- [ ] user-installation.md updated with new section
- [ ] Full URLs used (not relative paths) for Claude Code compatibility
- [ ] Both macOS/Linux and Windows platforms covered
- [ ] Link to commands/README.md included for testing
- [ ] Restart Claude Code instruction included
- [ ] Documentation follows existing style conventions

## Rollback Plan

If implementation fails:
1. Delete `.claude/docs/guides/copy-claude-directory.md` if created
2. Revert changes to `.claude/docs/guides/user-installation.md`
3. Git restore from previous commit if needed
