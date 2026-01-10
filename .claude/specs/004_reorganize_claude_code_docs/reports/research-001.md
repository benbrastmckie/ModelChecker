# Research Report: Task #4

**Task**: Reorganize Claude Code documentation to avoid redundancy
**Date**: 2026-01-10
**Focus**: Compare user-installation.md vs CLAUDE_CODE.md to eliminate redundancy

## Summary

There is significant overlap between `Docs/installation/CLAUDE_CODE.md` (708 lines) and `.claude/docs/guides/user-installation.md` (435 lines). CLAUDE_CODE.md is the more comprehensive, authoritative source with better cross-linking to other Docs. The user-installation.md file contains one unique section (Setting Up Claude Agent Commands) that should be merged into CLAUDE_CODE.md before removing user-installation.md.

## Findings

### Content Comparison

| Topic | CLAUDE_CODE.md | user-installation.md |
|-------|----------------|---------------------|
| Installation (macOS/Windows/Linux) | Comprehensive (multiple options per OS) | Simplified (one method per OS) |
| Authentication | Covered | Covered (duplicate) |
| Automated ModelChecker install | Covered | Covered (duplicate) |
| Creating projects | Covered with examples | Covered (simplified) |
| GitHub CLI integration | **Extensive** (PRs, branches, forking) | Basic (issue creation only) |
| Agent commands setup | Not covered | **Unique section** |
| Troubleshooting | Covered | Covered (subset) |
| CLAUDE.md customization | Covered | Not covered |

### Unique Content in user-installation.md

The only unique content is the **"Setting Up Claude Agent Commands"** section (lines 136-188):
- Explains the `.claude/` agent system
- Links to copy-claude-directory.md for installation
- Lists available commands (/task, /research, /plan, /implement, /todo)
- Links to commands reference

### References to Update

**Files referencing user-installation.md:**
1. `.claude/docs/guides/copy-claude-directory.md` (lines 3, 286, 301)
2. `.claude/docs/README.md` (lines 25, 339)
3. `.claude/context/project/modelchecker/installation.md` (line 86)

**Files referencing CLAUDE_CODE.md:**
- Many files in `Docs/installation/` - these are correct and need no change
- `.claude/docs/guides/user-installation.md` (lines 62, 418) - will be deleted
- `.claude/docs/README.md` (line 341) - needs update
- `.claude/context/project/modelchecker/installation.md` (lines 72, 210) - needs update

### Cross-Link Structure

CLAUDE_CODE.md is well-integrated into the `Docs/installation/` structure:
- Referenced from README.md, GIT_GOING.md, GETTING_STARTED.md
- Has proper navigation links to other Docs files

user-installation.md sits in `.claude/docs/guides/` and creates parallel documentation that fragments the user experience.

## Recommendations

1. **Add agent commands section to CLAUDE_CODE.md**
   - Add new section "Setting Up Claude Agent Commands (Optional)" after "Advanced Features"
   - Include the unique content from user-installation.md
   - Link to `.claude/docs/guides/copy-claude-directory.md` for installation
   - Link to `.claude/docs/commands/README.md` for command reference

2. **Delete user-installation.md**
   - Remove `.claude/docs/guides/user-installation.md`
   - Update all references to point to CLAUDE_CODE.md instead

3. **Update cross-references**
   - `.claude/docs/guides/copy-claude-directory.md`: Change links to CLAUDE_CODE.md
   - `.claude/docs/README.md`: Update references
   - `.claude/context/project/modelchecker/installation.md`: Update table

4. **Improve CLAUDE_CODE.md link to Homebrew**
   - Add Homebrew installation instructions like user-installation.md has

## References

- `Docs/installation/CLAUDE_CODE.md` - 708 lines, comprehensive
- `.claude/docs/guides/user-installation.md` - 435 lines, mostly redundant
- `.claude/docs/guides/copy-claude-directory.md` - references user-installation.md

## Next Steps

1. Add "Setting Up Claude Agent Commands" section to CLAUDE_CODE.md
2. Add Homebrew installation note for macOS
3. Delete user-installation.md
4. Update all cross-references (3 files)
5. Verify all links work
