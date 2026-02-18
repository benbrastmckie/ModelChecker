# Research Report: Task #9

**Task**: Refactor CLAUDE_CODE.md documentation
**Date**: 2026-01-11
**Focus**: Document structure, cross-linking, and progressive disclosure

## Summary

The current CLAUDE_CODE.md is comprehensive (765 lines) but mixes too many concerns into a single document. The task requires restructuring to follow a clear progression: (1) install model-checker, (2) test an example, (3) copy .claude/ directory, (4) learn the agent system, (5) use gh CLI for issues/PRs. The existing document has good content but overwhelms users with examples and lacks progressive disclosure.

## Findings

### Current Document Analysis

**CLAUDE_CODE.md (765 lines)** contains:
- Claude Code installation (macOS, Windows, Linux) - lines 35-109
- Authentication - lines 121-141
- Automated ModelChecker installation - lines 143-193
- Creating projects - lines 195-240
- GitHub integration - lines 242-465 (very long section)
- Example workflows - lines 346-436 (too many examples)
- Tips and troubleshooting - lines 467-586
- Advanced features (CLAUDE.md setup) - lines 589-658
- Agent commands setup - lines 660-708 (at the end, should be earlier)

**Issues identified:**
1. Agent commands section is buried at the end (lines 660-708)
2. Too many GitHub examples in one section
3. CLAUDE.md template setup mixes with agent commands
4. No clear progression for new users
5. The copy-claude-directory.md instructions are not prominent

### Supporting Documents

**GETTING_STARTED.md** - Well-structured beginner guide with:
- Terminal usage tutorial
- Editor setup recommendations
- Project creation walkthrough
- Running examples
- Already links to CLAUDE_CODE.md appropriately

**GIT_GOING.md** - Comprehensive GitHub setup:
- Git installation
- SSH key setup
- Basic Git concepts
- Contributing workflow
- Already referenced from CLAUDE_CODE.md

**copy-claude-directory.md** - Clear installation instructions for .claude/ system:
- Prerequisites
- macOS/Linux/Windows methods
- Verification steps
- Uses GitHub URL method as described in task

**.claude/docs/README.md** - Agent system documentation hub:
- Complete command reference
- Workflow documentation
- Should be linked prominently after .claude/ copy

### Proposed Structure

```markdown
# Using Claude Code with ModelChecker

## 1. Getting Started
   - What is Claude Code?
   - Prerequisites (link to GETTING_STARTED.md for terminal basics)

## 2. Install Claude Code
   - Platform-specific installation (condensed)
   - Verify and authenticate

## 3. Install ModelChecker
   - Use Claude Code to install model-checker
   - Test with example project
   - One clear example workflow

## 4. Set Up the Agent System (NEW EMPHASIS)
   - Copy .claude/ directory using GitHub path
   - Restart and verify
   - Link to .claude/docs/README.md for full documentation

## 5. Using gh CLI for GitHub
   - Ask Claude to install gh
   - Authentication
   - Create issues when problems occur
   - Submit pull requests (one focused example)
   - Link to GIT_GOING.md for Git/GitHub basics

## 6. Next Steps
   - Links to relevant guides
```

### Key Changes Required

1. **Move agent commands section earlier** - After install/test, before GitHub details
2. **Consolidate GitHub examples** - Keep 2-3 focused examples, remove duplicates
3. **Make .claude/ copy prominent** - Use the GitHub URL method as the primary approach
4. **Add clear progression** - Number sections to show intended flow
5. **Remove CLAUDE.md template section** - This belongs in project setup, not installation
6. **Add issue creation workflow** - This is task #7's content, should be brief here

### Content to Keep

- Claude Code installation for all platforms (condense slightly)
- Authentication section
- "What Claude Code Will Do" list for ModelChecker install
- One or two GitHub workflow examples
- Troubleshooting section

### Content to Remove or Relocate

- Excessive GitHub examples (lines 300-360, 410-465) - too many
- CLAUDE.md template section (lines 599-645) - belongs in GETTING_STARTED.md
- "Understanding Theory Implementation" example - too advanced for installation guide
- Multiple similar pull request examples

### Cross-Links Needed

| Topic | Link To |
|-------|---------|
| Terminal basics | GETTING_STARTED.md#before-you-begin-using-the-terminal |
| Git/GitHub concepts | GIT_GOING.md |
| Agent system full docs | .claude/docs/README.md |
| Copy instructions | .claude/docs/guides/copy-claude-directory.md |
| ModelChecker installation | BASIC_INSTALLATION.md |

## Recommendations

1. **Restructure with numbered sections** showing clear progression
2. **Reduce document length** from 765 to ~400-500 lines
3. **Make .claude/ setup prominent** - directly after testing an example
4. **Use the GitHub URL pattern** for copying .claude/ as described in task:
   ```
   Please read https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/.claude/docs/guides/copy-claude-directory.md and follow the instructions to copy the .claude/ directory.
   ```
5. **Consolidate GitHub section** - focus on: install gh, create issue, create PR
6. **Link liberally** to specialized guides rather than duplicating content

## References

- `/home/benjamin/Projects/ModelChecker/Docs/installation/CLAUDE_CODE.md` - Current document (765 lines)
- `/home/benjamin/Projects/ModelChecker/Docs/installation/GETTING_STARTED.md` - Terminal and editor setup
- `/home/benjamin/Projects/ModelChecker/Docs/installation/GIT_GOING.md` - Git/GitHub guide
- `/home/benjamin/Projects/ModelChecker/.claude/docs/guides/copy-claude-directory.md` - Agent system copy instructions
- `/home/benjamin/Projects/ModelChecker/.claude/docs/README.md` - Agent system documentation hub

## Next Steps

1. Create implementation plan with phased approach
2. Phase 1: Restructure with numbered sections and new flow
3. Phase 2: Consolidate GitHub content, add issue creation workflow
4. Phase 3: Update cross-links and verify all paths work
4. Verify document length reduced to target range
