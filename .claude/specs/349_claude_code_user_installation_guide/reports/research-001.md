# Research Report: Task #349

**Task**: Expand .claude/docs/ with Claude Code installation guide for new users
**Date**: 2026-01-10
**Focus**: Documentation structure, content requirements, and context file organization

## Summary

The ModelChecker project has comprehensive user-facing installation documentation in `Docs/installation/` including a detailed Claude Code guide (`CLAUDE_CODE.md`). The `.claude/` agent system has its own documentation in `.claude/docs/` focused on internal development. This task requires creating a bridge guide in `.claude/docs/guides/` that helps new users install Claude Code and use it to install ModelChecker, while also creating an installation context file for agent reference.

## Findings

### Existing Documentation Structure

**User-facing installation docs (`Docs/installation/`):**
- `README.md` - Installation hub with overview of all guides
- `CLAUDE_CODE.md` - Comprehensive 700+ line Claude Code installation and usage guide
- `BASIC_INSTALLATION.md` - Standard pip installation guide
- `GETTING_STARTED.md` - First steps after installation (terminal basics, editor setup)
- `GIT_GOING.md` - GitHub and Git setup for beginners
- `TROUBLESHOOTING.md` - Platform-specific troubleshooting
- `VIRTUAL_ENVIRONMENTS.md` - Virtual environment setup
- `CLAUDE_TEMPLATE.md` - Template for user project CLAUDE.md files

**Agent system docs (`.claude/docs/`):**
- `README.md` - Documentation hub for the agent system
- `guides/` - How-to guides (context-management.md, creating-commands.md, creating-skills.md)
- `commands/` - Command reference
- `skills/` - Skill documentation
- `workflows/` - Workflow documentation
- `reference/` - Quick reference guides
- `templates/` - Command and skill templates

### Existing Context Files

**In `.claude/context/project/modelchecker/`:**
- `architecture.md` - System architecture overview (166 lines)
- `theories.md` - Semantic theory library documentation (241 lines)
- `z3-patterns.md` - Z3 solver patterns (365 lines)

**Missing**: No installation context file exists. There's no context to help Claude Code assist users with installation when cloned or forked.

### Reference Document Analysis

The example document from Connectives demonstrates a user-focused approach:
1. Clear installation instructions by platform (macOS, Windows, Linux)
2. Authentication setup
3. Practical usage patterns with specific examples
4. Advanced capabilities section
5. Best practices for effectiveness
6. Troubleshooting coverage

The existing `Docs/installation/CLAUDE_CODE.md` already covers these well. The `.claude/docs/guides/user-installation.md` should:
1. Be tailored for users who have cloned/forked ModelChecker
2. Focus on using Claude Code with the existing documentation
3. Point to the detailed installation docs rather than duplicating them
4. Include GitHub CLI setup for issue reporting

### Gap Analysis

**What's needed in `.claude/docs/guides/user-installation.md`:**
1. Quick Claude Code installation steps (reference existing docs for details)
2. How to use Claude Code with ModelChecker installation docs
3. GitHub CLI (`gh`) setup and authentication
4. Opening issues on ModelChecker repo
5. Using Claude Code to create Logos projects
6. Linking to existing documentation for details

**What's needed in `.claude/context/project/modelchecker/installation.md`:**
1. Installation paths and URLs for Claude Code to reference
2. Key installation commands summary
3. Project creation workflow
4. Troubleshooting pointers
5. References to detailed documentation
6. Should be loadable by agents without burdening context unnecessarily

### Documentation Cross-References

The new guide should reference:
- `Docs/installation/CLAUDE_CODE.md` - Full Claude Code installation details
- `Docs/installation/BASIC_INSTALLATION.md` - pip installation
- `Docs/installation/GETTING_STARTED.md` - Terminal basics
- `Docs/installation/GIT_GOING.md` - GitHub setup
- `Docs/installation/TROUBLESHOOTING.md` - Platform issues

## Recommendations

### 1. Create `.claude/docs/guides/user-installation.md`

A focused guide (~200-300 lines) covering:
- Quick-start Claude Code installation (platform agnostic)
- Authentication setup
- Using Claude Code to install ModelChecker via the existing docs
- GitHub CLI installation and authentication
- Creating issues on ModelChecker repo via `gh`
- Creating and modifying Logos projects with Claude Code assistance
- Links to detailed documentation for each topic

### 2. Create `.claude/context/project/modelchecker/installation.md`

A context file (~150-200 lines) for agent reference containing:
- Key installation URLs and commands
- Documentation paths that agents can reference
- Project creation workflow summary
- Common troubleshooting patterns
- Issue reporting instructions

### 3. Update `.claude/docs/README.md`

Add entry for the new user-installation guide in the guides section.

### 4. Update Context Index

If there's a context index file, add the new installation.md entry.

## References

- `Docs/installation/README.md` - Installation documentation hub
- `Docs/installation/CLAUDE_CODE.md` - Existing Claude Code guide (reference)
- `Docs/installation/GETTING_STARTED.md` - Terminal and editor basics
- `Docs/installation/GIT_GOING.md` - GitHub setup guide
- `.claude/docs/README.md` - Agent documentation hub
- `.claude/docs/guides/context-management.md` - Context loading patterns
- `.claude/context/project/modelchecker/` - Existing context files
- https://github.com/benbrastmckie/Connectives/blob/master/docs/CLAUDE_CODE.md - Reference example

## Next Steps

1. Create `.claude/docs/guides/user-installation.md` with user-focused content
2. Create `.claude/context/project/modelchecker/installation.md` for agent reference
3. Update `.claude/docs/README.md` to include new guide
4. Consider adding installation.md reference to CLAUDE.md context loading sections where relevant
5. Test the workflow by simulating a new user experience
