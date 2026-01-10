# Research Report: Task #1

**Task**: Create .claude/ directory copy instructions for Claude Code users
**Date**: 2026-01-10
**Focus**: General research

## Summary

This task requires creating documentation that guides users on how to copy the `.claude/` directory from the ModelChecker repository into their own Claude Code project directories. The documentation must provide clear, executable steps and integrate with the existing user-installation.md guide.

## Findings

### Current State of user-installation.md

The existing guide at `.claude/docs/guides/user-installation.md` covers:
- Claude Code installation (macOS, Windows, Linux)
- Authentication with Anthropic
- ModelChecker installation via pip
- Creating Logos projects
- GitHub CLI setup
- Issue reporting workflows

The guide currently lacks instructions for setting up the `.claude/` agent system, which provides the task management commands (`/task`, `/research`, `/plan`, `/implement`, etc.).

### Repository Information

- **Repository URL**: `https://github.com/benbrastmckie/ModelChecker`
- **Target directory**: `.claude/` at repository root
- **Key subdirectories**:
  - `commands/` - Slash command definitions (9 commands)
  - `skills/` - Specialized agent skills (8 skills)
  - `rules/` - Automatic behavior rules
  - `context/` - Domain knowledge and standards
  - `specs/` - Task artifacts and state files
  - `docs/` - Agent system documentation

### Methods for Copying .claude/ Directory

#### Option 1: Git Sparse Checkout (Recommended for tech-savvy users)

```bash
# Clone with sparse checkout for minimal download
git clone --filter=blob:none --sparse https://github.com/benbrastmckie/ModelChecker.git temp-modelchecker
cd temp-modelchecker
git sparse-checkout set .claude
cp -r .claude ../your-project/
cd .. && rm -rf temp-modelchecker
```

This method:
- Downloads only necessary files
- Requires git knowledge
- Works best for users comfortable with terminal

#### Option 2: Full Clone and Copy (Simplest)

```bash
git clone https://github.com/benbrastmckie/ModelChecker.git
cp -r ModelChecker/.claude your-project/
rm -rf ModelChecker
```

This method:
- Simple and straightforward
- Downloads full repository (larger download)
- Best for beginners

#### Option 3: GitHub Download ZIP

1. Navigate to https://github.com/benbrastmckie/ModelChecker
2. Click "Code" → "Download ZIP"
3. Extract and copy `.claude/` directory

This method:
- No git required
- GUI-based
- Works for users unfamiliar with terminal

### Documentation Structure Requirements

Per the task description, the documentation must include:

1. **copy-claude-directory.md** (new file)
   - Full GitHub URL
   - Step-by-step copying instructions
   - Multiple methods for different user skill levels
   - Verification steps

2. **user-installation.md** (update)
   - New section pointing to copy-claude-directory.md
   - Uses full URLs (not relative paths) for Claude Code
   - Links to commands/README.md for testing

### URL Requirements

URLs in user-installation.md must be full URLs when intended for pasting into Claude Code. The raw GitHub URL format for the new guide would be:
```
https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/.claude/docs/guides/copy-claude-directory.md
```

### Verification Steps

After copying, users should:
1. Restart Claude Code
2. Test commands work: `/task`, `/research`, `/plan`
3. Check state files exist: `.claude/specs/TODO.md`, `.claude/specs/state.json`

## Recommendations

1. **Use Option 2 (Full Clone)** as the primary method - it's simplest and most reliable
2. **Include Option 1 (Sparse Checkout)** as an alternative for users wanting minimal download
3. **Omit Option 3 (ZIP)** - less reliable for maintaining directory structure
4. **Provide Claude Code prompt templates** so users can ask Claude to execute the setup
5. **Include platform-specific notes** for Windows users (different cp commands)

## References

- [Git Sparse Checkout Documentation](https://git-scm.com/docs/git-sparse-checkout)
- [GitHub Blog: Sparse Checkout](https://github.blog/open-source/git/bring-your-monorepo-down-to-size-with-sparse-checkout/)
- Current user-installation.md: `.claude/docs/guides/user-installation.md`
- Command reference: `.claude/docs/commands/README.md`

## Next Steps

1. Create `.claude/docs/guides/copy-claude-directory.md` with:
   - Introduction explaining the `.claude/` system
   - Prerequisites section
   - Platform-specific copy instructions (macOS/Linux and Windows)
   - Verification steps
   - Troubleshooting section

2. Update `.claude/docs/guides/user-installation.md` to add:
   - New section "Setting Up Claude Agent Commands"
   - Full URL to copy-claude-directory.md for use with Claude Code
   - Link to commands/README.md for testing commands
   - Brief explanation of what the agent system provides
