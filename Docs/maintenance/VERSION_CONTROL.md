# Version Control Standards

[← Performance](PERFORMANCE.md) | [Back to Maintenance](README.md) | [Templates →](templates/)

## Overview

This document defines version control standards for the ModelChecker repository, including commit messages, branch naming, and workflow guidelines.

## Commit Message Standards

### Format

Use present tense and be descriptive but concise:

```
Add modal operator support to logos theory

- Implement Box and Diamond operators
- Add tests for modal axioms K, T, 4, 5
- Update documentation with modal examples
```

### Good Commit Messages

```bash
# GOOD - Clear and specific
git commit -m "Fix Z3 timeout in counterfactual evaluation"
git commit -m "Add iteration support for exclusion theory"
git commit -m "Update formula formatting standards in MAINTENANCE.md"

# BAD - Too vague
git commit -m "Fix bug"
git commit -m "Update docs"
git commit -m "Changes"
```

### Reference Issues

When fixing issues, reference them in the commit:

```bash
git commit -m "Fix #123: Resolve import error in logos subtheories"
git commit -m "Address #456: Improve error messages for invalid formulas"
```

## Branch Naming Conventions

### Feature Branches
```bash
feature/modal-operators
feature/jupyter-integration
feature/performance-optimization
```

### Bug Fix Branches
```bash
fix/formula-parsing-error
fix/z3-timeout-handling
fix/import-cycle
```

### Documentation Branches
```bash
docs/api-reference-update
docs/theory-examples
docs/maintenance-refactor
```

### Experimental Branches
```bash
experimental/new-solver-backend
experimental/parallel-checking
```

## Workflow Guidelines

### Feature Development

1. Create feature branch from main:
   ```bash
   git checkout -b feature/new-feature main
   ```

2. Make incremental commits:
   ```bash
   git add -p  # Stage changes selectively
   git commit -m "Implement base functionality for new feature"
   ```

3. Keep branch up to date:
   ```bash
   git fetch origin
   git rebase origin/main
   ```

4. Push to remote:
   ```bash
   git push -u origin feature/new-feature
   ```

### Pull Request Guidelines

#### PR Title
Clear and descriptive, matching the branch purpose:
- "Add modal operator support to logos theory"
- "Fix formula parsing for nested implications"

#### PR Description Template
```markdown
## Summary
Brief description of changes

## Changes Made
- Specific change 1
- Specific change 2

## Testing
- How the changes were tested
- Any new tests added

## Related Issues
Fixes #123
```

### Code Review Standards

#### As a Reviewer
- Check for adherence to coding standards
- Verify tests pass and coverage is maintained
- Ensure documentation is updated
- Test the changes locally when possible

#### As an Author
- Respond to all feedback
- Make requested changes in new commits
- Squash commits before merging if requested
- Update PR description with changes made

## Branching Strategy

### Main Branch
- Always deployable
- Protected with required reviews
- All tests must pass

### Development Workflow
1. Create feature branch
2. Develop and test
3. Create pull request
4. Code review
5. Merge to main

### Release Process
1. Tag release on main:
   ```bash
   git tag -a v1.2.3 -m "Release version 1.2.3"
   git push origin v1.2.3
   ```

2. Create release notes documenting:
   - New features
   - Bug fixes
   - Breaking changes
   - Migration instructions

## Git Best Practices

### Keep History Clean

```bash
# Before pushing, clean up commit history
git rebase -i HEAD~3  # Interactive rebase last 3 commits

# Squash related commits
pick abc1234 Add basic structure
squash def5678 Fix typo
squash ghi9012 Add tests
```

### Write Good Commit Messages

```bash
# Use git commit without -m for longer messages
git commit

# Opens editor for detailed message:
# Add comprehensive theory comparison framework
#
# - Implement cross-theory validity checking
# - Add comparison visualization tools
# - Support for theory translation mappings
# - Include extensive test coverage
#
# This allows researchers to compare how different
# theories handle the same logical principles.
```

### Use .gitignore

Ensure .gitignore includes:
```
# Python
__pycache__/
*.py[cod]
*$py.class
*.so
.Python
env/
venv/

# IDE
.vscode/
.idea/
*.swp
*.swo

# Testing
.coverage
htmlcov/
.pytest_cache/

# OS
.DS_Store
Thumbs.db

# Project specific
*.log
output/
temp/
```

### Handle Sensitive Information

Never commit:
- API keys or tokens
- Passwords or credentials  
- Personal information
- Large binary files

If accidentally committed:
```bash
# Remove from history (requires force push)
git filter-branch --force --index-filter \
  "git rm --cached --ignore-unmatch path/to/sensitive/file" \
  --prune-empty --tag-name-filter cat -- --all
```

## Collaboration Guidelines

### Communicate Changes
- Announce breaking changes in PRs
- Document migration steps
- Update relevant documentation

### Maintain Consistency
- Follow established patterns
- Don't introduce new conventions without discussion
- Keep style consistent within files

### Be Respectful
- Provide constructive feedback
- Explain reasoning for changes
- Credit contributors appropriately

---

[← Performance](PERFORMANCE.md) | [Back to Maintenance](README.md) | [Templates →](templates/)