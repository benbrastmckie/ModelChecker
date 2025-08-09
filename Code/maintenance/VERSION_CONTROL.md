# Version Control Standards for Code

[← Back to Maintenance](README.md) | [Testing Standards →](TESTING_STANDARDS.md) | [Unicode Guidelines →](UNICODE_GUIDELINES.md)

## Overview

This document defines version control standards for **code changes** in the ModelChecker repository, including commit messages, branch naming, code review processes, and workflow guidelines specific to implementation tasks.

For documentation-specific version control standards, see [Docs/maintenance/VERSION_CONTROL.md](../../Docs/maintenance/VERSION_CONTROL.md).

## Code Commit Standards

### Commit Message Format

Use present tense and be descriptive about code changes:

```
Add modal operator support to logos theory

- Implement Box and Diamond operators
- Add tests for modal axioms K, T, 4, 5
- Update theory configuration for modal logic
```

### Code-Specific Commit Examples

```bash
# GOOD - Clear about code changes
git commit -m "Fix Z3 timeout in counterfactual evaluation"
git commit -m "Refactor syntactic.py into modular components"
git commit -m "Add iteration support for exclusion theory"
git commit -m "Optimize constraint extraction performance by 10x"

# BAD - Too vague for code changes
git commit -m "Fix bug"
git commit -m "Update code"
git commit -m "Changes"
```

### Breaking Changes

When making breaking changes (following NO BACKWARDS COMPATIBILITY principle):

```bash
git commit -m "BREAKING: Remove deprecated model.py classes

- Delete ModelVariable, ModelFunction, ModelConstraints
- Update all imports to use new models/ package
- No compatibility layer - update all call sites"
```

## Branch Naming for Code Features

### Feature Implementation
```bash
feature/modal-operators
feature/output-system-enhancement
feature/performance-optimization
```

### Bug Fixes
```bash
fix/z3-boolean-evaluation
fix/import-cycle-models
fix/iterator-constraint-preservation
```

### Refactoring
```bash
refactor/syntactic-modularization
refactor/model-package-structure
refactor/theory-agnostic-builder
```

## Code Development Workflow

### 1. Feature Implementation from Spec

```bash
# Create branch from spec name
git checkout -b feature/spec-name main

# Example from actual spec
git checkout -b feature/maintenance-refactor
```

### 2. Test-Driven Development Commits

```bash
# Commit tests first
git add tests/
git commit -m "Add tests for new output system features"

# Then implementation
git add src/
git commit -m "Implement OutputManager with color support"
```

### 3. Phase-Based Commits

Following implementation phases:

```bash
git commit -m "Phase 1 Complete: Core infrastructure

- Implement base classes and interfaces
- Add comprehensive unit tests (98% coverage)
- All tests passing

Next: Phase 2 - Integration"
```

### 4. Keep Branch Current

```bash
# Regularly rebase with main
git fetch origin
git rebase origin/main

# Resolve conflicts maintaining new behavior
# Never add compatibility layers during rebase
```

## Code Review Standards

### As a Code Reviewer

- **Architecture**: Check for clean design and unified interfaces
- **Breaking Changes**: Ensure all call sites are updated
- **Tests**: Verify comprehensive test coverage
- **Performance**: Check for regressions with benchmarks
- **Standards**: Ensure compliance with Code/maintenance/ standards

### As a Code Author

- **Test Results**: Include test output in PR description
- **Performance Impact**: Document any performance changes
- **Breaking Changes**: List all updated call sites
- **Refactoring Rationale**: Explain architectural improvements

### PR Template for Code Changes

```markdown
## Summary
Brief description of code changes

## Implementation Details
- Architecture decisions made
- Breaking changes introduced
- Performance considerations

## Testing
- Test coverage: XX%
- Performance benchmark results
- Regression testing completed

## Breaking Changes
- List all removed/changed APIs
- Show before/after for call sites
- No compatibility layers added

## Checklist
- [ ] All tests passing
- [ ] No performance regressions
- [ ] Code follows maintenance standards
- [ ] Documentation updated
```

## Git Best Practices for Code

### Atomic Commits

Each commit should be a complete, working change:

```bash
# BAD - Broken intermediate state
git commit -m "Start refactoring models"
git commit -m "Fix compilation errors"
git commit -m "Make tests pass"

# GOOD - Each commit works independently
git commit -m "Extract ModelVariable to models/variable.py"
git commit -m "Extract ModelFunction to models/function.py"
git commit -m "Update all imports to use new models package"
```

### Clean History Before Merge

```bash
# Interactive rebase to clean up
git rebase -i origin/main

# Squash related commits
pick abc1234 Add failing tests for feature
squash def5678 Implement feature
squash ghi9012 Fix edge case
# Results in: "Implement feature X with comprehensive tests"
```

### Code-Specific .gitignore

Ensure .gitignore includes:

```
# Python build artifacts
__pycache__/
*.py[cod]
*.so
build/
dist/
*.egg-info/

# Test artifacts
.coverage
htmlcov/
.pytest_cache/
.tox/

# Development artifacts
*.log
debug_*.py
test_*.py  # Temporary test files
output/
temp/

# IDE
.vscode/
.idea/
*.swp
```

## Handling Code Conflicts

### During Rebase

```bash
# When conflicts occur
git rebase origin/main

# Fix conflicts maintaining new behavior
# Never add optional parameters for compatibility
# Update all affected code to new interface

git add .
git rebase --continue
```

### Merge Strategy

- **Always rebase** feature branches before merge
- **No merge commits** in feature branches
- **Squash and merge** for clean main history

## Release Process for Code

### Version Tags

```bash
# Tag after major refactoring
git tag -a v2.0.0 -m "Major refactor: Model package restructure

Breaking changes:
- All model imports must be updated
- No backwards compatibility

See migration guide in docs/"
```

### Code Migration Documentation

When making breaking changes, document migration:

```markdown
# Migration Guide: v1.x to v2.0

## Model Imports
Before:
```python
from model_checker.model import ModelVariable
```

After:
```python
from model_checker.models.variable import ModelVariable
```

## Updated Interfaces
All call sites must be updated - no optional parameters
or compatibility layers are provided.
```

---

[← Back to Maintenance](README.md) | [Testing Standards →](TESTING_STANDARDS.md) | [Unicode Guidelines →](UNICODE_GUIDELINES.md)