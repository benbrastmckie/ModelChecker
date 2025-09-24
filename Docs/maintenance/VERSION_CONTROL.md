# Version Control Standards for Documentation

[← Back to Maintenance](README.md) | [Unicode Guidelines →](UNICODE_GUIDELINES.md) | [Documentation Standards →](quality/DOCUMENTATION_STANDARDS.md)

## Overview

This document defines version control standards for **documentation changes** in the ModelChecker repository, including commit messages, branch naming, and workflow guidelines specific to documentation tasks.

For code-specific version control standards, see [Code/maintenance/VERSION_CONTROL.md](../../Code/maintenance/VERSION_CONTROL.md).

## Documentation Commit Standards

### Commit Message Format

Use clear, descriptive messages for documentation changes:

```
Add modal logic tutorial for interdisciplinary audience

- Create step-by-step guide for non-programmers
- Include visual diagrams of Kripke models
- Add glossary of technical terms
- Link to relevant theory implementations
```

### Documentation-Specific Commit Examples

```bash
# GOOD - Clear about documentation changes
git commit -m "Add installation guide for Windows users"
git commit -m "Update theory explanations with Unicode symbols"
git commit -m "Reorganize tutorials by difficulty level"
git commit -m "Fix broken links in methodology section"

# BAD - Too vague for documentation
git commit -m "Update docs"
git commit -m "Fix typos"
git commit -m "Changes"
```

### Documentation Categories

Include the type of documentation in commits:

```bash
git commit -m "Tutorial: Add counterfactual logic walkthrough"
git commit -m "Methodology: Document semantic framework approach"
git commit -m "README: Update navigation structure"
git commit -m "Templates: Add educational content template"
```

## Branch Naming for Documentation

### Documentation Updates
```bash
docs/modal-logic-tutorial
docs/installation-guide-update
docs/methodology-expansion
```

### Documentation Reorganization
```bash
docs/tutorial-restructure
docs/maintenance-refactor
docs/cross-reference-update
```

### New Documentation Series
```bash
docs/theory-explanation-series
docs/video-tutorial-scripts
docs/academic-paper-supplements
```

## Documentation Development Workflow

### 1. Planning Documentation

```bash
# Create branch for documentation work
git checkout -b docs/topic-name main

# Example
git checkout -b docs/counterfactual-tutorial
```

### 2. Incremental Documentation

```bash
# Commit logical sections
git add tutorials/counterfactuals/introduction.md
git commit -m "Tutorial: Add counterfactual introduction

- Explain philosophical background
- Define key terms for interdisciplinary audience
- Include historical context"

git add tutorials/counterfactuals/examples.md
git commit -m "Tutorial: Add interactive examples

- Show basic counterfactual formulas
- Demonstrate ModelChecker syntax
- Include expected outputs"
```

### 3. Cross-Reference Management

```bash
# When updating links
git commit -m "Docs: Update cross-references for new structure

- Fix links after maintenance/ reorganization
- Update relative paths in all affected files
- Verify all internal links work"
```

## Documentation Review Standards

### As a Documentation Reviewer

- **Clarity**: Check for clear explanations
- **Audience**: Ensure appropriate level for target readers
- **Completeness**: Verify all sections are covered
- **Links**: Test all cross-references work
- **Examples**: Confirm code examples are accurate

### As a Documentation Author

- **Preview**: Check rendered Markdown appearance
- **Navigation**: Ensure easy navigation flow
- **Consistency**: Follow documentation standards
- **Accessibility**: Consider diverse backgrounds

### PR Template for Documentation

```markdown
## Summary
Brief description of documentation changes

## Documentation Details
- Type: Tutorial/Guide/Reference/Methodology
- Target Audience: [Specify reader background]
- Scope: What topics are covered

## Changes Made
- New sections added
- Updated examples
- Fixed issues
- Improved clarity

## Checklist
- [ ] Links tested and working
- [ ] Follows documentation standards
- [ ] Examples verified
- [ ] Appropriate for target audience
- [ ] Navigation structure clear
```

## Git Best Practices for Documentation

### Logical Commits

Group related documentation changes:

```bash
# BAD - Too granular
git commit -m "Fix typo in line 1"
git commit -m "Fix typo in line 5"
git commit -m "Fix typo in line 10"

# GOOD - Grouped improvements
git commit -m "Tutorial: Fix typos and improve clarity

- Correct mathematical notation
- Clarify ambiguous explanations
- Improve example descriptions"
```

### Documentation-First Workflow

```bash
# Document before implementing
git checkout -b docs/new-feature-guide

# Write user documentation first
git add docs/guides/new-feature.md
git commit -m "Docs: Add guide for upcoming feature"

# This helps clarify feature design
```

## Handling Documentation Conflicts

### During Merge

```bash
# When documentation conflicts occur
git merge origin/main

# Resolve by:
# 1. Preserving both improvements
# 2. Maintaining consistent style
# 3. Updating cross-references

git add resolved-file.md
git commit -m "Merge: Combine documentation improvements"
```

### Large Documentation Projects

For substantial documentation work:

```bash
# Feature branch for major docs
git checkout -b docs/comprehensive-tutorial-series

# Work incrementally
git commit -m "Tutorial Series: Add part 1 - basics"
git commit -m "Tutorial Series: Add part 2 - intermediate"
git commit -m "Tutorial Series: Add part 3 - advanced"

# Squash if needed before merge
git rebase -i origin/main
```

## Documentation Release Notes

### Version Documentation

```bash
# Tag documentation milestones
git tag -a docs-v1.0 -m "Documentation Release 1.0

- Complete tutorial series
- Full API reference
- Methodology documentation
- Installation guides for all platforms"
```

### Changelog for Documentation

Maintain a documentation changelog:

```markdown
# Documentation Changelog

## [1.1.0] - 2024-12-20
### Added
- Counterfactual logic tutorial series
- Video tutorial scripts
- Glossary of terms

### Changed
- Reorganized tutorials by difficulty
- Updated all code examples to v2.0

### Fixed
- Broken links in methodology section
- Incorrect Unicode symbols in theory guides
```

## Documentation-Specific .gitignore

Consider these documentation artifacts:

```
# Documentation build artifacts
docs/_build/
docs/.doctrees/
*.pdf

# Editor temporary files
*.swp
*~
.#*

# OS files
.DS_Store
Thumbs.db

# Documentation tools
.vale/
.markdownlint.json
```

## Quality Assurance

### Pre-Commit Checks

```bash
# Check for broken links
markdownlint docs/

# Verify spelling
vale docs/

# Test all code examples
python test_doc_examples.py
```

### Documentation Standards Compliance

```bash
# Verify structure follows standards
grep -r "^#" docs/*.md  # Check heading hierarchy

# Ensure no emojis
grep -r ":[a-z_]+:" docs/  # Should return nothing

# Check Unicode usage (should be in docs, not code examples)
grep -r "[∧∨¬□◇]" docs/
```

---

[← Back to Maintenance](README.md) | [Unicode Guidelines →](UNICODE_GUIDELINES.md) | [Documentation Standards →](quality/DOCUMENTATION_STANDARDS.md)