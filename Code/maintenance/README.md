# ModelChecker Maintenance Standards

[← Back to Code](../README.md) | [Formula Formatting →](FORMULA_FORMATTING.md)

## Overview

This directory contains comprehensive maintenance standards for the ModelChecker codebase. These standards ensure consistency, quality, and maintainability across all code, documentation, and development practices.

## Directory Structure

```
maintenance/
├── README.md                    # This file - navigation hub and overview
├── FORMULA_FORMATTING.md        # Formula formatting standards
├── EXAMPLES_STRUCTURE.md        # Examples.py file structure standards
├── DOCUMENTATION_STANDARDS.md   # General documentation guidelines
├── README_STANDARDS.md          # README.md specific standards
├── CODE_ORGANIZATION.md         # Code structure and organization
├── TESTING_STANDARDS.md         # Testing guidelines and requirements
├── ERROR_HANDLING.md            # Error handling best practices
├── PERFORMANCE.md               # Performance optimization guidelines
├── VERSION_CONTROL.md           # Git and version control standards
├── UNICODE_GUIDELINES.md        # Character encoding standards
└── templates/                   # Documentation templates
    ├── README_TEMPLATE.md       # Standard README template
    ├── THEORY_README.md         # Theory-specific README template
    └── SUBTHEORY_README.md      # Subtheory README template
```

## Quick Reference

### Code Standards

- **[Formula Formatting](FORMULA_FORMATTING.md)** - LaTeX notation, parentheses rules, capital letters
- **[Examples Structure](EXAMPLES_STRUCTURE.md)** - PREFIX_TYPE_NUMBER naming, required variables
- **[Code Organization](CODE_ORGANIZATION.md)** - File naming, imports, docstrings
- **[Unicode Guidelines](UNICODE_GUIDELINES.md)** - LaTeX in code, Unicode only in comments

### Documentation Standards

- **[Documentation Standards](DOCUMENTATION_STANDARDS.md)** - General principles, no emojis, cross-references
- **[README Standards](README_STANDARDS.md)** - 9-section structure, directory trees, navigation
- **[Templates](templates/)** - Ready-to-use documentation templates

### Development Standards

- **[Testing Standards](TESTING_STANDARDS.md)** - Test organization, coverage requirements
- **[Error Handling](ERROR_HANDLING.md)** - User-friendly messages, exception types
- **[Performance Guidelines](PERFORMANCE.md)** - Z3 optimization, memory management
- **[Version Control](VERSION_CONTROL.md)** - Commit messages, branching, PR guidelines

## Core Principles

### No Emojis

Never use emojis anywhere in the codebase, documentation, or output.

### LaTeX in Code

Always use LaTeX notation in code (`\\wedge`, `\\Box`). Unicode symbols (∧, □) are only for comments and documentation.

### Specific Over Generic

Use content-specific section names. Avoid generic labels like "Basic Usage" or "Advanced Topics".

### Complete Documentation

Every directory must have a README.md with a complete file tree and clear purpose.

## Common Tasks

### Adding a New Theory

1. Follow [Code Organization](CODE_ORGANIZATION.md) for module structure
2. Use [Theory README Template](templates/THEORY_README.md) for documentation
3. Structure examples.py per [Examples Structure](EXAMPLES_STRUCTURE.md)
4. Apply [Formula Formatting](FORMULA_FORMATTING.md) in all examples

### Writing Documentation

1. Start with [Documentation Standards](DOCUMENTATION_STANDARDS.md)
2. For READMEs, follow [README Standards](README_STANDARDS.md)
3. Use appropriate [template](templates/) as starting point
4. Verify no Unicode in code examples per [Unicode Guidelines](UNICODE_GUIDELINES.md)

### Code Review Checklist

- [ ] Formulas use correct formatting (capital letters, parentheses)
- [ ] Examples follow PREFIX_TYPE_NUMBER naming
- [ ] Documentation has no emojis
- [ ] READMEs have complete directory trees
- [ ] Tests follow naming conventions
- [ ] Error messages are helpful
- [ ] Commit messages are descriptive

## Maintenance Checklist

When modifying the codebase:

### Documentation

- [ ] Every directory has README.md with file tree
- [ ] Navigation links at top and bottom
- [ ] No emojis used anywhere
- [ ] LaTeX notation in code examples
- [ ] Settings have inline comments

### Code Quality

- [ ] Operator definitions use LaTeX notation
- [ ] Imports organized correctly
- [ ] Functions have type hints
- [ ] Docstrings follow standards
- [ ] Tests cover new functionality

### Repository Health

- [ ] No temporary files committed
- [ ] .gitignore is comprehensive
- [ ] Dependencies documented
- [ ] Version control standards followed

## Contributing to Standards

To propose changes to these standards:

1. Create a branch: `docs/update-[standard-name]`
2. Make changes with clear justification
3. Update all affected documentation
4. Submit PR with examples of impact

## See Also

- **[Main Package Documentation](../README.md)** - ModelChecker overview
- **[Development Guide](../docs/DEVELOPMENT.md)** - Development workflow
- **[Theory Library](../src/model_checker/theory_lib/README.md)** - Theory implementations

---

[← Back to Code](../README.md) | [Formula Formatting →](FORMULA_FORMATTING.md)
