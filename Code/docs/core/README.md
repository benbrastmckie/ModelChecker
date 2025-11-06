# Core: Foundation Standards

[← Back to Docs](../README.md) | [CODE_STANDARDS →](CODE_STANDARDS.md) | [TESTING →](TESTING.md) | [ARCHITECTURE →](ARCHITECTURE.md)

## Directory Structure

```
core/
├── CODE_STANDARDS.md              # Python coding conventions
├── TESTING.md                     # Test-driven development practices
├── ARCHITECTURE.md                # System design patterns
└── DOCUMENTATION.md               # Documentation requirements
```

## Overview

The core directory contains foundational standards that define the ModelChecker project's development philosophy, practices, and patterns. These documents establish the baseline requirements for code quality, testing methodology, system architecture, and documentation structure.

All developers must familiarize themselves with these standards before contributing to the project. The core standards enforce consistency across the codebase and ensure maintainability through test-driven development, clear architectural patterns, and comprehensive documentation.

The standards in this directory are mandatory and apply to all project code without exception. They represent the project's commitment to code quality, fail-fast error handling, and zero backwards compatibility in favor of clean design.

## Documents

### CODE_STANDARDS.md
- **Purpose**: Define Python coding conventions and style requirements
- **Use When**: Writing any Python code in the ModelChecker project
- **Key Sections**:
  - Import organization and relative imports
  - Type coverage requirements (>90%)
  - Error handling patterns (fail-fast philosophy)
  - No backwards compatibility policy

### TESTING.md
- **Purpose**: Establish test-driven development practices and requirements
- **Use When**: Writing tests (which is before writing any implementation code)
- **Key Sections**:
  - RED-GREEN-REFACTOR workflow
  - Test coverage targets (>85% overall, >90% critical paths)
  - Unit vs integration test organization
  - Theory-specific testing patterns

### ARCHITECTURE.md
- **Purpose**: Document system design patterns and architectural decisions
- **Use When**: Understanding package organization or designing new features
- **Key Sections**:
  - Package structure and responsibilities
  - Model iteration engine design
  - Theory library organization
  - Clean breaks over compatibility

### DOCUMENTATION.md
- **Purpose**: Specify documentation structure and requirements
- **Use When**: Creating or updating documentation files
- **Key Sections**:
  - ALL CAPS naming convention
  - README.md template structure
  - Three-tier documentation hierarchy
  - File tree comment alignment (column 37-40)

## Learning Path

**Recommended reading order for new contributors**:

1. **Start here**: [CODE_STANDARDS.md](CODE_STANDARDS.md) - Understand coding conventions first
2. **Then**: [TESTING.md](TESTING.md) - Learn TDD workflow before writing code
3. **Next**: [ARCHITECTURE.md](ARCHITECTURE.md) - Grasp system design patterns
4. **Finally**: [DOCUMENTATION.md](DOCUMENTATION.md) - Learn how to document your work

## Quick Reference

### Common Tasks

- **Starting a new feature?** → Read CODE_STANDARDS.md for style, then TESTING.md for TDD workflow
- **Writing tests?** → See TESTING.md sections on test organization and coverage
- **Understanding package structure?** → Check ARCHITECTURE.md for design patterns
- **Creating documentation?** → Follow DOCUMENTATION.md template structure
- **Need import guidance?** → CODE_STANDARDS.md has detailed import organization rules

### Key Principles

- **Fail-Fast**: Validate inputs early, report errors immediately (CODE_STANDARDS.md)
- **TDD Always**: Write tests BEFORE implementation (TESTING.md)
- **No Compatibility**: Clean breaks when improving code (CODE_STANDARDS.md)
- **Type Coverage**: >90% of codebase must have type annotations (CODE_STANDARDS.md)
- **ALL CAPS**: Documentation files use ALL CAPS naming (DOCUMENTATION.md)

## References

### Related Documentation Categories
- [Implementation Guidelines](../implementation/README.md) - Detailed workflow and error handling patterns
- [Quality Assurance](../quality/README.md) - Quality metrics and review processes
- [Component-Specific Standards](../specific/README.md) - Module-specific requirements

### External Resources
- Project README: [../../README.md](../../README.md)
- CLAUDE.md: [../../CLAUDE.md](../../CLAUDE.md) - Project configuration for AI-assisted development

[← Back to Docs](../README.md) | [CODE_STANDARDS →](CODE_STANDARDS.md)
