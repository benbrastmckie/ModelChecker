# Implementation: Practical Development Guidelines

[← Back to Docs](../README.md) | [DEVELOPMENT_WORKFLOW →](DEVELOPMENT_WORKFLOW.md) | [ERROR_HANDLING →](ERROR_HANDLING.md)

## Directory Structure

```
implementation/
├── DEVELOPMENT_WORKFLOW.md        # Feature development process
├── ERROR_HANDLING.md              # Error handling patterns
├── PERFORMANCE.md                 # Performance optimization
└── REFACTORING.md                 # Code improvement guidelines
```

## Overview

The implementation directory provides practical guidelines for day-to-day development activities. While the core standards define *what* is required, these documents explain *how* to implement features, handle errors, optimize performance, and refactor code effectively.

These guidelines translate the project's foundational standards into concrete development workflows and patterns. They cover the complete development lifecycle from planning through implementation, testing, and refinement.

Use these documents as your operational handbook for building features, handling errors gracefully, maintaining performance, and continuously improving code quality.

## Documents

### DEVELOPMENT_WORKFLOW.md
- **Purpose**: Define the complete feature development lifecycle
- **Use When**: Planning and implementing any new feature or bug fix
- **Key Sections**:
  - Research phase (investigating requirements)
  - Planning phase (creating implementation plan)
  - Implementation phase with TDD workflow
  - Code review and PR process
  - Breaking changes guidance

### ERROR_HANDLING.md
- **Purpose**: Establish error handling patterns and validation strategies
- **Use When**: Implementing input validation or error conditions
- **Key Sections**:
  - Fail-fast philosophy implementation
  - Early validation patterns
  - Clear error messaging
  - Exception handling best practices
  - Z3 error handling specifics

### PERFORMANCE.md
- **Purpose**: Guide performance optimization and efficiency
- **Use When**: Optimizing solver operations or iteration performance
- **Key Sections**:
  - Z3 solver optimization techniques
  - Model iteration performance
  - Caching strategies
  - Profiling and measurement
  - Performance vs maintainability tradeoffs

### REFACTORING.md
- **Purpose**: Provide safe code improvement procedures
- **Use When**: Improving existing code structure or clarity
- **Key Sections**:
  - When to refactor vs rewrite
  - Test-driven refactoring approach
  - Incremental change strategy
  - Breaking changes with no compatibility
  - Migration guides for breaking changes

## Learning Path

**Recommended reading order for implementation tasks**:

1. **Feature work**: [DEVELOPMENT_WORKFLOW.md](DEVELOPMENT_WORKFLOW.md) - Complete development process
2. **Error cases**: [ERROR_HANDLING.md](ERROR_HANDLING.md) - Validation and error reporting
3. **Optimization**: [PERFORMANCE.md](PERFORMANCE.md) - When performance matters
4. **Improvements**: [REFACTORING.md](REFACTORING.md) - Safe code improvement

## Quick Reference

### Common Tasks

- **Starting new feature?** → Follow DEVELOPMENT_WORKFLOW.md from research through implementation
- **Adding validation?** → See ERROR_HANDLING.md for fail-fast patterns
- **Code running slow?** → Check PERFORMANCE.md for optimization strategies
- **Improving existing code?** → Follow REFACTORING.md incremental approach
- **Handling Z3 errors?** → ERROR_HANDLING.md has solver-specific patterns

### Development Workflow Quick Start

1. **Research**: Understand requirements and constraints
2. **Plan**: Create implementation plan with phases
3. **Write Test**: RED - create failing test
4. **Implement**: GREEN - make test pass
5. **Refactor**: Clean up while keeping tests green
6. **Review**: Submit PR following review checklist
7. **Document**: Update relevant documentation

### Key Patterns

- **Fail-Fast Validation**: Check inputs immediately, clear error messages (ERROR_HANDLING.md)
- **TDD Cycle**: RED → GREEN → REFACTOR for all changes (DEVELOPMENT_WORKFLOW.md)
- **No Compatibility**: Clean breaks with migration guides (REFACTORING.md)
- **Incremental Refactoring**: Small changes with tests (REFACTORING.md)
- **Performance Last**: Correctness first, optimize after (PERFORMANCE.md)

## References

### Related Documentation Categories
- [Core Standards](../core/README.md) - Foundation standards that govern all development
- [Quality Assurance](../quality/README.md) - Testing and review processes
- [Component-Specific Standards](../specific/README.md) - Module-level requirements

### Testing Resources
- [Core Testing Standards](../core/TESTING.md) - TDD practices and requirements
- [Manual Testing Guide](../quality/MANUAL_TESTING.md) - Integration testing procedures

### Code Quality
- [Code Standards](../core/CODE_STANDARDS.md) - Style and convention requirements
- [Review Checklist](../quality/REVIEW_CHECKLIST.md) - PR review criteria

[← Back to Docs](../README.md) | [DEVELOPMENT_WORKFLOW →](DEVELOPMENT_WORKFLOW.md)
