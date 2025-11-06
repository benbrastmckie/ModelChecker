# Specific: Component-Specific Standards

[← Back to Docs](../README.md) | [FORMULAS →](FORMULAS.md) | [ITERATOR →](ITERATOR.md) | [PACKAGES →](PACKAGES.md)

## Directory Structure

```
specific/
├── FORMULAS.md                    # Formula parsing standards
├── ITERATOR.md                    # Model iteration patterns
├── PACKAGES.md                    # Package organization
└── UTILITIES.md                   # Utility module guidelines
```

## Overview

The specific directory contains component-level standards and patterns for ModelChecker's key subsystems. While core standards apply broadly across the project, these documents provide detailed requirements and best practices for individual components like formula parsing, model iteration, package structure, and utility modules.

Each document focuses on a specific subsystem and covers its unique requirements, patterns, and gotchas. These standards ensure consistency within each component while allowing appropriate variation between different architectural concerns.

Consult these documents when working on or extending the particular subsystems they cover. They complement the general core standards with component-specific details.

## Documents

### FORMULAS.md
- **Purpose**: Define formula parsing and syntactic processing standards
- **Use When**: Working with formula input, parsing, or abstract syntax trees
- **Key Sections**:
  - Formula syntax specification
  - Parser implementation patterns
  - AST node structure
  - Operator precedence and associativity
  - Error reporting for invalid formulas

### ITERATOR.md
- **Purpose**: Establish model iteration engine patterns and contracts
- **Use When**: Implementing or modifying model generation and iteration logic
- **Key Sections**:
  - Iterator architecture and control flow
  - Verification vs counterexample modes
  - N-model iteration strategies
  - Performance optimization for iteration
  - Theory-specific iteration customization

### PACKAGES.md
- **Purpose**: Define package structure and organization requirements
- **Use When**: Creating new theories or reorganizing package structure
- **Key Sections**:
  - Package hierarchy and naming
  - Required module files (semantic.py, operators.py, examples.py)
  - Theory library organization
  - .modelchecker package marker requirements
  - Import patterns within packages

### UTILITIES.md
- **Purpose**: Guide utility module organization and common helpers
- **Use When**: Creating shared utilities or helper functions
- **Key Sections**:
  - Utility module organization
  - Common helper patterns
  - Shared validation functions
  - Formatting and output utilities
  - Testing utilities

## Learning Path

**Component-specific learning order**:

1. **Formula work**: [FORMULAS.md](FORMULAS.md) - Syntax and parsing patterns
2. **Iteration logic**: [ITERATOR.md](ITERATOR.md) - Model generation engine
3. **Package structure**: [PACKAGES.md](PACKAGES.md) - Theory organization
4. **Helper functions**: [UTILITIES.md](UTILITIES.md) - Shared utilities

## Quick Reference

### Common Tasks

- **Extending formula syntax?** → FORMULAS.md defines grammar and parser patterns
- **Modifying iteration?** → ITERATOR.md covers iteration engine architecture
- **Creating new theory?** → PACKAGES.md specifies required structure
- **Adding utility function?** → UTILITIES.md guides utility organization
- **Need AST manipulation?** → FORMULAS.md explains node structure

### Component Entry Points

- **Formula Parsing**: `model_checker.syntactic` - See FORMULAS.md for patterns
- **Model Iteration**: `model_checker.iterate` - See ITERATOR.md for architecture
- **Theory Libraries**: `model_checker.theory_lib/*` - See PACKAGES.md for structure
- **Utilities**: `model_checker.utils` - See UTILITIES.md for organization

### Key Patterns Per Component

**Formulas** (FORMULAS.md):
- Operator precedence table drives parsing
- AST nodes follow visitor pattern
- Error messages include formula position

**Iterator** (ITERATOR.md):
- Verification mode: find counterexample or confirm validity
- Counterexample mode: enumerate satisfying models
- N-model iteration: depth-first with backtracking

**Packages** (PACKAGES.md):
- Required: semantic.py (theory definition)
- Required: operators.py (operator declarations)
- Required: examples.py (test cases)
- Optional: iterate.py (custom iteration logic)

**Utilities** (UTILITIES.md):
- Group related helpers in dedicated modules
- Prefer specific over generic implementations
- Document expected input/output types

## References

### Related Documentation Categories
- [Core Standards](../core/README.md) - General standards that apply to all components
- [Implementation Guidelines](../implementation/README.md) - Development workflow and patterns
- [API Documentation](../api/README.md) - Public API specifications

### Architecture Context
- [System Architecture](../core/ARCHITECTURE.md) - Overall system design
- [Package Organization](../core/ARCHITECTURE.md#package-structure) - How components fit together

### Testing Requirements
- [Testing Standards](../core/TESTING.md) - General testing practices
- [Manual Testing](../quality/MANUAL_TESTING.md) - Component integration testing

[← Back to Docs](../README.md) | [FORMULAS →](FORMULAS.md)
