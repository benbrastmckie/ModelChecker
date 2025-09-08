# Code Maintenance: Standards and Best Practices

[← Back to Code](../README.md) | [Implementation Guide →](IMPLEMENT.md) | [Code Standards →](CODE_STANDARDS.md)

## Directory Structure

```
maintenance/
├── README.md                       # This file - code maintenance hub
├── IMPLEMENT.md                    # Spec execution guide (concise workflow)
├── CODE_STANDARDS.md               # Unified code quality standards
├── REFACTORING_METHODOLOGY.md      # Systematic improvement approach
├── METHOD_COMPLEXITY.md            # Context-aware complexity guidelines
├── ARCHITECTURAL_PATTERNS.md       # Protocol-based design patterns
├── UTILITY_ORGANIZATION.md         # Shared vs package-specific utilities
├── FORMULA_FORMATTING.md           # LaTeX notation in code
├── EXAMPLES_STRUCTURE.md           # examples.py file standards
├── CODE_ORGANIZATION.md            # Module structure and imports
├── ERROR_HANDLING.md               # Exception handling patterns (enhanced)
├── PERFORMANCE.md                  # Z3 optimization guidelines
├── TEST_STATUS.md                  # Current test status and summary
├── TESTING_STANDARDS.md            # Test requirements with isolation (enhanced)
├── TEST_ORGANIZATION.md            # Test suite organization standards
├── MANUAL_TESTING.md               # Manual testing protocol (REQUIRED)
├── UNICODE_GUIDELINES.md           # Character encoding for code
├── VERSION_CONTROL.md              # Git workflow for code changes
├── PYPI_LINK_REQUIREMENTS.md       # PyPI README link formatting standards
└── templates/
    ├── THEORY_TEMPLATE.py          # Theory implementation template
    ├── EXAMPLES_TEMPLATE.py        # Examples file template
    └── TEST_TEMPLATE.py            # Test file template
```

## Overview

This directory contains **comprehensive code maintenance standards** for the ModelChecker framework, ensuring consistency, quality, and maintainability across all code implementation, testing, and development practices. These standards guide developers in writing high-quality, maintainable code that follows established patterns and best practices.

The code maintenance standards cover **16 key areas**: systematic refactoring methodology, context-aware complexity guidelines, architectural patterns, utility organization, spec execution workflows, unified code standards, formula formatting, example structure, code organization, enhanced error handling, performance optimization, comprehensive testing with isolation, manual testing requirements, character encoding, version control, and template resources. Together, these standards ensure technical excellence and consistency across the entire codebase.

Following these standards is **essential for all code contributors**, whether implementing new features, fixing bugs, adding theories, or optimizing performance. The standards reflect our commitment to clean architecture, test-driven development, and systematic refactoring practices outlined in [CLAUDE.md](../CLAUDE.md).

## Code Implementation Examples

### Spec Execution Example

Following [IMPLEMENT.md](IMPLEMENT.md) for executing approved specs:

```bash
# Start implementation of approved spec
implement docs/specs/plans/021_maintenance_refactor.md

# 1. Create feature branch
git checkout -b feature/maintenance-refactor

# 2. Execute phases with TDD
./run_tests.py --new-feature-tests
# Implement minimal solution
./run_tests.py --all

# 3. Validate with dual testing
./dev_cli.py src/model_checker/theory_lib/logos/examples.py
```

### Formula Formatting Example

Proper formula formatting ensures clarity and Z3 compatibility:

```python
# CORRECT - Following standards
MODAL_TH_1_premises = ["\\Box (A \\rightarrow B)", "\\Box A"]
MODAL_TH_1_conclusions = ["\\Box B"]
MODAL_TH_1_settings = {
    'N': 3,                    # Number of atomic states
    'contingent': False,       # Modal-specific setting
    'expectation': False       # False = expect theorem
}

# INCORRECT - Common mistakes
bad_premises = ["□(a→b)", "□a"]     # Wrong: Unicode in code, lowercase
bad_settings = {'N': 3}             # Wrong: No comments
```

### Code Organization Example

```python
# Correct import organization
# Standard library imports
import os
from typing import Dict, List, Optional

# Third-party imports
import z3

# Local imports
from model_checker.defaults import SemanticDefaults
from model_checker.operators import Operator

# Theory-specific imports
from .proposition import LogosProposition
```

For complete standards, see individual standard documents.

## Subdirectories

### [templates/](templates/)
Code templates providing starting points for new theory implementations, example files, and test suites. See template files for proper structure and patterns.

## Documentation

### For Feature Implementers
- **[Spec Execution Guide](IMPLEMENT.md)** - Concise workflow for implementing specs
- **[Code Standards](CODE_STANDARDS.md)** - Unified code quality requirements
- **[Refactoring Methodology](REFACTORING_METHODOLOGY.md)** - Systematic improvement approach
- **[Testing Standards](TESTING_STANDARDS.md)** - TDD protocols with test isolation

### For Code Quality & Architecture
- **[Method Complexity](METHOD_COMPLEXITY.md)** - Context-aware complexity guidelines
- **[Architectural Patterns](ARCHITECTURAL_PATTERNS.md)** - Protocol-based design patterns
- **[Utility Organization](UTILITY_ORGANIZATION.md)** - Shared vs package-specific utilities
- **[Error Handling](ERROR_HANDLING.md)** - Enhanced exception patterns and hierarchies

### For Theory Developers
- **[Formula Formatting](FORMULA_FORMATTING.md)** - LaTeX notation requirements
- **[Examples Structure](EXAMPLES_STRUCTURE.md)** - Example file standards
- **[Code Organization](CODE_ORGANIZATION.md)** - Module structure patterns

### For Performance & Quality
- **[Performance Guidelines](PERFORMANCE.md)** - Z3 optimization techniques
- **[Unicode Guidelines](UNICODE_GUIDELINES.md)** - Character encoding for code

### Testing & Quality
- **[Test Status](TEST_STATUS.md)** - Current test status and summary
- **[Testing Standards](TESTING_STANDARDS.md)** - Comprehensive testing guidelines
- **[Test Organization](TEST_ORGANIZATION.md)** - Test structure and categorization  
- **[Manual Testing](MANUAL_TESTING.md)** - Manual testing procedures

### For Development Workflow
- **[Version Control](VERSION_CONTROL.md)** - Git workflow and commit standards
- **[Implementation Process](../docs/IMPLEMENTATION.md)** - Comprehensive planning guide

## Key Features

### Core Principles
- **No Backwards Compatibility** - Break compatibility for cleaner architecture
- **Test-Driven Development** - Write tests before implementation
- **Systematic Refactoring** - Continuous improvement without legacy debt
- **Clean Architecture** - Unified interfaces and clear separation of concerns

### Quality Standards
- **LaTeX in Code** - Always use LaTeX notation (`\\wedge`, `\\Box`) in code
- **Capital Letters** - Use A, B, C for atomic propositions
- **Proper Parentheses** - Binary operators need outer parentheses
- **UTF-8 Encoding** - All files must use UTF-8 without BOM

### Development Practices
- **Dual Testing** - Use both test runner and CLI validation
- **Phase Implementation** - Execute specs phase by phase
- **Documentation Updates** - Keep docs synchronized with code
- **Performance Validation** - No regressions allowed

## References

### Related Documentation
- **[Technical Documentation Hub](../docs/README.md)** - Development guides
- **[Documentation Maintenance](../../Docs/maintenance/README.md)** - Documentation standards
- **[API Documentation](../src/model_checker/README.md)** - Framework APIs
- **[Theory Library](../src/model_checker/theory_lib/README.md)** - Theory implementations

### Development Resources
- **[Development Guide](../docs/DEVELOPMENT.md)** - Environment setup
- **[Architecture Guide](../docs/ARCHITECTURE.md)** - System design
- **[Tools Guide](../docs/TOOLS.md)** - Debugging utilities
- **[Style Guide](../docs/STYLE_GUIDE.md)** - Quick reference

---

[← Back to Code](../README.md) | [Implementation Guide →](IMPLEMENT.md) | [Testing Standards →](TESTING_STANDARDS.md)
