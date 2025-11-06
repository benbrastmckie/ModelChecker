# Templates: Code Templates for New Components

[← Back to Docs](../README.md) | [THEORY_TEMPLATE →](THEORY_TEMPLATE.py) | [EXAMPLES_TEMPLATE →](EXAMPLES_TEMPLATE.py)

## Directory Structure

```
templates/
├── THEORY_TEMPLATE.py             # Template for semantic.py
├── EXAMPLES_TEMPLATE.py           # Template for examples.py
└── TEST_TEMPLATE.py               # Template for unit tests
```

## Overview

The templates directory provides code templates for creating new ModelChecker components. These templates follow project standards and include comprehensive comments explaining required structure, common patterns, and best practices.

Use these templates as starting points when creating new semantic theories, example files, or test suites. The templates are designed to be copied, renamed, and customized for specific use cases while maintaining consistency with project conventions.

All templates are Python files (.py) that can be directly used or adapted. They include placeholder code that demonstrates proper structure and organization.

## Documents

### THEORY_TEMPLATE.py
- **Purpose**: Template for creating new semantic theory implementations (semantic.py)
- **Use When**: Starting a new semantic theory
- **Key Sections**:
  - Module docstring structure
  - Required imports and type annotations
  - Semantic class definition pattern
  - Model generation methods
  - Verification methods
  - Standard method signatures

### EXAMPLES_TEMPLATE.py
- **Purpose**: Template for theory example files (examples.py)
- **Use When**: Creating examples and test cases for a theory
- **Key Sections**:
  - Example formula definitions
  - Expected results documentation
  - Test case organization
  - Integration with model checker
  - Comment conventions for examples

### TEST_TEMPLATE.py
- **Purpose**: Template for unit test files
- **Use When**: Creating new test suites
- **Key Sections**:
  - pytest structure and fixtures
  - Test function naming conventions
  - Assertion patterns
  - Test organization (unit vs integration)
  - Coverage best practices

## Learning Path

**Creating new components**:

1. **New theory**: Copy [THEORY_TEMPLATE.py](THEORY_TEMPLATE.py) → Customize for your semantics
2. **Theory examples**: Copy [EXAMPLES_TEMPLATE.py](EXAMPLES_TEMPLATE.py) → Add your test cases
3. **Unit tests**: Copy [TEST_TEMPLATE.py](TEST_TEMPLATE.py) → Implement tests following TDD

## Quick Reference

### Common Tasks

- **Creating new theory?** → Copy THEORY_TEMPLATE.py to semantic.py, customize semantics
- **Adding examples?** → Copy EXAMPLES_TEMPLATE.py to examples.py, add your formulas
- **Writing tests?** → Copy TEST_TEMPLATE.py, follow pytest patterns
- **Need theory structure?** → See THEORY_TEMPLATE.py for required methods
- **Example format?** → See EXAMPLES_TEMPLATE.py for documentation patterns

### Using Templates

**Step 1: Copy template**
```bash
# For new theory
cp Code/docs/templates/THEORY_TEMPLATE.py Code/src/model_checker/theory_lib/my_theory/semantic.py

# For examples
cp Code/docs/templates/EXAMPLES_TEMPLATE.py Code/src/model_checker/theory_lib/my_theory/examples.py

# For tests
cp Code/docs/templates/TEST_TEMPLATE.py Code/src/model_checker/theory_lib/my_theory/tests/test_semantic.py
```

**Step 2: Customize**
- Replace placeholder names with your theory name
- Implement required methods
- Add theory-specific logic
- Update docstrings with your documentation

**Step 3: Follow TDD**
- Write tests first (RED)
- Implement to pass tests (GREEN)
- Refactor while keeping tests green (REFACTOR)

### Template Conventions

All templates follow these conventions:
- Comprehensive module docstrings
- Type annotations for all functions
- Clear comments explaining required vs optional sections
- Placeholder names in ALL_CAPS (replace with actual names)
- Standard imports organized per CODE_STANDARDS.md

## References

### Related Documentation Categories
- [Project Creation Guide](../guides/PROJECT_CREATION.md) - How to create complete theory projects
- [Package Structure](../specific/PACKAGES.md) - Required package organization
- [Code Standards](../core/CODE_STANDARDS.md) - Coding conventions to follow

### Standards to Follow
- [Code Standards](../core/CODE_STANDARDS.md) - Python conventions and style
- [Testing Standards](../core/TESTING_GUIDE.md) - TDD workflow and test requirements
- [Documentation Standards](../core/DOCUMENTATION.md) - How to document code

### Implementation Resources
- [Development Workflow](../implementation/DEVELOPMENT_WORKFLOW.md) - Feature development process
- [Theory-Specific Testing](../core/TESTING_GUIDE.md#theory-testing) - How to test theories
- [Error Handling](../implementation/ERROR_HANDLING.md) - Validation patterns

### Example Theories
- Logos: `Code/src/model_checker/theory_lib/logos/`
- Exclusion: `Code/src/model_checker/theory_lib/exclusion/`
- Imposition: `Code/src/model_checker/theory_lib/imposition/`
- Bimodal: `Code/src/model_checker/theory_lib/bimodal/`

[← Back to Docs](../README.md) | [THEORY_TEMPLATE →](THEORY_TEMPLATE.py)
