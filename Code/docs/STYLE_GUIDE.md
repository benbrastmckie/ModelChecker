# Style Guide Quick Reference

[← Back to Technical Docs](README.md) | [Maintenance Standards →](../MAINTENANCE.md) | [Development →](DEVELOPMENT.md)

## Overview

This document provides a quick reference to the ModelChecker coding and documentation standards. For comprehensive standards, see [maintenance/README.md](../../Docs/maintenance/README.md).

## Quick Reference

### Formula Formatting

See [MAINTENANCE.md § Formula Formatting Standards](../MAINTENANCE.md#formula-formatting-standards)

- Use capital letters (`A`, `B`, `C`) for propositions
- Binary operators require outer parentheses: `(A \\rightarrow B)`
- Unary operators have no outer parentheses: `\\neg A`
- LaTeX notation only in code (Unicode in comments)

### Examples.py Structure

See [MAINTENANCE.md § Examples.py Structure Standards](../MAINTENANCE.md#examplespy-structure-standards)

- Follow PREFIX_TYPE_NUMBER naming: `LOG_TH_1_example`
- Required variables: `unit_tests`, `example_range`, `semantic_theories`
- Include all core settings with descriptive comments
- Reference [EXAMPLES.md](EXAMPLES.md) for complete template

### Documentation Standards

See [MAINTENANCE.md § Documentation Standards](../MAINTENANCE.md#documentation-standards)

- Every directory must have a README.md
- Follow 9-section structure for README files
- Include navigation links at top and bottom
- No emojis anywhere

### Code Organization

See [MAINTENANCE.md § Code Organization Standards](../MAINTENANCE.md#code-organization-standards)

#### Naming Conventions

| Element       | Convention    | Example            |
| ------------- | ------------- | ------------------ |
| **Functions** | `snake_case`  | `check_formula()`  |
| **Classes**   | `PascalCase`  | `LogosSemantics`   |
| **Modules**   | `lowercase`   | `semantic.py`      |
| **Constants** | `UPPER_SNAKE` | `DEFAULT_SETTINGS` |

#### Import Order

```python
# 1. Standard library
import os
import sys

# 2. Third-party
import z3

# 3. Local framework
from model_checker import get_theory

# 4. Relative imports
from .semantic import TheorySemantics
```

### Testing Standards

See [MAINTENANCE.md § Testing Standards](../MAINTENANCE.md#testing-standards)

- Use descriptive test names
- Include docstrings explaining what is tested
- Follow test organization structure
- See [TESTS.md](TESTS.md) for testing guide

### Design Philosophy

#### Fail Fast

Let errors occur naturally rather than masking with defaults:

```python
# Good
def check_formula(formula, theory):
    return theory.validate(formula)

# Bad
def check_formula(formula, theory=None):
    if theory is None:
        theory = get_default_theory()
```

#### Explicit Parameters

No hidden conversions or implicit state:

```python
# Good
def evaluate_at_world(self, formula: str, world_id: int) -> bool:
    return self.evaluations[world_id][formula]

# Bad
def evaluate_at_world(self, formula, world):
    world_id = self._convert_world(world)
```

## Complete Standards

For comprehensive coding and documentation standards, refer to:

- **[MAINTENANCE.md](../MAINTENANCE.md)** - Complete standards document
- **[EXAMPLES.md](EXAMPLES.md)** - Examples.py file standards
- **[DEVELOPMENT.md](DEVELOPMENT.md)** - Development workflow
- **[ARCHITECTURE.md](ARCHITECTURE.md)** - System design

---

[← Back to Technical Docs](README.md) | [Maintenance Standards →](../MAINTENANCE.md) | [Development →](DEVELOPMENT.md)
