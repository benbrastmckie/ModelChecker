# Style Guide Quick Reference

[← Back to Technical Docs](README.md) | [Implementation →](IMPLEMENTATION.md) | [Tests Guide →](TESTS.md) | [Maintenance Standards →](../../Docs/maintenance/README.md) | [Development →](DEVELOPMENT.md)

## Overview

This document provides a **quick reference** to the ModelChecker coding and documentation standards for implementing new features. It consolidates key standards from the comprehensive maintenance documentation and provides direct links to implementation guidelines.

For complete standards, see [Maintenance Documentation](../../Docs/maintenance/README.md). For AI development guidelines, see [CLAUDE.md](../CLAUDE.md). For testing procedures, see [TESTS.md](TESTS.md).

## Quick Reference

### Formula Formatting

See [Formula Formatting Standards](../../Docs/maintenance/FORMULA_FORMATTING.md)

**Essential Rules:**
- Use capital letters (`A`, `B`, `C`) for propositions  
- Binary operators require outer parentheses: `(A \\rightarrow B)`
- Unary operators have no outer parentheses: `\\neg A`
- **LaTeX notation only in code** (Unicode in comments/docs)
- Always use double backslashes: `\\Box`, `\\wedge`, `\\rightarrow`

### Examples.py Structure  

See [Examples Structure Standards](../../Docs/maintenance/EXAMPLES_STRUCTURE.md)

**Required Pattern:**
- Follow PREFIX_TYPE_NUMBER naming: `MODAL_TH_1_premises`
- Required variables: `unit_tests`, `example_range`, `semantic_theories`
- Include all core settings with descriptive comments
- Reference [EXAMPLES.md](EXAMPLES.md) for complete template

### Documentation Standards

See [Documentation Standards](../../Docs/maintenance/DOCUMENTATION_STANDARDS.md) | [README Standards](../../Docs/maintenance/README_STANDARDS.md)

**Core Requirements:**
- Every directory must have a README.md
- Follow **comprehensive documentation standards** for README files
- Include navigation links at top and bottom  
- **No emojis anywhere** in codebase or documentation
- Use content-specific section names (not generic labels)

### Development Documentation Practice

**docs/specs/ Directory Usage:**
- Use `docs/specs/` directory (tracked in git) for all development artifacts:
  - `plans/` - Numbered implementation plans (e.g., `001_output.md`)
  - `debug/` - Numbered debugging analyses (e.g., `001_capture_analysis.md`)
  - `findings/` - Numbered lessons learned reports (e.g., `001_output_lessons.md`)
- Documents are numbered sequentially starting from 001
- Use short, descriptive names without redundant prefixes
- **Update specs/README.md** when completing major features

**Workflow:**
1. Create implementation plan in `specs/plans/00X_feature.md`
2. Document debugging in `specs/debug/00X_issue.md` as needed
3. Write findings in `specs/findings/00X_lessons.md` after completion
4. Update `specs/README.md` with accomplishment summary
5. Incorporate key insights into:
   - Code comments for implementation details
   - Test documentation for edge cases discovered
   - Main documentation for architectural decisions

**Example Structure:**
```
docs/specs/                            # Development artifacts (tracked)
├── README.md                         # Major accomplishments log
├── plans/                           # Implementation plans
│   ├── 001_output.md               # Save output plan
│   ├── 002_structured_output.md    # Structured output plan
│   └── 003_interactive_save.md     # Interactive save plan
├── debug/                          # Debugging analyses
│   ├── 001_output_analysis.md      # Output system analysis
│   └── 002_capture_analysis.md     # Capture debugging
└── findings/                       # Lessons learned
    └── 001_output_lessons.md       # Output implementation findings
```

### Code Organization

See [Code Organization Standards](../../Docs/maintenance/CODE_ORGANIZATION.md)

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
from typing import Dict, List, Optional

# 2. Third-party
import z3

# 3. Local framework
from model_checker.defaults import SemanticDefaults
from model_checker.operators import Operator

# 4. Theory-specific imports  
from .proposition import TheoryProposition
```

### Testing Standards

See [Testing Standards](../../Docs/maintenance/TESTING_STANDARDS.md) | **[Complete Testing Guide](TESTS.md)**

**Core Requirements:**
- Use descriptive test names: `test_modus_ponens_valid` not `test_1`
- Include docstrings explaining what is tested
- Follow test organization structure detailed in **[TESTS.md](TESTS.md)**
- Test both valid arguments (no countermodel) and invalid arguments (countermodel found)

**For comprehensive testing procedures**, see the **[Testing Guide](TESTS.md)** which covers test categories, running tests, writing tests, and best practices.

### Character Encoding & Unicode

See [Unicode Guidelines](../../Docs/maintenance/UNICODE_GUIDELINES.md) | [CLAUDE.md Character Standards](../CLAUDE.md#character-encoding-standards)

**File Requirements:**
- **UTF-8 encoding** without BOM for all files
- **No control characters** (ASCII 0-31 except tab, newline)
- **LaTeX in code**: `\\Box`, `\\wedge`, `\\rightarrow`
- **Unicode in docs**: □, ∧, ∨, ¬ for readability

**Validation Commands:**
```bash
# Check file encoding
file -i filename  # Should show: charset=utf-8

# Find problematic characters
grep -n '[^[:print:][:space:]]' filename
```

### Output System Standards 

See specs/ directory for implementation details (not tracked in git)

**For New Features Involving Output:**
- Use **OutputManager** from `model_checker.output` for all printing/saving
- **Never hardcode ANSI codes** - use ColorManager for color output
- Support both **terminal display** and **clean file saving**
- Respect existing **print_*** settings: `print_impossible`, `print_constraints`, `print_z3`

**Quick Integration:**
```python
from model_checker.output import OutputManager

# In your class __init__
self.output_manager = OutputManager(settings)

# For colored terminal output
self.output_manager.print_manager.print_theory_result(...)

# For file saving (if save_output=True)
self.output_manager.save_output_if_enabled(context)
```

### Design Philosophy

See [CLAUDE.md Core Development Principles](../CLAUDE.md#core-development-principles)

#### Architectural Clarity Over Compatibility
- **Break compatibility when necessary** for cleaner architecture
- **Remove deprecated patterns** rather than maintaining legacy code
- **Unify interfaces** - similar components should use identical patterns

#### Fail Fast & Explicit Parameters

**Fail Fast** - Let errors occur naturally rather than masking with defaults:

```python
# Good - Explicit error when theory missing
def check_formula(formula, theory):
    return theory.validate(formula)

# Bad - Hidden fallback behavior
def check_formula(formula, theory=None):
    if theory is None:
        theory = get_default_theory()
```

**Explicit Parameters** - No hidden conversions or implicit state:

```python
# Good - Clear data flow
def evaluate_at_world(self, formula: str, world_id: int) -> bool:
    return self.evaluations[world_id][formula]

# Bad - Hidden conversion
def evaluate_at_world(self, formula, world):
    world_id = self._convert_world(world)
```

#### Test-Driven Development
- **Write tests first** that define desired behavior
- **Comprehensive testing** to drive design decisions  
- **No untested code** - every component must have tests

### Error Handling Standards

See [Error Handling Standards](../../Docs/maintenance/ERROR_HANDLING.md)

**Core Principles:**
- **User-friendly messages** - explain what went wrong and how to fix it
- **Specific error types** - use appropriate exception classes
- **Context information** - include relevant details for debugging
- **Graceful degradation** - handle edge cases appropriately

```python
# Good - Specific, actionable error
if not os.path.exists(filepath):
    raise FileNotFoundError(
        f"Theory file '{filepath}' not found. "
        f"Check that the file exists and has correct permissions."
    )

# Bad - Generic, unhelpful error  
if not os.path.exists(filepath):
    raise Exception("File error")
```

### Performance Guidelines

See [Performance Standards](../../Docs/maintenance/PERFORMANCE.md)

**Z3 Optimization:**
- **Reset Z3 context** between examples to prevent state leakage
- **Use appropriate timeouts** based on expected complexity
- **Memory management** - clean up Z3 objects explicitly
- **Parallel execution** where appropriate for comparison tasks

## Essential Documentation

### For Feature Implementation
- **[Implementation Guide](IMPLEMENTATION.md)** - Complete feature development process with TDD protocols
- **[Maintenance Documentation](../../Docs/maintenance/README.md)** - Complete standards reference
- **[CLAUDE.md](../CLAUDE.md)** - AI development guidelines and core principles  
- **[DEVELOPMENT.md](DEVELOPMENT.md)** - Development workflow and environment setup
- **[TESTS.md](TESTS.md)** - Testing procedures and best practices

### For Specific Areas
- **[EXAMPLES.md](EXAMPLES.md)** - Examples.py file standards and templates
- **[ARCHITECTURE.md](ARCHITECTURE.md)** - System design and component relationships
- **[specs/](specs/README.md)** - Development artifacts, implementation plans, debugging analyses

### Quick Commands Reference

```bash
# Development
./run_tests.py                    # Run all tests  
./run_tests.py logos --unit       # Test specific theory (unit tests only)
./dev_cli.py examples/test.py     # Run example file

# Quality Assurance  
file -i filename                  # Check UTF-8 encoding
grep -n '[^[:print:][:space:]]' filename  # Find bad characters
find . -name "test_*.py" | grep -v "src/"  # Find temp files to clean

# Documentation
grep -r "^#" docs/ src/*/README.md  # Check section headers
```

---

[← Back to Technical Docs](README.md) | [Implementation →](IMPLEMENTATION.md) | [Tests Guide →](TESTS.md) | [Maintenance Standards →](../../Docs/maintenance/README.md) | [Development →](DEVELOPMENT.md)
