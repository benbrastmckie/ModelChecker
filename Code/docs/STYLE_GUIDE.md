# Style Guide Quick Reference

[← Back to Technical Docs](README.md) | [Implementation →](IMPLEMENTATION.md) | [Tests Guide →](TESTS.md) | [Code Maintenance →](../maintenance/README.md) | [Development →](DEVELOPMENT.md)

## Overview

This document provides a **quick reference** to the ModelChecker coding and documentation standards for implementing new features. It consolidates key standards from the comprehensive maintenance documentation and provides direct links to implementation guidelines.

For code standards, see [Code Maintenance](../maintenance/README.md). For documentation standards, see [Documentation Maintenance](../../Docs/maintenance/README.md). For AI guidelines, see [CLAUDE.md](../CLAUDE.md). For testing procedures, see [TESTS.md](TESTS.md).

## Quick Reference

### Formula Formatting

See [Formula Formatting Standards](../maintenance/FORMULA_FORMATTING.md)

**Essential Rules:**
- Use capital letters (`A`, `B`, `C`) for propositions  
- Binary operators require outer parentheses: `(A \\rightarrow B)`
- Unary operators have no outer parentheses: `\\neg A`
- **LaTeX notation only in code** (Unicode in comments/docs)
- Always use double backslashes: `\\Box`, `\\wedge`, `\\rightarrow`

### Examples.py Structure  

See [Examples Structure Standards](../maintenance/EXAMPLES_STRUCTURE.md)

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
  - `plans/` - Implementation plans
  - `debug/` - Debugging analyses
  - `findings/` - Lessons learned reports
  - `implementation/` - Implementation summaries
  - `research/` - Research reports and comparative analyses
  - `baselines/` - Captured test outputs and regression baselines

**Chronological Numbering Convention:**
- Each directory maintains independent numbering starting from 001
- Numbers increase chronologically within each directory
- Higher numbers indicate more recent documents
- Examples:
  - `debug/001_output_analysis.md` - First debug analysis
  - `plans/016_builder_theory_agnostic_refactor.md` - Recent plan
  - `findings/015_iterator_fix_implemented.md` - Recent finding
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
├── debug/                           # Debugging analyses
│   ├── 001_output_analysis.md      # First debug analysis
│   └── 006_iterator_constraint_analysis.md  # Recent debug work
├── plans/                           # Implementation plans
│   ├── 001_output.md               # First plan
│   └── 016_builder_theory_agnostic_refactor.md  # Recent plan
├── findings/                        # Lessons learned
│   ├── 001_output_lessons.md       # First finding
│   └── 015_iterator_fix_implemented.md  # Recent finding
├── implementation/                  # Implementation summaries
│   └── 001_input_provider_implementation_summary.md
└── research/                        # Research reports
    ├── 001_batch_output_research.md  # First research
    └── 009_iterator_analysis_summary.md  # Recent research
```

### Code Organization

See [Code Organization Standards](../../Docs/maintenance/CODE_ORGANIZATION.md)

#### Critical Rules

**NO DECORATORS**: The ModelChecker codebase does not use decorators. Always use explicit method calls and standard class inheritance patterns instead of decorators. This includes:
- No `@property` decorators - use explicit getter/setter methods
- No `@abstractmethod` decorators - use `raise NotImplementedError` in base classes
- No custom decorators - use explicit function calls
- No `@classmethod` or `@staticmethod` - use regular methods or module-level functions

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

#### NO BACKWARDS COMPATIBILITY
- **ALWAYS break compatibility** for cleaner architecture - never add optional parameters
- **No compatibility layers** - update all call sites when changing interfaces
- **Remove deprecated patterns immediately** - no deprecation periods
- **Unify interfaces** - similar components must use identical patterns

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

### Debugging Protocol

**Systematic Debugging Guidelines:**
- **Gather information systematically** without requiring user interaction
- **Avoid commands that block** (e.g., prompts requiring user input)
- **Create test scripts** to isolate issues without modifying the codebase
- **Document findings** in specs/debug/ with clear analysis
- **Compile comprehensive reports** when stuck, highlighting key findings
- **Request user review** only after exhausting autonomous investigation

**Debugging Process:**
1. Create analysis document in specs/debug/
2. Reproduce issue with minimal test case
3. Trace execution flow and identify root causes
4. Test potential fixes in isolation
5. Implement and verify solution
6. Document lessons learned

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

[← Back to Technical Docs](README.md) | [Implementation →](IMPLEMENTATION.md) | [Tests Guide →](TESTS.md) | [Code Maintenance →](../maintenance/README.md) | [Development →](DEVELOPMENT.md)
