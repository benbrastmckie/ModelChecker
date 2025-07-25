# ModelChecker Maintenance Standards

This document establishes coding, documentation, and maintenance standards for the ModelChecker repository. All contributors should follow these guidelines to ensure consistency and quality across the codebase.

## Table of Contents

- [Unicode Character Guidelines](#unicode-character-guidelines)
- [Documentation Standards](#documentation-standards)
- [README.md Standards](#readmemd-standards)
- [Non-README Documentation Standards](#non-readme-documentation-standards)
- [Theory Documentation Structure](#theory-documentation-structure)
- [Code Organization Standards](#code-organization-standards)
- [Testing Standards](#testing-standards)
- [Version Control Standards](#version-control-standards)
- [Performance Guidelines](#performance-guidelines)
- [Error Handling Standards](#error-handling-standards)

## Unicode Character Guidelines

### General Rule

Unicode characters (∧, ∨, ¬, □, ◇, →, ↔, etc.) are **ONLY** permitted in comments and documentation for improving human readability. They must **NEVER** be used in actual code, operator definitions, or any text that the ModelChecker parser processes.

### Correct Usage

```python
# CORRECT - Unicode in comments only
class Negation(Operator):
    """Negation operator (¬) for logical negation."""
    def __init__(self):
        super().__init__("\\neg", 1)  # LaTeX notation for parser

# CORRECT - Unicode in docstrings
def conjunction_operator():
    """Implements logical conjunction (∧)."""
    return "\\wedge"  # Parser expects LaTeX notation
```

### Incorrect Usage

```python
# INCORRECT - Unicode in operator definition
class Negation(Operator):
    def __init__(self):
        super().__init__("¬", 1)  # WRONG: Parser cannot read this

# INCORRECT - Unicode in formulas
formula = "p ∧ q"  # WRONG: Must use "p \\wedge q"
```

### LaTeX Notation Reference

The ModelChecker parser expects the following LaTeX notation:

| Operator      | Unicode (docs only) | LaTeX (code)             | Description          |
| ------------- | ------------------- | ------------------------ | -------------------- |
| Negation      | ¬                   | `\\neg`                  | Logical NOT          |
| Conjunction   | ∧                   | `\\wedge`                | Logical AND          |
| Disjunction   | ∨                   | `\\vee`                  | Logical OR           |
| Implication   | →                   | `\\to` or `\\rightarrow` | Material conditional |
| Biconditional | ↔                  | `\\leftrightarrow`       | If and only if       |
| Necessity     | □                   | `\\Box`                  | Modal necessity      |
| Possibility   | ◇                   | `\\Diamond`              | Modal possibility    |
| Future        | ⏵                   | `\\future`               | Temporal future      |
| Past          | ⏴                   | `\\past`                 | Temporal past        |
| Top           | ⊤                   | `\\top`                  | Logical truth        |
| Bottom        | ⊥                   | `\\bot`                  | Logical falsehood    |

## Documentation Standards

### General Requirements

1. **No Emojis**: Never use emojis anywhere in the codebase, documentation, or output
2. **No Unicode in Code Examples**: All code examples must use LaTeX notation
3. **Consistent Formatting**: Use consistent header levels and formatting
4. **Working Examples**: All code examples must be tested and working
5. **Cross-References**: Link between related documentation

### Content Organization Principles

Based on analysis of exemplary documentation, follow these principles:

1. **Progressive Disclosure**: Start with overview and quick start, then dive into details
2. **Audience Segmentation**: Organize information by user type (new users, researchers, developers)
3. **Quantitative Specificity**: Include concrete numbers (operators, examples, test cases)
4. **Integration Context**: Explain how components fit into the larger framework
5. **Theoretical Grounding**: Link implementation to academic foundations where relevant
6. **Practical Usability**: Always include working code examples and clear usage instructions
7. **Redundancy Reduction**: Cross-reference rather than duplicate information
8. **Consistent Navigation**: Use standardized link patterns throughout the repository

### Directory Documentation Rule

**EVERY directory in the repository MUST have a README.md file** that documents its contents and purpose.

## README.md Standards

All README.md files throughout the repository must follow this precise structure:

### Special Exception: Code/README.md

The `/Code/README.md` file is **exempt** from these standard requirements because it serves as the package description on PyPI. This file:
- Does not require navigation links at the top
- Does not require a complete file tree at the beginning
- Should be formatted for optimal display on PyPI
- Must focus on user-facing documentation rather than directory structure

All other README.md files must follow the standards below:

### 1. Title with Navigation (Top)

```markdown
# [Directory/Component Name]: [Descriptive Tagline]

[← Back to Parent](../README.md) | [Key Doc →](docs/README.md) | [Key Resource →](link2)
```

**Best Practices:**
- Use descriptive taglines that capture the essence (e.g., "Complete Computational Realization of Unilateral Semantics")
- Navigation links should prioritize the most important related resources
- Always include a back link to parent directory

### 2. File/Directory Tree

**REQUIRED**: Every README.md must begin with a complete tree showing all contents:

```markdown
## Directory Structure
```
directory_name/
├── README.md               # This file - comprehensive overview
├── __init__.py            # Module initialization and public API
├── semantic.py            # Core semantic implementation
├── operators.py           # Operator definitions and registry
├── examples.py            # Example formulas and test cases
├── docs/                  # Documentation directory (see docs/README.md)
├── tests/                 # Test suite (see tests/README.md)  
└── notebooks/             # Interactive tutorials (see notebooks/README.md)
```
```

**Best Practices:**
- Use consistent indentation and tree structure
- Include file extensions for clarity
- Add meaningful descriptions after # comments
- For directories, reference their README.md files
- Show the logical organization and dependencies

### 3. Overview Section

**REQUIRED**: Provide a comprehensive overview that includes:

1. **Primary Purpose**: What this component/theory/module does
2. **Key Features**: Main capabilities or distinguishing characteristics  
3. **Integration Context**: How it fits into the larger ModelChecker framework
4. **Academic/Theoretical Background**: Relevant citations or theoretical foundations (for theories)

**Best Practices:**
- Start with a strong declarative sentence about the component's role
- Use 2-4 paragraphs for adequate depth without overwhelming
- Include quantitative details when relevant (e.g., "20 logical operators across 5 subtheories")
- Link to broader theoretical contexts where appropriate

### 4. Quick Start Section

**REQUIRED**: Provide immediate usability with practical examples:

```markdown
## Quick Start

```python
from model_checker.theory_lib.logos import get_theory
from model_checker import BuildExample

# Load the theory
theory = get_theory()

# Create and check a formula
model = BuildExample("example", theory)
result = model.check_formula("\\Box p \\rightarrow p")
print(f"T axiom is {'valid' if result else 'invalid'}")
```

```
**Best Practices:**
- Use realistic, working code examples
- Show the most common use cases first
- Use LaTeX notation for formulas, not Unicode
- Include expected output where helpful
- Keep examples simple but meaningful

### 5. Subdirectory Summaries

**REQUIRED**: Provide a summary for each subdirectory with links:

```markdown
## Subdirectories

### [docs/](docs/)
Comprehensive documentation including user guides, technical references, and architecture details. The documentation is organized for different audiences from beginners to researchers. See [docs/README.md](docs/README.md) for the complete navigation guide.

### [tests/](tests/)  
Complete test suite covering semantic functionality, operator behavior, and example validation. Includes unit tests, integration tests, and comprehensive coverage of logical principles. See [tests/README.md](tests/README.md) for testing methodology.

### [notebooks/](notebooks/)
Interactive Jupyter notebooks providing hands-on learning experiences with the theory. Features progressive tutorials, comparative analyses, and research-level demonstrations. See [notebooks/README.md](notebooks/README.md) for the complete collection.
```

**Best Practices:**
- Summarize the purpose and scope of each subdirectory
- Mention the target audience or use case
- Always link to the subdirectory's README.md
- Use consistent formatting and depth across summaries

### 6. Documentation Links Section

**REQUIRED**: Organize documentation by user type and purpose:

```markdown
## Documentation

### For New Users
- **[User Guide](docs/USER_GUIDE.md)** - Practical usage and examples
- **[Interactive Notebooks](notebooks/README.md)** - Hands-on learning materials
- **[Settings Reference](docs/SETTINGS.md)** - Configuration options

### For Researchers  
- **[Architecture Guide](docs/ARCHITECTURE.md)** - System design and implementation
- **[Academic References](#references)** - Theoretical background and citations
- **[Test Examples](tests/README.md)** - Validation and edge cases

### For Developers
- **[API Reference](docs/API_REFERENCE.md)** - Complete API documentation
- **[Contributing Guidelines](#contributing)** - Development workflow
- **[Development Guide](../../../docs/DEVELOPMENT.md)** - Framework integration
```

**Best Practices:**
- Organize by user persona (new users, researchers, developers)
- Use descriptive link text that explains the purpose
- Include both internal and external documentation references
- Maintain consistent formatting across sections

### 7. References and Related Resources

**ENCOURAGED**: Include academic references and related resources:

```markdown
## References

### Primary Sources
- Author (Year) ["Paper Title"](link), Journal Name
- Author (Year) ["Another Paper"](link), Conference Proceedings

### Related Resources
- **[Related Theory](../other_theory/)** - Brief description of relationship
- **[Framework Documentation](../../README.md)** - Main system documentation
- **[External Resource](link)** - Description of external relevance
```

### 8. Navigation Links (Bottom)

```markdown
---

[← Back to Parent](../README.md) | [Documentation →](docs/README.md) | [Examples →](examples.py)
```

**Best Practices:**
- Include 2-4 most relevant navigation targets
- Use consistent arrow symbols (← and →)
- Prioritize the most commonly accessed related resources
- Always include a back link to the parent directory

## Non-README Documentation Standards

All documentation files that are NOT README.md files must follow these standards:

### 1. Title and Navigation (Top)

```markdown
# [Document Title]

[← Back to [Source]](../README.md) | [Related Doc →](related.md)
```

### 2. Table of Contents

**REQUIRED**: All non-README documentation must have a table of contents with links:

```markdown
## Table of Contents

1. [Introduction](#introduction)
2. [Core Concepts](#core-concepts)
   - [Subsection 1](#subsection-1)
   - [Subsection 2](#subsection-2)
3. [Implementation Details](#implementation-details)
4. [Examples](#examples)
5. [References](#references)
```

### 3. Content Sections

Use the section IDs from the table of contents for proper linking.

### 4. Navigation Links (Bottom)

```markdown
---

[← Back to [Source]](../README.md) | [Next Topic →](next.md)
```

## Theory Documentation Structure

Every theory in `theory_lib/` must maintain the following documentation structure:

```
theory_name/
├── README.md              # Theory overview with file tree
├── docs/
│   ├── README.md         # Documentation hub with file tree
│   ├── API_REFERENCE.md  # Complete API documentation
│   ├── ARCHITECTURE.md   # Technical implementation details
│   ├── USER_GUIDE.md     # Practical usage guide
│   ├── ITERATE.md        # Model iteration features
│   └── SETTINGS.md       # Configuration options
├── examples.py           # Example formulas
├── semantic.py          # Core semantic implementation
├── operators.py         # Operator definitions
├── tests/               # Test suite
│   └── README.md        # Test documentation with file tree
└── notebooks/           # Jupyter notebooks
    └── README.md        # Notebook guide with file tree
```

### Theory-Specific Documentation Requirements

Each theory must have these specific documentation files with the required sections:

#### Theory Root README.md

Must include:

1. Title with tagline
2. Navigation links at top
3. Complete directory structure
4. Theory overview (2-3 paragraphs)
5. Quick start example
6. Subdirectory summaries with links
7. Documentation links
8. Academic references
9. Navigation links at bottom

#### docs/API_REFERENCE.md

Must include:

1. Navigation links at top
2. Table of contents
3. API overview
4. Core functions documentation
5. Classes documentation
6. Operators reference
7. Type definitions
8. Examples
9. Error handling
10. Navigation links at bottom

## Code Organization Standards

### File Naming

- Use lowercase with underscores: `my_module.py`
- Test files: `test_[module_name].py`
- Documentation: UPPERCASE.md for standard docs

### Import Organization

```python
# Standard library imports
import os
import sys
from typing import Dict, List, Optional

# Third-party imports
import z3

# Local imports
from model_checker.base import BaseClass
from .local_module import LocalClass
```

### Class and Function Naming

- Classes: PascalCase (e.g., `BimodalSemantics`)
- Functions: snake_case (e.g., `get_theory()`)
- Constants: UPPER_SNAKE_CASE (e.g., `DEFAULT_SETTINGS`)
- Private methods: Leading underscore (e.g., `_internal_method()`)

## Testing Standards

### Test File Organization

```
theory_name/
└── tests/
    ├── README.md           # Test documentation with file tree
    ├── __init__.py
    ├── test_semantic.py    # Test semantic components
    ├── test_operators.py   # Test individual operators
    ├── test_examples.py    # Test example formulas
    └── test_iterate.py     # Test model iteration
```

### Test Documentation

Every `tests/` directory must have a README.md that includes:

1. Complete file tree of test files
2. Description of each test file
3. How to run the tests
4. Test categories and coverage

## Version Control Standards

### Commit Messages

- Use present tense: "Add feature" not "Added feature"
- Be descriptive but concise
- Reference issues when applicable: "Fix #123: Resolve import error"

### Branch Naming

- Feature branches: `feature/description`
- Bug fixes: `fix/description`
- Documentation: `docs/description`

## Performance Guidelines

### Z3 Optimization

1. Minimize the number of Z3 variables
2. Use appropriate bit vector sizes
3. Add constraints in order of importance
4. Consider timeout settings for complex formulas

### Memory Management

1. Clean up temporary objects
2. Use generators for large iterations
3. Implement proper cleanup in `__del__` methods

## Error Handling Standards

### User-Friendly Messages

```python
# GOOD
if not os.path.exists(file_path):
    raise FileNotFoundError(
        f"Example file '{file_path}' not found. "
        f"Check that the file exists and the path is correct."
    )

# BAD
assert os.path.exists(file_path), "File not found"
```

### Validation

1. Validate inputs early
2. Provide specific error messages
3. Suggest corrections when possible
4. Never expose internal implementation details in errors

## Documentation Templates

### README.md Template

```markdown
# Component Name: Descriptive Tagline

[← Back to Parent](../README.md) | [Documentation →](docs/README.md) | [Key Resource →](link)

## Directory Structure
```
component_name/
├── README.md               # This file - comprehensive overview
├── __init__.py            # Module initialization and public API
├── core_file.py           # Core implementation
├── docs/                  # Documentation directory (see docs/README.md)
└── tests/                 # Test suite (see tests/README.md)
```

## Overview

[Component overview with purpose, key features, integration context, and theoretical background]

## Quick Start

```python
# Working code example demonstrating basic usage
from model_checker.component import main_function
result = main_function("example")
```

## Subdirectories

### [docs/](docs/)
[Description of documentation contents and target audience]

## Documentation

### For New Users
- **[User Guide](docs/USER_GUIDE.md)** - Practical usage guide

### For Developers  
- **[API Reference](docs/API_REFERENCE.md)** - Technical documentation

## References

### Primary Sources
- Author (Year) ["Title"](link), Journal

---

[← Back to Parent](../README.md) | [Documentation →](docs/README.md)
```

### API_REFERENCE.md Template

```markdown
# Component API Reference

[← Back to README](../README.md) | [User Guide →](USER_GUIDE.md)

## Table of Contents

1. [Overview](#overview)
2. [Core Functions](#core-functions)
3. [Classes](#classes)
4. [Examples](#examples)
5. [Error Handling](#error-handling)

## Overview

[Brief description of API scope and purpose]

## Core Functions

### `function_name(param1, param2=None)`

Description of what the function does.

**Parameters:**
- `param1` (type): Description
- `param2` (type, optional): Description

**Returns:**
- `type`: Description

**Example:**
```python
result = function_name("value")
```

---

[← Back to README](../README.md) | [Architecture →](ARCHITECTURE.md)
```

## Maintenance Checklist

When modifying or adding to the repository:

### Documentation Checklist

- [ ] Every directory has a README.md with complete file tree (except /Code/README.md)
- [ ] All README.md files have navigation links at top and bottom (except /Code/README.md)
- [ ] All README.md files summarize and link to subdirectories
- [ ] All non-README docs have table of contents with links
- [ ] All non-README docs have navigation links at top and bottom
- [ ] No emojis used anywhere
- [ ] No unicode in code examples (LaTeX notation used instead)
- [ ] /Code/README.md is formatted for PyPI display

### Code Checklist

- [ ] All operator definitions use LaTeX notation (not Unicode)
- [ ] All required documentation files are present
- [ ] Code examples in documentation are tested
- [ ] Public APIs have comprehensive docstrings
- [ ] Tests cover new functionality
- [ ] No debug code in production files
- [ ] Imports are properly organized
- [ ] Error messages are user-friendly

## Conclusion

Following these standards ensures that the ModelChecker remains maintainable, consistent, and user-friendly. When in doubt, prioritize clarity and consistency over cleverness or brevity. Remember: every directory needs a README.md, every README.md needs a file tree, and all documentation needs proper navigation.
