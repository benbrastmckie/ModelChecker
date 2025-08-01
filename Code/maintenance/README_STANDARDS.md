# README.md Standards

[← Documentation Standards](DOCUMENTATION_STANDARDS.md) | [Back to Maintenance](README.md) | [Code Organization →](CODE_ORGANIZATION.md)

## Overview

This document defines the required structure for all README.md files in the ModelChecker repository. Every directory must have a README.md following this structure.

## Special Exception: Code/README.md

The `/Code/README.md` file is **exempt** from these standards because it serves as the package description on PyPI. This file:
- Does not require navigation links
- Does not require a file tree
- Should be formatted for PyPI display
- Must focus on user-facing documentation

All other README.md files must follow the standards below.

## Required Nine-Section Structure

### 1. Title with Navigation

```markdown
# [Directory/Component Name]: [Descriptive Tagline]

[← Back to Parent](../README.md) | [Key Doc →](docs/README.md) | [Key Resource →](link2)
```

Use descriptive taglines that capture the essence of the component.

### 2. Directory Structure

**REQUIRED**: Every README must begin with a complete tree showing all contents:

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

Include file extensions and meaningful descriptions after # comments.

### 3. Overview

Provide a comprehensive overview including:
- **Primary Purpose**: What this component does
- **Key Features**: Main capabilities
- **Integration Context**: How it fits into ModelChecker
- **Academic Background**: Relevant theoretical foundations

### 4. Theory Examples (formerly Quick Start)

Focus on theory-specific aspects:

```markdown
## Theory Examples

### Theory-Specific Imports

```python
from model_checker.theory_lib.logos import LogosOperatorRegistry

# Load specific subtheories
registry = LogosOperatorRegistry()
registry.load_subtheories(['modal', 'constitutive'])
```

### Example Definition

```python
MODAL_TH_1_premises = ['\\Box A']
MODAL_TH_1_conclusions = ['A']
MODAL_TH_1_settings = {
    'N': 3,                    # Number of atomic states
    'contingent': False,       # Modal-specific setting
    'expectation': False,      # False = expect theorem
}
```

### Running Examples

```bash
model-checker path/to/theory/examples.py
```
```

Link to [docs/EXAMPLES.md](../docs/EXAMPLES.md) for complete file structure.

### 5. Subdirectories

Summarize each subdirectory:

```markdown
## Subdirectories

### [docs/](docs/)
Comprehensive documentation including user guides and technical references. See [docs/README.md](docs/README.md) for navigation.

### [tests/](tests/)  
Complete test suite covering semantic functionality and operator behavior. See [tests/README.md](tests/README.md) for methodology.
```

### 6. Documentation

Organize by user type:

```markdown
## Documentation

### For New Users
- **[User Guide](docs/USER_GUIDE.md)** - Practical usage and examples
- **[Interactive Notebooks](notebooks/README.md)** - Hands-on learning

### For Researchers  
- **[Architecture Guide](docs/ARCHITECTURE.md)** - System design
- **[Academic References](#references)** - Theoretical background

### For Developers
- **[API Reference](docs/API_REFERENCE.md)** - Complete API documentation
- **[Development Guide](../../../docs/DEVELOPMENT.md)** - Framework integration
```

### 7. Key Features (Optional)

Highlight distinguishing capabilities when relevant.

### 8. References

Include academic citations and related resources:

```markdown
## References

### Primary Sources
- Author (Year) ["Paper Title"](link), Journal Name

### Related Resources
- **[Related Theory](../other_theory/)** - Brief description
- **[Framework Documentation](../../README.md)** - Main documentation
```

### 9. Navigation Footer

```markdown
---

[← Back to Parent](../README.md) | [Documentation →](docs/README.md) | [Examples →](examples.py)
```

## Theory Documentation Structure

Every theory in `theory_lib/` must maintain this documentation structure:

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

### Theory Documentation Example Standards

Theory documentation should focus on what makes each theory unique:

**Include:**
- Theory-specific imports and operator loading
- Individual example definitions with theory-specific settings
- Theory-specific settings with meaningful comments
- Command-line usage for running examples
- Link to EXAMPLES.md for complete file structure

**Omit:**
- Generic boilerplate (unit_tests dictionary, semantic_theories setup)
- Standard executable setup (if __name__ == "__main__")
- Repetitive settings explanations covered in EXAMPLES.md
- Generic example_range and general_settings

### Subtheory Documentation Standards

For theories with modular subtheories (e.g., Logos), each subtheory must:

1. Follow the standard 9-section README format
2. State hyperintensional semantics implementation in overview
3. Clearly distinguish primitive vs defined operators
4. Include operator reference with:
   - Symbol (LaTeX and Unicode)
   - Name, arity, and type
   - Truth conditions (informal then Z3)
   - Usage examples and key properties

### Accuracy Requirements

- Example counts must match actual files
- Operator counts must match implementations
- Truth conditions must match code
- Use grep to verify: `grep "^[A-Z]*_[CT][MH]_[0-9]*_example =" examples.py | wc -l`

## Navigation Best Practices

- Include 2-4 most relevant links
- Use consistent arrow symbols (← and →)
- Always include parent directory link
- Prioritize commonly accessed resources

## Content Principles

- Start with specific, concrete information
- Use quantitative details ("19 operators", "177 examples")
- Show working code examples
- Link rather than duplicate information
- Focus on practical usage while grounding in theory

---

[← Documentation Standards](DOCUMENTATION_STANDARDS.md) | [Back to Maintenance](README.md) | [Code Organization →](CODE_ORGANIZATION.md)