# Documentation Hub: ModelChecker User and Research Documentation

[← Back to Project](../README.md) | [Installation →](installation/README.md) | [Architecture →](architecture/README.md)

## Directory Structure

```
Docs/
├── README.md                       # This file - documentation hub and navigation
├── installation/                   # Setup and configuration guides
│   ├── README.md                   # Installation documentation hub
│   ├── BASIC_INSTALLATION.md       # Standard pip installation
│   ├── GETTING_STARTED.md          # First steps after installation
│   ├── TROUBLESHOOTING.md          # Platform-specific solutions
│   ├── VIRTUAL_ENVIRONMENTS.md     # Virtual environment setup
│   ├── JUPYTER_SETUP.md            # Jupyter notebook configuration
│   └── DEVELOPER_SETUP.md          # Development environment setup
├── architecture/                   # Programmatic semantics framework
│   ├── README.md                   # Architecture documentation hub
│   ├── PIPELINE.md                 # System design and integration
│   ├── BUILDER.md                  # Pipeline orchestration
│   ├── SYNTAX.md                   # AST conversion pipeline
│   ├── SEMANTICS.md                # Constraint generation
│   ├── MODELS.md                   # SMT solving and interpretation
│   └── ITERATOR.md                 # Model iteration system
├── usage/                          # Practical usage guides
│   ├── README.md                   # Usage documentation hub
│   ├── WORKFLOW.md                 # Comprehensive workflows
│   ├── TOOLS.md                    # Advanced tools and theory comparison
│   └── SEMANTICS.md              # Testing semantic constraints
├── theory/                         # Theoretical foundations
│   ├── README.md                   # Theory documentation hub
│   ├── HYPERINTENSIONAL.md         # Hyperintensional logic
│   ├── Z3_BACKGROUND.md            # SMT solver background
│   ├── REFERENCES.md               # Academic bibliography
│   └── IMPLEMENTATION.md           # Implementation insights
└── maintenance/                    # Standards and best practices
    ├── README.md                   # Maintenance documentation hub
    ├── AUDIENCE.md                 # Audience guidelines
    ├── CODE_ORGANIZATION.md        # Code structure guidelines
    ├── ERROR_HANDLING.md           # Error handling patterns
    ├── EXAMPLES_STRUCTURE.md       # Example file standards
    ├── FORMULA_FORMATTING.md       # Formula notation conventions
    ├── PERFORMANCE.md              # Performance optimization
    ├── TESTING_STANDARDS.md        # Testing requirements
    ├── UNICODE_GUIDELINES.md       # Unicode character usage
    ├── VERSION_CONTROL.md          # Git best practices
    ├── quality/                    # Documentation quality control
    │   ├── README.md               # Quality standards hub
    │   ├── DOCUMENTATION_STANDARDS.md # Documentation principles
    │   ├── README_STANDARDS.md     # README requirements
    │   └── CONTINUOUS_IMPROVEMENT.md # Quality improvement processes
    └── templates/                  # Documentation templates
        ├── README.md               # Template usage guide
        ├── README_TEMPLATE.md      # Basic README template
        ├── THEORY_README.md        # Theory README template
        └── SUBTHEORY_README.md     # Subtheory README template
```

## Overview

This directory serves as the **comprehensive documentation hub** for the ModelChecker framework, providing user guides, research documentation, and theoretical background. The documentation is organized into **5 major categories**: installation and setup, programmatic semantics architecture, practical usage workflows, theoretical foundations, and maintenance standards.

The documentation follows an **interdisciplinary approach**, making computational logic accessible to researchers from diverse backgrounds including logic, linguistics, computer science, and AI. Each section is designed to be self-contained while providing clear navigation to related topics, enabling readers to find exactly what they need without navigating through unrelated content.

For **technical implementation details**, including API documentation, development workflows, and architecture specifics, see the [Developer Documentation](../Code/docs/README.md). This separation ensures that users focused on applying ModelChecker can find practical guides here, while developers working on the framework itself have dedicated technical resources.

## Theory Examples

### Quick ModelChecker Demo

Get started with a simple validity check:

```bash
# Install ModelChecker
pip install model-checker
```

```python
# Create example file: modus_ponens.py
from model_checker.theory_lib.logos import get_theory

theory = get_theory()

# Modus ponens example
MP_premises = ["A", "A \\rightarrow B"]
MP_conclusions = ["B"]
MP_settings = {
    'N': 3,                    # Max atomic propositions
    'expectation': False       # False = expect theorem
}
MP_example = [
    MP_premises,
    MP_conclusions,
    MP_settings
]

example_range = {"MP": MP_example}
semantic_theories = {"logos": theory}
```

### Understanding the Pipeline

The methodology transforms logical arguments through stages:

```
Input: premises=["A"], conclusions=["B"], settings={'N': 3}

1. Syntax parsing → AST construction
2. Semantic interpretation → Z3 constraints
3. Model finding → Satisfying assignment
4. Result interpretation → Countermodel display
```

### Exploring Theoretical Foundations

The ModelChecker can accommodate a wide range of different semantic theories, providing a methodology for implementing semantic theories programmatically as well as a TheoryLib consisting of different semantic theories that have been implemented so far.

To bring out the contrast between theories with different expressive powers, consider the following sentences:

```python
# Hyperintensional semantics reveals three levels of equivalence:
# Consider logically equivalent formulas with different structure

# 1. Material equivalence (same truth value in actual world):
"(A \\leftrightarrow (A \\wedge (A \\vee B)))"
# - Logos: Theorem

# 2. Necessary equivalence (same truth value in all possibilities):
"\\Box(A \\leftrightarrow (A \\wedge (A \\vee B)))"
# - Logos: Theorem

# 3. Propositional identity (express the same hyperintensional proposition):
"(A \\equiv (A \\wedge (A \\vee B)))"
# - Logos: Finds countermodels (different subject-matters)
```

For hands-on examples, see [Getting Started](installation/GETTING_STARTED.md).

## Subdirectories

### [installation/](installation/)

**Comprehensive installation and setup guides** covering 6 scenarios from basic pip installation to full development environments. Includes platform-specific troubleshooting, virtual environment management, and Jupyter configuration. See [installation/README.md](installation/README.md) for complete setup documentation.

### [architecture/](architecture/)

**Programmatic semantics framework documentation** explaining how ModelChecker transforms logical formulas into executable semantic programs. Covers system architecture, pipeline orchestration, syntax processing, constraint generation, model finding, and iteration strategies. See [architecture/README.md](architecture/README.md) for the complete methodology guide.

### [usage/](usage/)

**Practical usage guides** for working with ModelChecker, including comprehensive workflows for all features and specialized theory comparison techniques. Covers command-line usage, debugging, performance optimization, and integration patterns. See [usage/README.md](usage/README.md) for practical workflows.

### [theory/](theory/)

**Theoretical foundations and research context** including hyperintensional logic, truthmaker semantics, SMT solving background, and implementation insights. Provides the academic grounding for ModelChecker's approach. See [theory/README.md](theory/README.md) for theoretical documentation.

### [maintenance/](maintenance/)

**Standards and best practices** ensuring consistency across the codebase. Covers comprehensive development standards, documentation quality control, and template resources. Includes specialized quality standards directory and documentation templates for consistent structure. See [maintenance/README.md](maintenance/README.md) for all standards.

## Documentation

### For New Users

- **[Installation Guide](installation/README.md)** - Choose your setup path
- **[Getting Started](installation/GETTING_STARTED.md)** - First steps tutorial
- **[Basic Workflows](usage/WORKFLOW.md#basic-workflows)** - Running examples

### For Researchers

- **[Theoretical Foundations](theory/README.md)** - Academic background
- **[Architecture Overview](architecture/README.md)** - Programmatic semantics
- **[ModelChecker Tools](usage/TOOLS.md)** - Advanced features and comparison
- **[Constraint Testing](usage/SEMANTICS.md)** - Proving properties by absence

### For Developers

- **[Developer Setup](installation/DEVELOPER_SETUP.md)** - Contributing environment
- **[Technical Docs](../Code/docs/README.md)** - Implementation details
- **[Maintenance Standards](maintenance/README.md)** - Code quality guides
- **[Quality Standards](maintenance/quality/README.md)** - Documentation quality control
- **[Documentation Templates](maintenance/templates/README.md)** - Standardized README structures

## Key Features

### Comprehensive Coverage

- **5 major documentation categories** with dedicated README hubs
- **30+ detailed guides** covering all aspects of ModelChecker
- **Quality-controlled documentation** with comprehensive standards and templates
- **Interdisciplinary approach** serving diverse academic backgrounds
- **Clear navigation** with consistent structure and cross-references

### User-Focused Organization

- **Installation options** from basic to advanced development setups
- **Practical workflows** for common tasks and debugging
- **Theory comparison** guides for research applications
- **Getting started** tutorials for immediate productivity

### Research Integration

- **Theoretical grounding** in truthmaker semantics
- **Academic bibliography** with proper citations
- **Implementation insights** bridging theory and practice
- **Architecture documentation** for understanding the approach

## References

### Primary Documentation

- **[Technical Documentation](../Code/docs/README.md)** - Development and API docs
- **[Theory Library](../Code/src/model_checker/theory_lib/README.md)** - Implementations
- **[Main Package](../Code/README.md)** - ModelChecker overview

### External Resources

- **[GitHub Repository](https://github.com/benbrastmckie/ModelChecker)** - Source code
- **[PyPI Package](https://pypi.org/project/model-checker/)** - Python package
- **[Z3 Prover](https://z3prover.github.io/)** - SMT solver documentation

---

[← Back to Project](../README.md) | [Installation →](installation/README.md) | [Technical Docs →](../Code/docs/README.md)
