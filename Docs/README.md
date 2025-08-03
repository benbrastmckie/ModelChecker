# ModelChecker Documentation Hub

[← Back to Project Root](../README.md) | [Technical Docs →](../Code/docs/README.md) | [Code →](../Code/README.md)

## Overview

This directory contains general project documentation for the ModelChecker framework, focusing on installation, getting started, theoretical background, and research methodology. For technical documentation including development guides, architecture, and testing, see the [Technical Documentation](../Code/docs/README.md).

## Directory Structure

```
Docs/
├── README.md                       # This file - documentation hub
├── installation/                   # Modular installation guides
│   ├── README.md                   # Installation overview and navigation
│   ├── BASIC_INSTALLATION.md       # Standard pip installation guide
│   ├── TROUBLESHOOTING.md          # Platform-specific solutions
│   ├── VIRTUAL_ENVIRONMENTS.md     # Virtual environment setup
│   ├── JUPYTER_SETUP.md            # Jupyter notebook configuration
│   └── DEVELOPER_SETUP.md          # Development environment setup
├── GETTING_STARTED.md              # Quick start tutorial for new users
├── COMPARE_THEORIES.md             # Theory comparison guide and best practices
├── methodology/                    # Programmatic semantics methodology
│   ├── README.md                   # Methodology hub and overview
│   ├── BUILDER_PATTERN.md          # BuildModule/BuildExample architecture
│   ├── SYNTAX.md                   # AST conversion pipeline
│   ├── SEMANTICS.md                # Constraint generation
│   └── MODELS.md                   # SMT solving and interpretation
├── HYPERINTENSIONAL.md             # Theoretical background and core concepts
├── Z3_BACKGROUND.md                # Introduction to Z3 theorem prover
├── REFERENCES.md                   # Complete academic bibliography
└── FINDINGS.md                     # Research findings and logical insights
```

## Documentation Overview

This directory contains comprehensive documentation for the ModelChecker project, covering installation, usage, development, and theoretical background.

## Quick Navigation

### Getting Started

- **[Installation Hub](installation/README.md)** - Modular installation guides for all scenarios
- **[Basic Installation](installation/BASIC_INSTALLATION.md)** - Quick pip installation
- **[Getting Started Guide](GETTING_STARTED.md)** - Create your first ModelChecker project
- **[Code Package](../Code/README.md)** - ModelChecker implementation and usage

### Technical Documentation

- **[Technical Docs Hub](../Code/docs/README.md)** - Development and architecture documentation
- **[Development Guide](../Code/docs/DEVELOPMENT.md)** - Contributing and development workflow
- **[Testing Guide](../Code/docs/TESTS.md)** - Testing methodology and best practices
- **[Tools Guide](../Code/docs/TOOLS.md)** - Advanced features and debugging
- **[Examples Guide](../Code/docs/EXAMPLES.md)** - Standard example file structure

### Theory and Background

- **[Theory Comparison Guide](COMPARE_THEORIES.md)** - Compare multiple semantic theories
- **[Academic References](REFERENCES.md)** - Complete bibliography with BibTeX citations
- **[Hyperintensional Semantics](HYPERINTENSIONAL.md)** - Truthmaker semantics explained
- **[Z3 Background](Z3_BACKGROUND.md)** - Understanding the Z3 theorem prover
- **[Theory Library](../Code/src/model_checker/theory_lib/README.md)** - Available theories

### Research

- **[Methodology](methodology/README.md)** - Programmatic semantics methodology
- **[Findings](FINDINGS.md)** - Key insights and discoveries

## Documentation by Audience

### For New Users

1. Start with **[Installation](installation/README.md)** to set up ModelChecker
2. Follow **[Getting Started](GETTING_STARTED.md)** for your first project
3. Read the **[Main README](../Code/README.md)** for quick start examples
4. Explore **[Tools](../Code/docs/TOOLS.md)** for advanced features

### For Developers

1. Review **[Development Guide](../Code/docs/DEVELOPMENT.md)** for contribution guidelines
2. Study **[Testing Guide](../Code/docs/TESTS.md)** for testing practices
3. Check **[API Documentation](../Code/src/model_checker/README.md)** for implementation details
4. Read **[Architecture](../Code/docs/ARCHITECTURE.md)** for system design

### For Researchers

1. Read **[Hyperintensional Semantics](HYPERINTENSIONAL.md)** for theoretical foundations
2. Review **[Theory Comparison Guide](COMPARE_THEORIES.md)** for cross-theory analysis
3. Explore **[Methodology](methodology/README.md)** and **[Findings](FINDINGS.md)** for research context
4. Review **[Theory Library](../Code/src/model_checker/theory_lib/README.md)** for implementations

### For Educators

1. Use **[Hyperintensional Semantics](HYPERINTENSIONAL.md)** as teaching material
2. Reference **[Installation](installation/README.md)** for student setup
3. See **[Jupyter Setup](installation/JUPYTER_SETUP.md)** for notebook configuration
4. Explore **[Jupyter Notebooks](../Code/src/model_checker/theory_lib/logos/notebooks/)** for interactive demos

## Key Topics

### Installation and Setup

The **[Installation Documentation](installation/README.md)** provides:

- **[Basic Installation](installation/BASIC_INSTALLATION.md)** - pip install with options
- **[Troubleshooting](installation/TROUBLESHOOTING.md)** - Platform-specific solutions
- **[Virtual Environments](installation/VIRTUAL_ENVIRONMENTS.md)** - Isolated setups
- **[Jupyter Setup](installation/JUPYTER_SETUP.md)** - Notebook configuration
- **[Developer Setup](installation/DEVELOPER_SETUP.md)** - Contributing setup

### Hyperintensional Logic

The **[Hyperintensional Semantics Guide](HYPERINTENSIONAL.md)** covers:

- Truthmaker semantics fundamentals
- States, fusion, and evaluation
- Logical operators in hyperintensional context
- Implementation in ModelChecker

### Advanced Features

The **[Tools Documentation](../Code/docs/TOOLS.md)** explains:

- Model iteration for finding multiple models
- Theory comparison across semantic frameworks
- Maximize mode for performance benchmarking
- Debugging flags and constraint analysis

### Development Resources

The technical documentation in Code/docs/ includes:

- **[Development Guide](../Code/docs/DEVELOPMENT.md)** - Contributing workflow
- **[Architecture](../Code/docs/ARCHITECTURE.md)** - System design and components
- **[Style Guide](../Code/docs/STYLE_GUIDE.md)** - Coding standards quick reference
- **[Maintenance Standards](../Code/MAINTENANCE.md)** - Comprehensive standards

## Related Resources

### Code Documentation

- **[ModelChecker API](../Code/src/model_checker/README.md)** - Core API reference
- **[Architecture](../Code/docs/ARCHITECTURE.md)** - System design
- **[Theory Library](../Code/src/model_checker/theory_lib/README.md)** - Semantic theories

### Theory Documentation

- **[Logos Theory](../Code/src/model_checker/theory_lib/logos/README.md)** - Hyperintensional framework
- **[Exclusion Theory](../Code/src/model_checker/theory_lib/exclusion/README.md)** - Unilateral semantics
- **[Imposition Theory](../Code/src/model_checker/theory_lib/imposition/README.md)** - Fine's semantics

### External Resources

- **[GitHub Repository](https://github.com/benbrastmckie/ModelChecker)** - Source code
- **[Z3 Documentation](https://z3prover.github.io/)** - Z3 theorem prover

## References

This documentation hub follows the standards defined in [MAINTENANCE.md](../Code/MAINTENANCE.md) for consistent structure and navigation.

---

[← Back to Project Root](../README.md) | [Technical Docs →](../Code/docs/README.md) | [Code →](../Code/README.md)
