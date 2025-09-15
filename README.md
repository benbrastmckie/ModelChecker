# ModelChecker: Unified Programmatic Semantics Framework

[Code →](Code/README.md) | [Documentation →](Docs/README.md) | [Theory Library →](Code/src/model_checker/theory_lib/README.md)

## Directory Structure

```
ModelChecker/
├── Code/                           # Main implementation directory (see Code/README.md)
│   ├── src/                        # Source code
│   ├── docs/                       # Technical documentation
│   ├── specs/                      # Implementation specifications
│   └── tests/                      # Test suites
├── Docs/                           # General project documentation (see Docs/README.md)
│   ├── installation/               # Modular installation guides
│   ├── GETTING_STARTED.md          # Quick start guide
│   ├── usage/                      # Practical usage guides
│   │   ├── WORKFLOW.md             # Usage workflows
│   │   └── COMPARE_THEORIES.md     # Theory comparison
│   ├── methodology/                # Programmatic semantics methodology
│   │   ├── README.md               # Methodology overview
│   │   ├── BUILDER.md              # Pipeline orchestration
│   │   ├── SYNTAX.md               # AST conversion
│   │   ├── SEMANTICS.md            # Constraint generation
│   │   ├── MODELS.md               # SMT solving
│   │   └── ITERATOR.md             # Model iteration
│   ├── ARCHITECTURE.md             # System design and overview
│   ├── HYPERINTENSIONAL.md         # Theoretical background
│   ├── Z3_BACKGROUND.md            # SMT solver information
│   └── FINDINGS.md                 # Research findings
├── Images/                         # Screenshots and diagrams
└── README.md                       # This file - project overview
```

## Overview

The **ModelChecker** provides a [programmatic methodology](Docs/methodology/README.md) for developing and exploring modular semantic theories. Built on the SMT solver [Z3](Docs/theory/Z3_BACKGROUND.md), the framework enables researchers to establish logical consequence over finite models, automatically generating readable countermodels when formulas or inferences are invalid. The framework includes the [**TheoryLib**](Code/src/model_checker/theory_lib/README.md), a growing library of semantic theories that users can clone, modify, and contribute back to the project for public use. The [Logos](Code/src/model_checker/theory_lib/logos/README.md) theory supports extensional, modal, counterfactual, and constitutive operators through a modular architecture designed for studying [hyperintensional logics](Docs/theory/HYPERINTENSIONAL.md) and promoting transparent, verifiable reasoning.

The project enables exploration of complex logical systems with multiple interacting operators that would be intractable to analyze manually. While Logos implements bilateral hyperintensional semantics, the TheoryLib also includes Bernard and Champollion's unilateral semantics for negation based on exclusion, Fine's imposition semantics for counterfactuals, and a bimodal logic for reasoning with tense and modality. The modular architecture features automatic dependency resolution, making it straightforward to build new theories on existing ones while clearly tracking their differences for comparative study.

> **Note on Documentation**: This project's documentation is designed for an interdisciplinary audience, welcoming both those new to programming and those new to formal logic and semantics. For our documentation philosophy and accessibility goals, see [Audience Guidelines](Docs/maintenance/AUDIENCE.md) and [Maintenance Standards](Docs/maintenance/README.md).

## Documentation Organization

The ModelChecker documentation is organized into two main areas:

- **[General Documentation](Docs/README.md)** - Installation, getting started, theoretical background, and research methodology
- **[Technical Documentation](Code/docs/README.md)** - Development guides, architecture, testing, and implementation details

This separation ensures users can quickly find installation and usage information while developers have easy access to technical specifications and contribution guidelines.

## Installation

For most users:
```bash
pip install model-checker
```

For comprehensive installation instructions including platform-specific guides, virtual environments, and development setup, see the [Installation Documentation](Docs/installation/README.md).

**Quick Links:**
- [Basic Installation](Docs/installation/BASIC_INSTALLATION.md) - Standard pip installation
- [NixOS Installation](Docs/installation/BASIC_INSTALLATION.md#nixos-installation) - NixOS-specific setup
- [Developer Setup](Docs/installation/DEVELOPER_SETUP.md) - Development environment
- [Troubleshooting](Docs/installation/TROUBLESHOOTING.md) - Common issues

### Development Installation

```bash
git clone https://github.com/benbrastmckie/ModelChecker
cd ModelChecker/Code
# Use the development CLI to run locally without installation:
./dev_cli.py examples/my_example.py
```

For comprehensive development setup instructions, including virtual environments and platform-specific guidance, see the [Development Guide](Code/docs/DEVELOPMENT.md). NixOS users can use the provided `shell.nix` configuration for automatic environment setup.

### With Jupyter Support

```bash
pip install model-checker[jupyter]
```

For Jupyter notebook features and interactive exploration, see the [Jupyter Integration Guide](Code/src/model_checker/jupyter/README.md).

## Quick Start

### Create a New Theory Project

```bash
# Create a project from an existing theory
model-checker -l logos
model-checker -l exclusion
model-checker -l imposition
model-checker -l bimodal
```

### Run Examples

When you load an existing theory using `model-checker -l <theory_name>`, it creates a new project directory containing all necessary files, including an `examples.py` file with pre-configured examples. You can then run this file to test the theory:

```bash
# Run a specific example file
model-checker path/to/examples.py
```

Replace `path/to/` with the actual path to your project directory (e.g., `project_my_theory/examples.py`).

### Example Structure

Basic `examples.py` files must take the following form:

```python
# Import theory components
from model_checker.theory_lib.logos import get_theory

# Load the theory
theory = get_theory()

# Define examples following the standard format

# Example 1: Extensional Modus Ponens
EXT_TH_1_premises = ["A", "(A \\rightarrow B)"]
EXT_TH_1_conclusions = ["B"]
EXT_TH_1_settings = {
    'N': 3,                         # Max number of atomic propositions
    'contingent': False,            # Allow non-contingent propositions
    'non_null': False,              # Allow the null state
    'non_empty': False,             # Allow empty verifier/falsifier sets
    'disjoint': False,              # Allow verifier/falsifier overlap
    'max_time': 10,                 # Timeout in seconds
    'iterate': 1,                   # Number of models to find
    'expectation': False,           # True = expect countermodel, False = expect theorem
}
EXT_TH_1_example = [
    EXT_TH_1_premises,
    EXT_TH_1_conclusions,
    EXT_TH_1_settings,
]

# Example 2: Counterfactual Modus Ponens
CF_TH_1_premises = ["A", "(A \\boxright B)"]
CF_TH_1_conclusions = ["B"]
CF_TH_1_settings = {
    'N': 4,                         # Max number of atomic propositions
    'contingent': False,            # Allow non-contingent propositions
    'non_null': False,              # Allow the null state
    'non_empty': False,             # Allow empty verifier/falsifier sets
    'disjoint': False,              # Allow verifier/falsifier overlap
    'max_time': 10,                 # Timeout in seconds
    'iterate': 1,                   # Number of models to find
    'expectation': False,           # True = expect countermodel, False = expect theorem
}
CF_TH_1_example = [
    CF_TH_1_premises,
    CF_TH_1_conclusions,
    CF_TH_1_settings,
]

# Example 3: Constitutive Identity Reflexivity
CON_TH_1_premises = []
CON_TH_1_conclusions = ["(A \\equiv A)"]
CON_TH_1_settings = {
    'N': 3,                         # Max number of atomic propositions
    'contingent': False,            # Allow non-contingent propositions
    'non_null': False,              # Allow the null state
    'non_empty': False,             # Allow empty verifier/falsifier sets
    'disjoint': False,              # Allow verifier/falsifier overlap
    'max_time': 10,                 # Timeout in seconds
    'iterate': 1,                   # Number of models to find
    'expectation': False,           # True = expect countermodel, False = expect theorem
}
CON_TH_1_example = [
    CON_TH_1_premises,
    CON_TH_1_conclusions,
    CON_TH_1_settings,
]

# Collection of all examples (used by test framework)
unit_tests = {
    "EXT_TH_1": EXT_TH_1_example,  # Modus ponens theorem
    "CF_TH_1": CF_TH_1_example,    # Counterfactual modus ponens
    "CON_TH_1": CON_TH_1_example,  # Identity reflexivity
}

# The framework expects this to be named 'example_range'
example_range = {
    "EXT_TH_1": EXT_TH_1_example,  # Run modus ponens example
    "CF_TH_1": CF_TH_1_example,    # Run counterfactual example
    # "CON_TH_1": CON_TH_1_example,  # Commented out to run fewer
}

# Optional: General settings for execution
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,  # Set to True to compare multiple theories
}

# Define semantic theories to use
semantic_theories = {
    "logos": theory,
}
```

Follow the [Examples Documentation](Docs/installation/GETTING_STARTED.md) to find our more about running `examples.py` files.

## Subdirectories

### [Code/](Code/)

Main implementation directory containing the ModelChecker package source code, development tools, and technical documentation. Includes the core framework, theory library implementations, builder system, iteration engine, and comprehensive test suites. This is where developers work on extending the framework and contributing new theories. See [Code/README.md](Code/README.md) for package documentation.

### [Docs/](Docs/)

Project-level documentation for understanding the ModelChecker's theoretical foundations, development methodology, and advanced usage. Contains guides for installation, development workflows, research methodology, and detailed explanations of the Z3-based implementation approach. Essential reading for researchers and contributors. See [Docs/README.md](Docs/README.md) for documentation navigation.

### [Images/](Images/)

Visual documentation including architecture diagrams, countermodel visualizations, and screenshots demonstrating the framework in action. Helps illustrate complex semantic concepts and usage patterns that are difficult to convey through text alone.

## Documentation

### For New Users

- **[Installation Guide](Docs/installation/README.md)** - Setup instructions for all platforms
- **[Getting Started Guide](Docs/installation/GETTING_STARTED.md)** - Create your first project
- **[User Guide](Code/src/model_checker/theory_lib/docs/USAGE_GUIDE.md)** - Basic usage patterns
- **[Interactive Notebooks](Code/src/model_checker/theory_lib/logos/notebooks/README.md)** - Hands-on tutorials

### For Researchers

- **[Methodology](Docs/methodology/README.md)** - Programmatic semantics approach
- **[Theory Library](Code/src/model_checker/theory_lib/README.md)** - Available semantic theories
- **[Hyperintensional Logic](Docs/theory/HYPERINTENSIONAL.md)** - Theoretical background

### For Developers

- **[Development Guide](Docs/DEVELOPMENT.md)** - Comprehensive development workflow
- **[Architecture Documentation](Docs/methodology/ARCHITECTURE.md)** - System design patterns
- **[Contributing Guidelines](Code/MAINTENANCE.md)** - Coding and documentation standards

## Key Features

### 1. Modular Semantic Theories

- **Hyperintensional Bilateral Semantics** (Logos): 19 operators across 5 subtheories
- **Unilateral Exclusion Semantics**: Solving the False Premise Problem
- **Fine's Counterfactual Semantics**: Imposition semantics for counterfactuals
- **Bimodal Logic**: Intensional semantics for reasoning with both tense and modal operators

### 2. Computational Tools

- **Z3 SMT Integration**: Automated model finding and constraint solving
- **Countermodel Visualization**: Understand why formulas fail
- **Model Iteration**: Find multiple distinct models satisfying constraints
- **Semantic Comparison**: Run multiple semantic theories on the same examples

### 3. Development Framework

- **Theory Templates**: Quickly create new semantic theories
- **Modular Architecture**: Compose operators with automatic dependencies
- **Comprehensive Testing**: Unit tests, integration tests, and example validation
- **Rich Documentation**: From API references to theoretical guides

## Theory Highlights

### Logos: Hyperintensional Truthmaker Semantics

- Distinguishes necessarily equivalent propositions
- Tracks what propositions are "about" through verifier/falsifier sets
- Supports modal, counterfactual, constitutive, and relevance reasoning

### Exclusion: Unilateral Semantics

- Implements Bernard & Champollion's exclusion operator
- First computational implementation of this complex semantics

### Imposition: Fine's Counterfactual Theory

- Evaluates counterfactuals via imposition
- Uses primitive imposition relation on states

### Bimodal: Temporal-Modal Logic

- Facilitates reasoning about time and possibility
- World histories as functions from times to world states

## Contributing

We welcome contributions! Please:

1. Follow the [Development Guide](Docs/DEVELOPMENT.md) for workflow
2. Use the standard `examples.py` structure for examples
3. Ensure all tests pass before submitting PRs
4. Include documentation for new features
5. Read [Code/MAINTENANCE.md](Code/MAINTENANCE.md) for standards

## Academic References

### Primary Sources

- Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8). _Journal of Philosophical Logic_.
- Brast-McKie, B. (2021). ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w). _Journal of Philosophical Logic_, 50, 1471-1503.
- Fine, K. (2012). ["Counterfactuals without Possible Worlds"](https://doi.org/10.1111/j.1467-9213.2012.00001.x). _Journal of Philosophy_, 109(3), 221-246.
- Fine, K. (2017). ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22). In _A Companion to the Philosophy of Language_ (2nd ed.). Wiley-Blackwell.
- Fine, K. (2017). ["A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation"](https://link.springer.com/article/10.1007/s10992-016-9413-y). _Journal of Philosophical Logic_, 46, 625-674.
- Fine, K. (2017). ["A Theory of Truthmaker Content II: Subject-matter, Common Content, Remainder and Ground"](https://link.springer.com/article/10.1007/s10992-016-9423-1). _Journal of Philosophical Logic_, 46, 675-702.

## License

This project is licensed under GPL-3.0. See [Code/LICENSE](Code/LICENSE) for details.

## Support

If you find ModelChecker useful, please consider starring the repository to help others discover it. To receive notifications about new releases:

1. Click "Watch" on the [GitHub repository](https://github.com/benbrastmckie/ModelChecker)
2. Select "Custom" → "Releases" to be notified only about new versions

We encourage users to report bugs and suggest features by [creating issues](https://github.com/benbrastmckie/ModelChecker/issues/new). When creating an issue, please:

- Check existing issues to avoid duplicates
- Provide minimal reproducible examples for bugs
- See [troubleshooting guide](Docs/installation/TROUBLESHOOTING.md) for common problems

- **Issues**: [GitHub Issues](https://github.com/benbrastmckie/ModelChecker/issues)
- **Contact**: See repository for contact information

---

[Code →](Code/README.md) | [Documentation →](Docs/README.md) | [Getting Started →](Docs/installation/GETTING_STARTED.md)
