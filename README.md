# ModelChecker: Unified Programmatic Semantics Framework

[Code →](Code/README.md) | [Documentation →](Docs/README.md) | [Theory Library →](Code/src/model_checker/theory_lib/README.md)

## Overview

The **ModelChecker** provides a programmatic framework for developing and exploring modular semantic theories. Built on the SMT solver Z3, it enables researchers to establish logical consequence over finite models, automatically generating readable countermodels when formulas or inferences are invalid.

## Quick Start Workflow

### 1. Create or Load a Theory Project

Start by creating a new project from an existing theory or from scratch:

```bash
# Load an existing theory
model-checker -l logos       # Hyperintensional semantics
model-checker -l exclusion   # Unilateral exclusion semantics
model-checker -l imposition  # Fine's counterfactual semantics
model-checker -l bimodal     # Temporal-modal logic

# Or create a blank project
model-checker
```

See [Project Creation Guide](Docs/usage/PROJECT.md) for detailed instructions on starting new projects.

### 2. Test and Develop Examples

Each project includes an `examples.py` file where you define logical formulas to test:

```bash
# Run your examples
model-checker examples.py
```

Modify `examples.py` to test different inferences and adjust settings like model size and constraints. See the [Examples Guide](Docs/usage/EXAMPLES.md) and [Settings Guide](Docs/usage/SETTINGS.md) for details.

### 3. Customize Semantic Constraints

Modify `semantic.py` to change how your theory evaluates formulas. Add new constraints, modify existing ones, or create entirely new semantic frameworks. See the [Constraints Guide](Docs/usage/CONSTRAINTS.md).

### 4. Define New Operators

Extend your theory with custom operators:

- **Defined operators** in `operators.py` - built from existing operators
- **Primitive operators** in `semantic.py` - implemented with Z3 constraints

See the [Operators Guide](Docs/usage/OPERATORS.md) for implementation details.

### 5. Compare Theories and Iterate Models

Use advanced tools to explore your semantics:

- Compare multiple theories on the same examples
- Find all models satisfying given constraints
- Generate countermodels systematically

See the [Tools Guide](Docs/usage/TOOLS.md) for these capabilities.

### 6. Save and Export Results

Save your findings in various formats:

- Text files with countermodels
- LaTeX for publications
- JSON for further processing

See the [Output Guide](Docs/usage/OUTPUT.md) for export options.

## Directory Structure

```
ModelChecker/
├── Code/                           # Main implementation directory
│   ├── src/                        # Source code
│   ├── docs/                       # Technical documentation
│   ├── specs/                      # Implementation specifications
│   └── tests/                      # Test suites
├── Docs/                           # General project documentation
│   ├── installation/               # Installation guides
│   ├── usage/                      # Practical usage guides
│   │   ├── PROJECT.md              # Project creation
│   │   ├── EXAMPLES.md             # Writing examples
│   │   ├── SETTINGS.md             # Configuration settings
│   │   ├── CONSTRAINTS.md          # Semantic constraints
│   │   ├── OPERATORS.md            # Defining operators
│   │   ├── TOOLS.md                # Advanced tools
│   │   └── OUTPUT.md               # Saving results
│   ├── architecture/               # System architecture
│   └── theory/                     # Theoretical background
├── Images/                         # Screenshots and diagrams
└── README.md                       # This file
```

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

Project-level documentation for understanding the ModelChecker's theoretical foundations, development architecture, and advanced usage. Contains guides for installation, development workflows, research architecture, and detailed explanations of the Z3-based implementation approach. Essential reading for researchers and contributors. See [Docs/README.md](Docs/README.md) for documentation navigation.

### [Images/](Images/)

Visual documentation including architecture diagrams, countermodel visualizations, and screenshots demonstrating the framework in action. Helps illustrate complex semantic concepts and usage patterns that are difficult to convey through text alone.

## Documentation

### For New Users

- **[Installation Guide](Docs/installation/README.md)** - Setup instructions for all platforms
- **[Getting Started Guide](Docs/installation/GETTING_STARTED.md)** - Create your first project
- **[User Guide](Code/src/model_checker/theory_lib/docs/USAGE_GUIDE.md)** - Basic usage patterns
- **[Interactive Notebooks](Code/src/model_checker/theory_lib/logos/notebooks/README.md)** - Hands-on tutorials

### For Researchers

- **[Architecture](Docs/architecture/README.md)** - Programmatic semantics approach
- **[Theory Library](Code/src/model_checker/theory_lib/README.md)** - Available semantic theories
- **[Hyperintensional Logic](Docs/theory/HYPERINTENSIONAL.md)** - Theoretical background

### For Developers

- **[Development Guide](Docs/DEVELOPMENT.md)** - Comprehensive development workflow
- **[Architecture Documentation](Docs/architecture/ARCHITECTURE.md)** - System design patterns
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
