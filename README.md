# ModelChecker: Unified Programmatic Semantics Framework

[Code →](Code/README.md) | [Documentation →](Docs/README.md) | [Theory Library →](Code/src/model_checker/theory_lib/README.md)

## Overview

The **ModelChecker** provides a programmatic framework for developing and exploring modular semantic theories. Built on the SMT solver Z3, it enables researchers to establish logical consequence over finite models, automatically generating readable countermodels when formulas or inferences are invalid.

This [talk](https://www.youtube.com/watch?v=ZqTpdJKHT_4) at the [Topos Institute](https://topos.institute/) provides an overview of the project.

## Installation

### Basic Installation

```bash
pip install model-checker
```

### With Jupyter Support

```bash
pip install model-checker[jupyter]
```

For Jupyter notebook features and interactive exploration, see the [Jupyter Integration Guide](Code/src/model_checker/jupyter/README.md).

### Development Installation

```bash
git clone https://github.com/benbrastmckie/ModelChecker
cd ModelChecker/Code
# Use the development CLI to run locally without installation:
./dev_cli.py examples/my_example.py
```

For comprehensive development setup instructions, including virtual environments and platform-specific guidance, see the [Development Guide](Code/docs/DEVELOPMENT.md). NixOS users can use the provided `shell.nix` configuration for automatic environment setup.

### Installation Guides

For comprehensive installation instructions including platform-specific guides, virtual environments, and troubleshooting, see the [Installation Documentation](Docs/installation/README.md).

**Quick Links:**
- [Basic Installation](Docs/installation/BASIC_INSTALLATION.md) - Further details
- [NixOS Installation](Docs/installation/BASIC_INSTALLATION.md#nixos-installation) - NixOS-specific setup
- [Developer Setup](Docs/installation/DEVELOPER_SETUP.md) - Development environment
- [Troubleshooting](Docs/installation/TROUBLESHOOTING.md) - Common issues

## Quick Start

### 1. Create a Project

```bash
# Create a copy of the logos semantics (default)
model-checker

# Or load a specific theory
model-checker -l logos        # Hyperintensional semantics with all subtheories
model-checker -l exclusion    # Unilateral exclusion semantics
model-checker -l imposition   # Fine's counterfactual semantics
model-checker -l bimodal      # Bimodal logic for tense and circumstantial modalities

# Load specific logos subtheories
model-checker -l logos --subtheory counterfactual  # Just counterfactual + dependencies
```

This creates a project directory with `examples.py`, `semantic.py`, `operators.py`, and supporting files.

### 2. Run Examples

```bash
# Run the examples file created in your project
model-checker examples.py

# Compare multiple theories
model-checker examples.py --maximize

# Save results in various formats
model-checker examples.py --save           # All formats
model-checker examples.py --save json      # JSON only
```

### 3. Next Steps

- **New to ModelChecker?** Follow the [Getting Started Guide](Docs/installation/GETTING_STARTED.md)
- **Ready to develop?** See [The ModelChecker Methodology](#the-modelchecker-methodology) below
- **Need examples?** Check the [Examples Guide](Docs/usage/EXAMPLES.md) and [example structure](Docs/installation/GETTING_STARTED.md#example-structure)

## The ModelChecker Methodology

The ModelChecker provides a systematic methodology for developing and studying semantic theories. This section provides an overview of the workflow. For the complete methodology guide, see [Docs/usage/WORKFLOW.md](Docs/usage/WORKFLOW.md).

### 1. Create Your Theory Project

Start by creating a new project or loading an existing theory:

```bash
# Create a copy of the logos semantics
model-checker                                        # Creates a logos semantics by default with all subtheories

# Load an existing theory as starting point
model-checker -l logos --subtheory counterfactual    # Just counterfactual + dependencies
model-checker -l exclusion                           # Unilateral exclusion semantics
model-checker -l imposition                          # Fine's counterfactual semantics
model-checker -l bimodal                             # Bimodal logic for tense and circumstantial modalities
```

This creates a complete project directory with `examples.py`, `semantic.py`, `operators.py`, and supporting files. See [Project Creation Guide](Docs/usage/PROJECT.md) for detailed instructions.

### 2. Develop Examples

Edit the `examples.py` file to test logical inferences relevant to your theory:

```bash
# Run your examples
model-checker examples.py
```

Define a range of examples in order to evaluate their behavior in your theory. See the [Examples Guide](Docs/usage/EXAMPLES.md) and [Settings Guide](Docs/usage/SETTINGS.md) for details.

### 3. Adapt Semantic Framework

Modify `semantic.py` to implement your specific semantic theory. Add new constraints, modify existing ones, or create entirely new semantic frameworks to capture the logical principles that distinguish your theory. See the [Semantics Guide](Docs/usage/SEMANTICS.md).

### 4. Define Custom Operators

Extend your theory's expressive power with new operators:

- **Defined operators** in `operators.py` - shortcuts for combinations of existing operators
- **Primitive operators** requiring semantic interpretation in `semantic.py`

See the [Operators Guide](Docs/usage/OPERATORS.md) for implementation patterns.

### 5. Iterate Models and Compare Theories

Explore the space of models your theory allows and systematically compare with alternative approaches:

```bash
# Test single theory
model-checker examples.py

# Compare multiple theories
model-checker examples.py --maximize
```

See the [Tools Guide](Docs/usage/TOOLS.md) for model iteration and theory comparison.

### 6. Save and Export Results

Export your findings in formats suitable for analysis or publication:

```bash
model-checker examples.py --save           # All formats (json, markdown, jupyter)
model-checker examples.py --save json      # Machine-readable JSON
model-checker examples.py --save markdown  # Human-readable markdown
```

See the [Output Guide](Docs/usage/OUTPUT.md) for format options.

### Complete Methodology

This systematic approach enables you to:
1. **Start** with working theories as foundations
2. **Test** logical inferences computationally
3. **Customize** semantic behavior through constraints
4. **Extend** expressive power with new operators
5. **Explore** the space of possible models
6. **Compare** different theoretical approaches
7. **Document** and share your findings

For the complete step-by-step methodology with detailed examples and advanced techniques, see the [full Methodology Guide](Docs/usage/WORKFLOW.md).

## Project Structure

```
ModelChecker/
├── Code/                           # Main implementation directory
│   ├── src/                        # Source code
│   ├── docs/                       # Technical documentation
│   ├── scripts/                    # Development and maintenance scripts
│   └── tests/                      # Test suites
├── Docs/                           # General project documentation
│   ├── installation/               # Installation guides
│   ├── usage/                      # Practical usage guides
│   │   ├── PROJECT.md              # Project creation
│   │   ├── EXAMPLES.md             # Writing examples
│   │   ├── SETTINGS.md             # Configuration settings
│   │   ├── SEMANTICS.md            # Semantic constraints
│   │   ├── OPERATORS.md            # Defining operators
│   │   ├── TOOLS.md                # Advanced tools
│   │   ├── OUTPUT.md               # Saving results
│   │   └── WORKFLOW.md             # Complete methodology
│   ├── architecture/               # System architecture
│   ├── maintenance/                # Development standards
│   └── theory/                     # Theoretical background
├── Images/                         # Screenshots and diagrams
└── README.md                       # This file
```

### Main Directories

**[Code/](Code/)** - Main implementation directory containing the ModelChecker package source code, development tools, and technical documentation. Includes the core framework, theory library implementations, builder system, iteration engine, and comprehensive test suites. This is where developers work on extending the framework and contributing new theories. See [Code/README.md](Code/README.md) for package documentation.

**[Docs/](Docs/)** - Project-level documentation for understanding the ModelChecker's theoretical foundations, development architecture, and advanced usage. Contains guides for installation, development workflows, research architecture, and detailed explanations of the Z3-based implementation approach. Essential reading for researchers and contributors. See [Docs/README.md](Docs/README.md) for documentation navigation.

**[Images/](Images/)** - Visual documentation including architecture diagrams, countermodel visualizations, and screenshots demonstrating the framework in action. Helps illustrate complex semantic concepts and usage patterns that are difficult to convey through text alone.

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

- 19 operators across 5 modular subtheories
- Sensitive to differences in subject-matter via verifier/falsifier sets
- Distinguishes necessarily equivalent propositions
- Supports modal, counterfactual, constitutive, and relevance reasoning

### Exclusion: Unilateral Semantics

- Implements Bernard & Champollion's exclusion operator in a unilateral semantic
- Uses witness predicates for proper negation handling

### Imposition: Fine's Counterfactual Theory

- Evaluates counterfactuals via imposition
- Uses primitive imposition relation on states

### Bimodal: Temporal-Modal Logic

- Facilitates reasoning about time and possibility
- World histories as functions from times to world states
- Includes past, future, and modal operators


## Contributing

We welcome contributions! Please:

1. Follow the [Development Guide](Docs/DEVELOPMENT.md) for workflow
2. Use the standard `examples.py` structure for examples
3. Ensure all tests pass before submitting PRs
4. Include documentation for new features
5. Read [Code/MAINTENANCE.md](Code/MAINTENANCE.md) for standards

## Academic References

### Primary Sources

- Brast-McKie, B. (draft). ["The Construction of Possible Worlds"](http://www.benbrastmckie.com/wp-content/uploads/2025/11/possible_worlds.pdf).
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
