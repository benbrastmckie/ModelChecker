# ModelChecker: Unified Programmatic Semantics Framework

[Code →](Code/README.md) | [Documentation →](Docs/README.md) | [Theory Library →](Code/src/model_checker/theory_lib/README.md)

## Directory Structure
```
ModelChecker/
├── README.md               # This file - project overview
├── Code/                   # Main implementation directory (see Code/README.md)
│   ├── src/               # Source code
│   ├── docs/              # Development documentation
│   ├── specs/             # Implementation specifications
│   └── tests/             # Test suites
├── Docs/                   # Project documentation (see Docs/README.md)
│   ├── DEVELOPMENT.md     # Development guide
│   ├── INSTALLATION.md    # Installation instructions
│   ├── METHODOLOGY.md     # Research methodology
│   └── TOOLS.md           # Advanced tooling
├── Images/                 # Screenshots and diagrams
├── Old/                    # Legacy code and documentation
└── TODO.md                # Project roadmap
```

## Overview

The **ModelChecker** provides a unified programmatic semantics framework for developing and exploring modular semantic theories. Drawing on the Z3 SMT solver, it enables researchers to establish logical consequence over finite models, automatically finding readable countermodels when formulas are invalid. The framework supports modal, counterfactual, and hyperintensional logic through a modular architecture that promotes transparent and verifiable reasoning.

The project implements a **programmatic approach to formal semantics**, where semantic theories are encoded as Python programs that generate Z3 constraints. This enables computational exploration of complex logical systems that would be intractable to analyze by hand. The framework includes a comprehensive theory library with implementations of hyperintensional truthmaker semantics (Logos), unilateral exclusion semantics, Fine's counterfactual semantics, and bimodal temporal-modal logic.

Key innovations include **bilateral evaluation** (tracking both verification and falsification conditions), **modular operator composition** with automatic dependency resolution, and **interactive exploration tools** for understanding semantic distinctions invisible to classical logic.

## Quick Start

### Create a New Theory Project

```bash
# Install the package
pip install model-checker

# Create a project from an existing theory
model-checker -l logos
model-checker -l exclusion
model-checker -l imposition
model-checker -l bimodal
```

### Run Examples

```bash
# Run a specific example file
model-checker examples/my_logic_examples.py

# Or use the development CLI (from source)
./Code/dev_cli.py examples/my_logic_examples.py
```

### Example Structure

Create `examples/my_logic_examples.py`:

```python
# Import theory components
from model_checker.theory_lib.logos import get_theory

# Load the theory
theory = get_theory()

# Define examples
modus_ponens_example = [
    ["A", "(A \\rightarrow B)"],  # Premises
    ["B"],                        # Conclusion
    {'N': 3}                      # Settings
]

# Collection for execution
test_example_range = {
    "modus_ponens": modus_ponens_example,
}

# Define semantic theories
semantic_theories = {
    "logos": theory,
}
```

## Subdirectories

### [Code/](Code/)
Main implementation directory containing the ModelChecker package source code, development tools, and technical documentation. Includes the core framework, theory library implementations, builder system, iteration engine, and comprehensive test suites. This is where developers work on extending the framework and contributing new theories. See [Code/README.md](Code/README.md) for package documentation.

### [Docs/](Docs/)
Project-level documentation for understanding the ModelChecker's theoretical foundations, development methodology, and advanced usage. Contains guides for installation, development workflows, research methodology, and detailed explanations of the Z3-based implementation approach. Essential reading for researchers and contributors. See [Docs/README.md](Docs/README.md) for documentation navigation.

### [Images/](Images/)
Visual documentation including architecture diagrams, countermodel visualizations, and screenshots demonstrating the framework in action. Helps illustrate complex semantic concepts and usage patterns that are difficult to convey through text alone.

### [Old/](Old/)
Archive of legacy implementations, early design documents, and historical meeting notes. Preserved for reference and understanding the project's evolution. Contains the original proposal, early semantic experiments, and iterations that led to the current architecture.

## Documentation

### For New Users
- **[Installation Guide](Docs/INSTALLATION.md)** - Getting started with ModelChecker
- **[User Guide](Code/src/model_checker/theory_lib/docs/USAGE_GUIDE.md)** - Basic usage patterns
- **[Interactive Notebooks](Code/src/model_checker/theory_lib/logos/notebooks/README.md)** - Hands-on tutorials

### For Researchers  
- **[Methodology](Docs/METHODOLOGY.md)** - Research approach and validation
- **[Theory Library](Code/src/model_checker/theory_lib/README.md)** - Available semantic theories
- **[Hyperintensional Logic](Docs/HYPERINTENSIONAL.md)** - Theoretical background

### For Developers
- **[Development Guide](Docs/DEVELOPMENT.md)** - Comprehensive development workflow
- **[Architecture Documentation](Code/docs/ARCHITECTURE.md)** - System design patterns
- **[Contributing Guidelines](Code/MAINTENANCE.md)** - Coding and documentation standards

## Key Features

### 1. Modular Semantic Theories
- **Hyperintensional Truthmaker Semantics** (Logos): 19 operators across 5 subtheories
- **Unilateral Exclusion Semantics**: Solving the False Premise Problem
- **Fine's Counterfactual Semantics**: Without possible worlds
- **Bimodal Temporal-Modal Logic**: Combined reasoning about time and possibility

### 2. Computational Tools
- **Z3 SMT Integration**: Automated model finding and constraint solving
- **Model Iteration**: Find multiple distinct models satisfying constraints
- **Interactive Exploration**: Jupyter widgets for real-time semantic exploration
- **Countermodel Visualization**: Understand why formulas fail

### 3. Development Framework
- **Theory Templates**: Quickly create new semantic theories
- **Modular Architecture**: Compose operators with automatic dependencies
- **Comprehensive Testing**: Unit tests, integration tests, and example validation
- **Rich Documentation**: From API references to theoretical guides

## Installation

### Basic Installation
```bash
pip install model-checker
```

### Development Installation
```bash
git clone https://github.com/benbrastmckie/ModelChecker
cd ModelChecker/Code
pip install -e .[dev]
```

### With Jupyter Support
```bash
pip install model-checker[jupyter]
```

For detailed installation instructions including platform-specific notes, see [Docs/INSTALLATION.md](Docs/INSTALLATION.md).

## Theory Highlights

### Logos: Hyperintensional Truthmaker Semantics
- Distinguishes necessarily equivalent propositions
- Tracks what propositions are "about" through verifier/falsifier sets
- Supports modal, counterfactual, constitutive, and relevance reasoning

### Exclusion: Unilateral Semantics
- Implements Bernard & Champollion's exclusion operator
- Solves the False Premise Problem through witness predicates
- First computational implementation of this complex semantics

### Imposition: Fine's Counterfactual Theory
- Evaluates counterfactuals without possible worlds
- Uses primitive imposition relation on states
- Implements Fine's five frame constraints

### Bimodal: Temporal-Modal Logic
- Combines reasoning about time and possibility
- World histories as sequences of states
- Supports past, future, and modal operators

## Contributing

We welcome contributions! Please:

1. Read [Code/MAINTENANCE.md](Code/MAINTENANCE.md) for coding standards
2. Follow the [Development Guide](Docs/DEVELOPMENT.md) for workflow
3. Ensure all tests pass before submitting PRs
4. Include documentation for new features
5. Use the standard `examples.py` structure for examples

## Academic References

### Primary Sources
- Fine, K. (2012). "Counterfactuals without Possible Worlds"
- Fine, K. (2017). "Truthmaker Semantics"
- Bernard, T. & Champollion, L. (2024). "Unilateral Semantics"

### Framework Documentation
- Brastmckie, B. [Hyperintensional Semantics](http://www.benbrastmckie.com/research#access)
- ModelChecker [Counterfactual Logic Paper](https://link.springer.com/article/10.1007/s10992-025-09793-8)

## License

This project is licensed under GPL-3.0. See [Code/LICENSE](Code/LICENSE) for details.

## Support

- **Issues**: [GitHub Issues](https://github.com/benbrastmckie/ModelChecker/issues)
- **Documentation**: [Project Wiki](https://github.com/benbrastmckie/ModelChecker/wiki)
- **Contact**: See repository for contact information

---

[Code →](Code/README.md) | [Documentation →](Docs/README.md) | [Getting Started →](Docs/INSTALLATION.md)