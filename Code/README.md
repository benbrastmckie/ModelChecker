# ModelChecker

[← Back to Project](../README.md) | [General Docs →](../Docs/README.md) | [Technical Docs →](docs/README.md)

[![License: GPL-3.0](https://img.shields.io/badge/License-GPL%203.0-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![Python 3.8+](https://img.shields.io/badge/python-3.8+-blue.svg)](https://www.python.org/downloads/)
[![Z3 SMT Solver](https://img.shields.io/badge/Z3-SMT%20Solver-green.svg)](https://github.com/Z3Prover/z3)

A unified programmatic semantics framework for modal, counterfactual, and hyperintensional logic, powered by the Z3 SMT solver.

## Features

- **Automated Model Finding**: Discovers countermodels to invalid formulas automatically
- **Modular Theory Architecture**: Mix and match logical operators from different theories
- **Hyperintensional Reasoning**: Distinguishes necessarily equivalent propositions
- **Multiple Model Generation**: Find diverse models satisfying your constraints
- **Rich Theory Library**: Pre-built theories for modal, counterfactual, and temporal logic

## Installation

```bash
pip install model-checker
```

For Jupyter notebook support:

```bash
pip install model-checker[jupyter]
```

## Quick Start

Create a new logic project:

```bash
model-checker -l logos     # Hyperintensional logic
model-checker -l exclusion # Unilateral semantics
model-checker -l imposition # Fine's counterfactuals
model-checker -l bimodal   # Temporal-modal logic
```

Check logical validity:

```python
# Create example.py
from model_checker.theory_lib.logos import get_theory

# Load the theory
theory = get_theory()

# Define logical arguments following the naming convention
EXT_TH_1_premises = ["A", "(A \\rightarrow B)"]
EXT_TH_1_conclusions = ["B"]
EXT_TH_1_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}
EXT_TH_1_example = [
    EXT_TH_1_premises,
    EXT_TH_1_conclusions,
    EXT_TH_1_settings,
]

# Collection of all examples (used by test framework)
unit_tests = {
    "EXT_TH_1": EXT_TH_1_example,  # Modus ponens theorem
    # Add more examples here for comprehensive testing
}

# The framework expects this to be named 'example_range'
example_range = {
    "EXT_TH_1": EXT_TH_1_example,  # Run this specific example
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

# Run: model-checker example.py
```

## Available Theories

### Logos: Hyperintensional Truthmaker Semantics

- 19 operators across 5 modular subtheories
- Tracks what propositions are "about" via verifier/falsifier sets
- Distinguishes necessarily equivalent but distinct propositions

### Exclusion: Unilateral Semantics

- Solves the False Premise Problem
- First computational implementation of Bernard & Champollion's semantics
- Uses witness predicates for proper negation handling

### Imposition: Fine's Counterfactual Semantics

- Evaluates counterfactuals without possible worlds
- Based on primitive imposition relation between states
- Implements Fine's five frame constraints

### Bimodal: Temporal-Modal Logic

- Combines reasoning about time and possibility
- World histories as sequences of states
- Past, future, and modal operators

## Advanced Usage

### Find Multiple Models

```python
# In your examples.py file
CF_CM_1_premises = ["(A \\vee B)"]
CF_CM_1_conclusions = ["C"]
CF_CM_1_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': True,        # All propositions must be contingent
    'non_null': True,          # Exclude the null state
    'non_empty': True,         # Require non-empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 5,              # Find up to 5 distinct models
    'expectation': True,       # True = expect countermodel, False = expect theorem
}
CF_CM_1_example = [
    CF_CM_1_premises,
    CF_CM_1_conclusions,
    CF_CM_1_settings,
]

# Collection for testing
unit_tests = {
    "CF_CM_1": CF_CM_1_example,  # Multiple countermodel example
    # Add more examples here
}

example_range = {
    "CF_CM_1": CF_CM_1_example,  # Will find multiple countermodels
}

# Optional: General settings for execution
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,  # Set to True to compare multiple theories
}

semantic_theories = {
    "logos": logos.get_theory(),  # Or appropriate theory
}
```

### Theory Comparison

```python
from model_checker.theory_lib import logos, exclusion, imposition, bimodal

# Test double negation elimination across theories
DNE_TH_1_premises = ["\\neg \\neg A"]
DNE_TH_1_conclusions = ["A"]
DNE_TH_1_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}
DNE_TH_1_example = [
    DNE_TH_1_premises,
    DNE_TH_1_conclusions,
    DNE_TH_1_settings,
]

# Collection of all examples
unit_tests = {
    "DNE_TH_1": DNE_TH_1_example,  # Double negation elimination
    # Could add more cross-theory tests here
}

# Example range with the test
example_range = {
    "DNE_TH_1": DNE_TH_1_example,  # Double negation elimination
}

# Optional: General settings for execution
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,  # Set to True to compare multiple theories
}

# Define multiple theories for comparison
semantic_theories = {
    "logos": logos.get_theory(),
    "exclusion": exclusion.get_theory(),
    "imposition": imposition.get_theory(),
}
```

## Documentation

- **[GitHub Repository](https://github.com/benbrastmckie/ModelChecker)** - Full documentation and source code
- **[Development Guide](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/DEVELOPMENT.md)** - Contributing and development workflow
- **[Theory Documentation](https://github.com/benbrastmckie/ModelChecker/tree/master/Code/src/model_checker/theory_lib)** - Detailed theory specifications
- **[Academic Background](http://www.benbrastmckie.com/research#access)** - Theoretical foundations

## Contributing

We welcome contributions! See our [GitHub repository](https://github.com/benbrastmckie/ModelChecker) for:

- Contributing guidelines
- Development setup instructions
- Issue tracking
- Pull request procedures

## Academic Citations

If you use ModelChecker in your research, please cite:

- Brast-McKie, B. (2025). Model-Checker: A Programmatic Semantics Framework. [https://github.com/benbrastmckie/ModelChecker](https://github.com/benbrastmckie/ModelChecker)
- Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8), Journal of Philosophical Logic

## License

GPL-3.0 - see [LICENSE](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/LICENSE) for details.

## Support

- **Issues**: [GitHub Issues](https://github.com/benbrastmckie/ModelChecker/issues)
- **Discussions**: [GitHub Discussions](https://github.com/benbrastmckie/ModelChecker/discussions)
- **Documentation**: [Project Wiki](https://github.com/benbrastmckie/ModelChecker/wiki)

---

[← Back to Project](../README.md) | [General Docs →](../Docs/README.md) | [Technical Docs →](docs/README.md)
