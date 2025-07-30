# ModelChecker

[License: GPL-3.0](https://img.shields.io/badge/License-GPL%203.0-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[Python 3.8+](https://img.shields.io/badge/python-3.8+-blue.svg)](https://www.python.org/downloads/)
[Z3 SMT Solver](https://img.shields.io/badge/Z3-SMT%20Solver-green.svg)](https://github.com/Z3Prover/z3)

A unified programmatic semantics framework for modal, counterfactual, and hyperintensional logic, powered by the Z3 SMT solver.

## Features

- **🔍 Automated Model Finding**: Discovers countermodels to invalid formulas automatically
- **🧩 Modular Theory Architecture**: Mix and match logical operators from different theories
- **🎯 Hyperintensional Reasoning**: Distinguishes necessarily equivalent propositions
- **🔄 Multiple Model Generation**: Find diverse models satisfying your constraints
- **📚 Rich Theory Library**: Pre-built theories for modal, counterfactual, and temporal logic

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

# Define logical arguments
modus_ponens = [
    ["A", "(A \\rightarrow B)"],  # Premises
    ["B"],                        # Conclusion
    {'N': 3}                      # Settings
]

test_example_range = {
    "modus_ponens": modus_ponens,
}

semantic_theories = {
    "logos": get_theory(),
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
example_with_iteration = [
    ["(A \\vee B)"],              # Premise
    ["C"],                        # Conclusion  
    {
        'N': 3,
        'iterate': 5,             # Find up to 5 models
        'expectation': True       # Expect countermodels
    }
]
```

### Theory Comparison

```python
from model_checker.theory_lib import logos, exclusion, imposition, bimodal

# Test the same principle across theories
double_negation = [
    [],
    ["(\\neg \\neg A \\rightarrow A)"],
    {'N': 3}
]

semantic_theories = {
    "logos": logos.get_theory(),
    "exclusion": exclusion.get_theory(),
    "imposition": imposition.get_theory(),
    "bimodal": bimodal.bimodal_theory,
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

TODO: 

If you use ModelChecker in your research, please cite:

- Brast-McKie, B. (2025). Model-Checker: A Unified Programmatic Semantics Framework. https://github.com/benbrastmckie/ModelChecker
- **Counterfactual Worlds**: [Journal of Philosophical Logic](https://link.springer.com/article/10.1007/s10992-025-09793-8)

## License

GPL-3.0 - see [LICENSE](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/LICENSE) for details.

## Support

- **Issues**: [GitHub Issues](https://github.com/benbrastmckie/ModelChecker/issues)
- **Discussions**: [GitHub Discussions](https://github.com/benbrastmckie/ModelChecker/discussions)
- **Documentation**: [Project Wiki](https://github.com/benbrastmckie/ModelChecker/wiki)
