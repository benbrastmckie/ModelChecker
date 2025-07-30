# Theory Library: Semantic Theory Collection

[← Back to ModelChecker API](../README.md) | [Usage Guide →](docs/USAGE_GUIDE.md) | [Contributing →](docs/CONTRIBUTING.md)

## Directory Structure

```
theory_lib/
├── README.md               # This file - theory library overview
├── __init__.py            # Theory registration and loading functions
├── docs/                  # Documentation hub (see docs/README.md)
│   ├── README.md          # Documentation navigation guide
│   ├── USAGE_GUIDE.md     # Practical usage patterns and examples
│   ├── CONTRIBUTING.md    # Theory implementation and contribution guide
│   └── THEORY_ARCHITECTURE.md # Architecture patterns and design principles
├── tests/                 # Infrastructure tests (see tests/README.md)
├── logos/                 # Hyperintensional semantics (see logos/README.md)
├── exclusion/             # Unilateral semantics (see exclusion/README.md)
├── imposition/            # Fine's counterfactual semantics (see imposition/README.md)
└── bimodal/               # Temporal-modal logic (see bimodal/README.md)
```

## Overview

The **Theory Library** provides a collection of computational semantic theories implemented using Z3 constraint solving, enabling automated verification of logical arguments and discovery of countermodels across different semantic frameworks.

The library supports **4 semantic theories** with over 25 logical operators, following a **modular architecture** that allows comparison between theories, extension with new implementations, and standardized testing procedures.

Each theory implements common interface patterns while preserving unique semantic characteristics, enabling researchers to explore different approaches to modal, counterfactual, and hyperintensional logic within a unified computational framework.

## Quick Start

### Create a New Theory Project

```bash
# Load a theory template
model-checker -l logos
model-checker -l exclusion
model-checker -l imposition
model-checker -l bimodal
```

### Run Examples

```bash
# Run a specific example file
model-checker examples/my_logic_examples.py

# Or use dev_cli.py for development
./dev_cli.py examples/my_logic_examples.py
```

### Example Structure

Create `examples/my_logic_examples.py`:

```python
# Standard imports
import os
import sys

# Add current directory to path for imports
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

# Import theory components
from model_checker.theory_lib import logos

# Option 1: Load complete theory (all subtheories)
full_theory = logos.get_theory()

# Option 2: Load specific subtheories for focused analysis
# Modal logic only (includes extensional as dependency)
modal_theory = logos.get_theory(['modal'])

# Counterfactual reasoning (includes extensional)
counterfactual_theory = logos.get_theory(['counterfactual'])

# Multiple subtheories
constitutive_theory = logos.get_theory(['modal', 'constitutive'])

# Define examples following naming convention
LOG_TH_1_premises = []
LOG_TH_1_conclusions = ["(\\neg \\neg A \\rightarrow A)"]
LOG_TH_1_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}
LOG_TH_1_example = [
    LOG_TH_1_premises,
    LOG_TH_1_conclusions,
    LOG_TH_1_settings,
]

MOD_TH_1_premises = ["\\Box A"]
MOD_TH_1_conclusions = ["A"]
MOD_TH_1_settings = {
    'N': 3,                    # Max number of atomic propositions
    'contingent': False,       # Allow non-contingent propositions
    'non_null': False,         # Allow the null state
    'non_empty': False,        # Allow empty verifier/falsifier sets
    'disjoint': False,         # Allow verifier/falsifier overlap
    'max_time': 10,            # Timeout in seconds
    'iterate': 1,              # Number of models to find
    'expectation': False,      # True = expect countermodel, False = expect theorem
}
MOD_TH_1_example = [
    MOD_TH_1_premises,
    MOD_TH_1_conclusions,
    MOD_TH_1_settings,
]

# Collection of all examples (used by test framework)
unit_tests = {
    "LOG_TH_1": LOG_TH_1_example,  # Double negation elimination
    "MOD_TH_1": MOD_TH_1_example,  # T-axiom theorem
}

# The framework expects this to be named 'example_range'
example_range = {
    "LOG_TH_1": LOG_TH_1_example,  # Run specific examples
    "MOD_TH_1": MOD_TH_1_example,
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
# Can use full theory or selective subtheory loading
semantic_theories = {
    "modal_only": modal_theory,           # Just modal operators
    "full_logos": full_theory,            # All operators
    # "counterfactual": counterfactual_theory,  # Uncomment to add
}

# Make module executable
if __name__ == '__main__':
    import subprocess
    file_name = os.path.basename(__file__)
    subprocess.run(["model-checker", file_name], check=True, cwd=current_dir)
```

### Selective Subtheory Benefits

The Logos theory's modular architecture allows loading only the operators you need:

- **Performance**: Smaller constraint space for faster solving
- **Focus**: Test specific logical systems without interference
- **Dependencies**: Automatic resolution (e.g., modal requires extensional)
- **Flexibility**: Mix and match operators for custom logical systems

## Available Theories

### Architecture Patterns

The ModelChecker supports two primary theory architectures optimized for different semantic complexity levels:

**Simple Pattern** (focused theories): Single-file operator implementations for theories with cohesive operator sets
**Modular Pattern** (complex theories): Subtheory organization for theories with large, categorizable operator collections

### Logos Theory (Modular Pattern)

**Hyperintensional bilateral semantics** with 20+ operators across 5 subtheories

- **Author**: Benjamin Brast-McKie
- **Implementation**: Benjamin Brast-McKie, Miguel Buitrago
- **Architecture**: Modular (5 subtheories: extensional, modal, constitutive, counterfactual, relevance)
- **Key Features**: Truthmaker semantics, selective subtheory loading, comprehensive operator coverage
- **Papers**: 
  - Brast-McKie, B. (2021). ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w). _Journal of Philosophical Logic_, 50, 1471-1503.
  - Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8). _Journal of Philosophical Logic_.
- **Usage**: `logos.get_theory(['extensional', 'modal'])` for selective loading

More information: [logos/README.md](logos/README.md) | [Interactive Notebooks](logos/notebooks/README.md)

### Exclusion Theory (Simple Pattern)

**Unilateral semantics** with witness-based exclusion operations

- **Authors**: Lucas Champollion & Paul Bernard
- **Implementation**: Benjamin Brast-McKie, Miguel Buitrago
- **Architecture**: Simple (4 operators in unified implementation)
- **Key Features**: Witness predicates, exclusion-based negation, architectural innovations
- **Paper**: Champollion, L., & Bernard, P. (2024). ["Negation and Modality in Unilateral Truthmaker Semantics"](https://doi.org/10.1007/s10988-023-09407-z). _Linguistics and Philosophy_.
- **Significance**: Complete computational realization of unilateral semantics

More information: [exclusion/README.md](exclusion/README.md) | [Interactive Notebooks](exclusion/notebooks/README.md)

### Imposition Theory

**Fine's truthmaker semantics** for counterfactual reasoning

- **Author**: Kit Fine
- **Implementation**: Benjamin Brast-McKie
- **Key Features**: Imposition operator, could operator, distinctive counterfactual approach
- **Papers**:
  - Fine, K. (2012). ["Counterfactuals without Possible Worlds"](https://doi.org/10.5840/jphil2012109312). _Journal of Philosophy_, 109(3), 221-246.
  - Fine, K. (2012). ["A Difficulty for the Possible Worlds Analysis of Counterfactuals"](https://www.jstor.org/stable/41485149). _Synthese_, 189(1), 29-57.
- **Focus**: Alternative approach to counterfactual semantics through truthmaker framework

More information: [imposition/README.md](imposition/README.md) | [Interactive Notebooks](imposition/notebooks/README.md)

### Bimodal Theory

**Temporal-modal interaction** with world history semantics

- **Author**: Benjamin Brast-McKie
- **Implementation**: Benjamin Brast-McKie
- **Key Features**: Tense and circumstantial modality interaction, world history semantics
- **Focus**: Complex interactions between temporal and modal operators
- **Applications**: Temporal logic with modal embedding

More information: [bimodal/README.md](bimodal/README.md) | [Documentation](bimodal/docs/README.md)

## Subdirectories

### [docs/](docs/README.md)

Comprehensive documentation hub with **usage guides**, **architecture documentation**, **contribution guidelines**, and **implementation patterns**. Organized for different user types from beginners implementing their first theory to researchers comparing semantic approaches.

### [tests/](tests/README.md)

Infrastructure testing suite covering **theory discovery**, **metadata management**, **cross-theory compatibility**, and **common functionality**. Complements theory-specific tests with framework-level validation.

### Individual Theory Directories

Each theory directory contains **complete implementations** with semantic classes, operators, examples, comprehensive documentation, test suites, and interactive Jupyter notebooks for hands-on exploration.

## Documentation

### For New Users

- **[Usage Guide](docs/USAGE_GUIDE.md)** - Import strategies, basic examples, and configuration patterns
- **[Individual Theory READMEs](logos/README.md)** - Theory-specific documentation and quick start guides
- **[Interactive Notebooks](logos/notebooks/README.md)** - Hands-on tutorials and explorations

### For Researchers

- **[Theory Architecture Guide](docs/THEORY_ARCHITECTURE.md)** - Simple vs Modular patterns and design principles
- **[Comparison Examples](docs/USAGE_GUIDE.md#comparing-theories)** - Cross-theory analysis and formula testing
- **[Academic References](#references)** - Primary literature and theoretical foundations

### For Developers

- **[Contributing Guide](docs/CONTRIBUTING.md)** - Complete implementation workflow and requirements
- **[Testing Framework](tests/README.md#theory-testing-framework-guide)** - Comprehensive testing patterns
- **[API Integration](../README.md)** - Framework-level interfaces and coordination
- **[Examples Standard](../../docs/EXAMPLES.md)** - Standard form for examples.py files

## References

### Implementation Documentation

- Theory library implements 4 semantic theories with standardized interfaces and modular architecture
- Cross-theory comparison enabled through unified constraint-solving infrastructure

### Related Resources

- **[ModelChecker API](../README.md)** - Core framework documentation and 3-layer architecture
- **[Builder Package](../builder/README.md)** - Model construction and theory coordination
- **[Settings Management](../settings/README.md)** - Configuration system and theory-specific parameters

---

[← Back to ModelChecker API](../README.md) | [Usage Guide →](docs/USAGE_GUIDE.md) | [Contributing →](docs/CONTRIBUTING.md)
