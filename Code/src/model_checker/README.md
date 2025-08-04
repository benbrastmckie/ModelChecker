# ModelChecker API: Programmatic Semantic Framework

[← Back to Root](../README.md) | [Theory Library →](theory_lib/README.md) | [Development →](../../docs/DEVELOPMENT.md)

## Directory Structure

```
model_checker/
├── README.md               # This file - API documentation and architecture
├── __init__.py            # Main API exports and convenience functions
├── __main__.py             # Command-line interface and entry points
├── builder/                # Model construction and example builders (see builder/README.md)
├── iterate/                # Model iteration and constraint generation (see iterate/README.md)
├── jupyter/                # Interactive notebook integration (see jupyter/README.md)
├── settings/               # Centralized settings management (see settings/README.md)
├── theory_lib/             # Semantic theory implementations (see theory_lib/README.md)
└── utils/                  # Utility functions and helper modules
```

## Overview

The **ModelChecker API** provides a programmatic semantic framework for implementing and comparing logical theories, with a focus on modal, counterfactual, and hyperintensional logic. The framework enables automated verification of logical arguments, discovery of countermodels, and systematic comparison between different semantic approaches.

The API follows a **modular architecture** that separates core functionality from theory-specific implementations, allowing researchers to implement new semantic theories while leveraging shared constraint-solving infrastructure. The framework supports **4 semantic theories** with over 25 logical operators across different theoretical approaches.

This implementation enables computational logic research by providing **Z3-based constraint solving**, **interactive Jupyter integration**, and **systematic testing frameworks** for validating logical principles and discovering countermodels across different semantic theories.

## Subdirectories

### [builder/](builder/)

Model construction and example builders providing the `BuildExample` and `BuildModule` classes. Handles theory loading, constraint generation coordination, and result formatting. This is the primary interface between user code and the constraint-solving engine. See [builder/README.md](builder/README.md) for construction patterns.

### [iterate/](iterate/)

Model iteration and constraint generation for finding multiple distinct models. Implements sophisticated difference constraints to ensure model diversity and provides theory-specific iteration strategies. Essential for comprehensive countermodel analysis. See [iterate/README.md](iterate/README.md) for iteration techniques.

### [jupyter/](jupyter/)

Interactive notebook integration providing high-level functions and interactive widgets for logical exploration. Features formula checking, countermodel visualization, and theory comparison tools optimized for research and educational use. See [jupyter/README.md](jupyter/README.md) for interactive features.

### [settings/](settings/)

Centralized settings management system with theory-specific defaults, validation, and command-line flag integration. Implements the relevance principle where theories only define settings applicable to their semantics. See [settings/README.md](settings/README.md) for configuration details.

### [theory_lib/](theory_lib/)

Collection of semantic theory implementations including logos (hyperintensional), exclusion (unilateral), imposition (Fine's counterfactuals), and bimodal (temporal-modal) theories. Each theory follows standardized interfaces while preserving unique semantic characteristics. See [theory_lib/README.md](theory_lib/README.md) for theory details.

## API Architecture

### Core Components

The ModelChecker framework follows a **three-layer architecture**:

1. **User Interface Layer**: `BuildExample`, `BuildModule`, Jupyter widgets
2. **Coordination Layer**: Model construction, constraint generation, result processing
3. **Theory Implementation Layer**: Semantic classes, operators, and constraint definitions

### API Flow

The typical API usage follows these steps:

1. **Theory Selection**: Get a theory via `get_theory("theory_name")`
2. **Model Building**: Create a model with `BuildExample("name", theory)`
3. **Formula Evaluation**: Run the model to check validity
4. **Result Analysis**: Analyze validity and examine countermodels

### Using the Standard `examples.py` Workflow

```python
# Create example.py
import os
import sys

current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

from model_checker.theory_lib.logos import get_theory

# Load the theory
theory = get_theory()

# Define examples following the naming convention
LOG_TH_1_premises = []
LOG_TH_1_conclusions = ["(A \\rightarrow A)"]
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

# Organize examples by category
countermodel_examples = {
    # Add countermodel examples here
}

theorem_examples = {
    "LOG_TH_1": LOG_TH_1_example,  # Reflexivity theorem
    "MOD_TH_1": MOD_TH_1_example,  # T-axiom theorem
}

# Combine for unit_tests (used by test framework)
unit_tests = {**countermodel_examples, **theorem_examples}

# The framework expects this to be named 'example_range'
example_range = {
    "LOG_TH_1": LOG_TH_1_example,  # Run reflexivity example
    "MOD_TH_1": MOD_TH_1_example,  # Run T-axiom example
}
# Or run all tests: example_range = unit_tests

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

# Run with: model-checker example.py
```

## Creating a New Theory Project

```bash
# Create a project from a theory template
model-checker -l logos
model-checker -l exclusion
model-checker -l imposition
model-checker -l bimodal
```

## Theory Integration

### Available Theories

The framework includes **4 semantic theories**:

- **Logos**: Hyperintensional truthmaker semantics with 20+ operators across 5 subtheories
- **Exclusion**: Unilateral semantics with witness-based negation (4 operators)
- **Imposition**: Fine's state-based counterfactuals (2 specialized operators)
- **Bimodal**: Temporal-modal reasoning with world histories (4 operators)

### Theory Comparison

```python
# Compare logical principles across theories: dne_comparison.py
from model_checker.theory_lib import logos, exclusion, imposition, bimodal

# Test double negation elimination
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

# Set up collections for all theories
countermodel_examples = {
    # Add countermodel examples here
}

theorem_examples = {
    "DNE_TH_1": DNE_TH_1_example,  # Double negation elimination
}

# Combine for unit_tests (used by test framework)
unit_tests = {**countermodel_examples, **theorem_examples}

example_range = {
    "DNE_TH_1": DNE_TH_1_example,  # Run this test
}

# Optional: General settings for execution
general_settings = {
    "print_constraints": False,
    "print_impossible": False,
    "print_z3": False,
    "save_output": False,
    "maximize": False,  # Set to True to compare multiple theories
}

# Load all theories
semantic_theories = {
    "logos": logos.get_theory(),
    "exclusion": exclusion.get_theory(),
    "imposition": imposition.get_theory(),
    "bimodal": bimodal.bimodal_theory,
}

# Run with: model-checker dne_comparison.py
# Output shows which theories validate the principle
```

### Theory-Specific Features

Each theory provides:

- **Standardized Interface**: `get_theory()`, `get_examples()`, `get_test_examples()`
- **Custom Settings**: Only relevant settings for the semantic framework
- **Operator Collections**: Theory-appropriate logical operators
- **Example Libraries**: Validation examples and test cases

## Documentation

### For New Users

- **[Getting Started Guide](../README.md#quick-start)** - Basic usage and installation
- **[Theory Selection Guide](theory_lib/README.md#theory-selection-guide)** - Choosing appropriate theories
- **[Jupyter Integration](jupyter/README.md)** - Interactive exploration and learning

### For Researchers

- **[Theory Library](theory_lib/README.md)** - Comprehensive theory documentation and references
- **[Advanced Features](../../../Docs/TOOLS.md)** - Model iteration, theory comparison, debugging
- **[Academic References](theory_lib/README.md#references)** - Theoretical foundations and citations

### For Developers

- **[Development Guide](../../docs/DEVELOPMENT.md)** - Framework development and testing
- **[Architecture Documentation](../../../Docs/methodology/ARCHITECTURE.md)** - System design and implementation
- **[Contributing Guidelines](theory_lib/README.md#contributing)** - Adding new theories and features

### Jupyter Integration

Interactive exploration in notebooks (see [jupyter/README.md](jupyter/README.md) for comprehensive documentation):

```python
# Interactive widgets for exploration
from model_checker import ModelExplorer

# Create an interactive explorer
explorer = ModelExplorer(theory="exclusion")
explorer.display()

# Or work with BuildExample directly
from model_checker import get_theory, BuildExample

theory = get_theory("logos")
model = BuildExample("interactive_test", theory)
model.premises = ["p", "(p \\rightarrow q)"]
model.conclusions = ["q"]
result = model.run_single_test()
```

## Testing and Validation

The API includes comprehensive testing infrastructure:

```bash
# Test API components
python test_package.py --components builder iterate jupyter settings

# Test theory implementations
python test_theories.py --theories logos exclusion imposition bimodal

# Test specific functionality
python test_package.py --components utils --verbose
```

## References

### Framework Documentation

- See individual theory documentation for comprehensive references:
  - [Logos Theory References](theory_lib/logos/README.md#references)
  - [Exclusion Theory References](theory_lib/exclusion/README.md#references)
  - [Imposition Theory References](theory_lib/imposition/README.md#references)

## Related Resources

- **[Hyperintensional Semantics Guide](../../../Docs/theory/HYPERINTENSIONAL.md)** - Comprehensive introduction to truthmaker frameworks
- **[Development Tools Documentation](../../../Docs/TOOLS.md)** - Advanced features and debugging
- **[Main Package Documentation](../README.md)** - Installation and package-level information

## License

Licensed under GPL-3.0. See individual theory directories for specific attribution and citation requirements.

---

[← Back to Root](../README.md) | [Theory Library →](theory_lib/README.md) | [Builder →](builder/README.md) | [Jupyter →](jupyter/README.md)
