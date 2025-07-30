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

## Quick Start

### Create a New Theory Project

```bash
# Create a project from a theory template
model-checker -l logos
model-checker -l exclusion
model-checker -l imposition
model-checker -l bimodal
```

### Using the Standard Examples.py Workflow

```python
# Create reflexivity_example.py
import os
import sys

current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

from model_checker.theory_lib.logos import get_theory

# Define examples
reflexivity_example = [
    [],                              # No premises
    ["(A \\rightarrow A)"],          # Reflexivity theorem
    {'N': 3, 'expectation': False}   # Expect validity
]

t_axiom_example = [
    ["\\Box A"],                     # Premise: A is necessary
    ["A"],                           # Conclusion: A is true
    {'N': 3, 'expectation': False}   # Expect validity
]

# Collections
test_example_range = {
    "reflexivity": reflexivity_example,
    "t_axiom": t_axiom_example,
}

semantic_theories = {
    "logos": get_theory(),
}

# Run with: model-checker reflexivity_example.py
```

### Interactive Exploration (Jupyter)

```python
from model_checker import ModelExplorer
explorer = ModelExplorer()
explorer.display()  # Launch interactive widget
```

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

```python
# Complete workflow example
from model_checker import get_theory, BuildExample

# 1. Load a theory
theory = get_theory("logos")

# 2. Build a model with premises and conclusions
# Define example with premises and conclusions
modus_ponens_example = [
    ["A", "(A \\rightarrow B)"],      # Premises
    ["B"],                           # Conclusions
    {'N': 3, 'expectation': False}   # Settings (expect validity)
]

# 3. Set up collections
test_example_range = {
    "modus_ponens": modus_ponens_example,
}

semantic_theories = {
    "logos": theory,
}

# 4. Run with: model-checker modus_ponens.py
# Results show validity or countermodel automatically
```

### Extension Points

The framework is designed for extension in several ways:

- **New Theories**: Add theory directories to `theory_lib/` with standardized interfaces
- **New Operators**: Subclass `Operator` or `DefinedOperator` within theories
- **New Builders**: Extend `BuildExample` for specialized model construction
- **Custom Settings**: Define theory-specific settings following the relevance principle

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
dne_example = [
    [],                                  # No premises
    ["(\\neg \\neg A \\rightarrow A)"],      # Double negation elimination
    {'N': 3}                             # Settings
]

# Set up for all theories
test_example_range = {
    "double_negation": dne_example,
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
- **[Architecture Documentation](../ARCHITECTURE.md)** - System design and implementation
- **[Contributing Guidelines](theory_lib/README.md#contributing)** - Adding new theories and features

## Advanced Features

### Model Iteration

Find multiple distinct models for comprehensive analysis:

```python
# Find multiple models: iteration_example.py
from model_checker.theory_lib.logos import get_theory

# Example that allows multiple models
contingent_example = [
    [],                              # No premises
    ["(A \\vee \\neg A)"],           # Tautology with multiple models
    {
        'N': 3,
        'iterate': 5,                # Find up to 5 models
        'expectation': False         # Expect validity
    }
]

test_example_range = {
    "contingent": contingent_example,
}

semantic_theories = {
    "logos": get_theory(),
}

# Run with: model-checker iteration_example.py
# Outputs multiple distinct models
```

### Custom Settings

Configure theory-specific behavior:

```python
# Custom settings in examples.py
custom_example = [
    ["\\Box A"],
    ["A"],
    {
        'N': 8,                    # Larger state space
        'contingent': True,        # Require contingent propositions
        'iterate': 3,              # Find 3 models
        'max_time': 10000          # 10-second timeout
    }
]

test_example_range = {
    "custom_settings": custom_example,
}
```

### Jupyter Integration

Interactive exploration in notebooks:

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
- Fine, K. (2017) ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22), Wiley-Blackwell
- Brast-McKie, B. (2021) ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w), Journal of Philosophical Logic

### Implementation Papers
- See individual theory documentation for comprehensive references:
  - [Logos Theory References](theory_lib/logos/README.md#references)
  - [Exclusion Theory References](theory_lib/exclusion/README.md#references) 
  - [Imposition Theory References](theory_lib/imposition/README.md#references)

## Related Resources

- **[Hyperintensional Semantics Guide](../../../Docs/HYPERINTENSIONAL.md)** - Comprehensive introduction to truthmaker frameworks
- **[Development Tools Documentation](../../../Docs/TOOLS.md)** - Advanced features and debugging
- **[Main Package Documentation](../README.md)** - Installation and package-level information

## License

Licensed under GPL-3.0. See individual theory directories for specific attribution and citation requirements.

---

[← Back to Root](../README.md) | [Theory Library →](theory_lib/README.md) | [Builder →](builder/README.md) | [Jupyter →](jupyter/README.md)