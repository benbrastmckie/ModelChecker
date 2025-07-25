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

```python
from model_checker import BuildExample, get_theory, check_formula

# Basic formula checking
result = check_formula("p \\rightarrow p")  # Test reflexivity
print(f"Reflexivity: {'valid' if result else 'invalid'}")

# Theory-specific checking
theory = get_theory("logos")
model = BuildExample("modal_test", theory)
result = model.check_formula("\\Box p \\rightarrow p")  # T axiom
print(f"T axiom in logos: {'valid' if result else 'invalid'}")

# Interactive exploration
from model_checker import ModelExplorer
explorer = ModelExplorer()
explorer.display()  # Launch interactive widget in Jupyter
```

## Files in This Directory

### __init__.py
Main API exports providing convenient access to core functionality. Contains the primary functions `check_formula()`, `get_theory()`, `BuildExample`, and imports from major modules. This is the primary entry point for most ModelChecker usage.

### __main__.py
Command-line interface and entry points for the development CLI. Handles argument parsing, dispatch to appropriate modules, and integration with development workflow tools. Supports theory testing, example running, and project generation.

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

1. **User Interface Layer**: `BuildExample`, `check_formula()`, Jupyter widgets
2. **Coordination Layer**: Model construction, constraint generation, result processing  
3. **Theory Implementation Layer**: Semantic classes, operators, and constraint definitions

### API Flow

The typical API usage follows these steps:

1. **Theory Selection**: Get a theory via `get_theory("theory_name")`
2. **Model Building**: Create a model with `BuildExample("name", theory)`
3. **Formula Evaluation**: Check formulas using `model.check_formula()`
4. **Result Analysis**: Analyze validity and examine countermodels

```python
# Complete workflow example
from model_checker import get_theory, BuildExample

# 1. Load a theory
theory = get_theory("logos")

# 2. Build a model with premises and conclusions
model = BuildExample("modus_ponens", theory)
model.add_premises(["p", "p \\rightarrow q"])
model.add_conclusions(["q"])

# 3. Check validity
valid = model.check_validity()

# 4. Analyze results
if valid:
    print("Argument is valid")
else:
    print("Found countermodel:")
    model.print_countermodel()
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
# Compare logical principles across theories
from model_checker import get_theory, BuildExample

formula = "\\neg \\neg p \\rightarrow p"  # Double negation elimination
theories = ["logos", "exclusion", "imposition", "bimodal"]

print("Double negation elimination:")
for name in theories:
    theory = get_theory(name)
    model = BuildExample("dne_test", theory)
    result = model.check_formula(formula)
    print(f"  {name}: {'valid' if result else 'invalid'}")
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
from model_checker import BuildExample

# Find multiple models for the same formula
model = BuildExample("iteration_test", theory, settings={'iterate': 5})
models = model.find_models()

for i, m in enumerate(models):
    print(f"Model {i+1}: {m.get_model_summary()}")
```

### Custom Settings

Configure theory-specific behavior:

```python
# Logos theory with custom settings
settings = {
    'N': 8,                    # Larger state space
    'contingent': True,        # Require contingent propositions
    'iterate': 3,              # Find 3 models
    'max_time': 10000          # 10-second timeout
}

model = BuildExample("custom", theory, settings=settings)
```

### Jupyter Integration

Interactive exploration in notebooks:

```python
# High-level functions
from model_checker.jupyter import check_formula, find_countermodel

result = check_formula("\\Box (p \\rightarrow q) \\rightarrow (\\Box p \\rightarrow \\Box q)")
countermodel = find_countermodel("\\Box p \\rightarrow p", theory="logos")

# Interactive widgets
from model_checker import ModelExplorer
explorer = ModelExplorer(theory="exclusion")
explorer.display()
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