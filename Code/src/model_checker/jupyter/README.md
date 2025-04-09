# ModelChecker Jupyter Integration

This package provides a robust integration between the ModelChecker framework and Jupyter notebooks, enabling interactive exploration of logical models, formula validation, and visualization.

## Table of Contents

1. [Overview](#overview)
2. [Installation](#installation)
3. [Basic Usage](#basic-usage)
   - [Simple Formula Checking](#simple-formula-checking)
   - [Working with Premises](#working-with-premises)
   - [Finding Countermodels](#finding-countermodels)
   - [Interactive Explorer](#interactive-explorer)
4. [Advanced Features](#advanced-features)
   - [Working with Different Theories](#working-with-different-theories)
   - [Custom Settings](#custom-settings)
   - [Unicode Operator Support](#unicode-operator-support)
   - [Loading Example Libraries](#loading-example-libraries)
   - [Visualization Options](#visualization-options)
5. [Component Reference](#component-reference)
   - [High-Level Functions](#high-level-functions)
   - [UI Components](#ui-components)
   - [Utility Functions](#utility-functions)
6. [Troubleshooting](#troubleshooting)
7. [Developer Notes](#developer-notes)

## Overview

The ModelChecker Jupyter integration provides a set of tools for working with logical theories, models, and formulas in Jupyter notebooks. The integration offers both high-level functions for quick checks and interactive components for deeper exploration.

Key features:
- Formula checking with premises and theories
- Interactive model exploration with customizable settings
- Support for Unicode and LaTeX formula notation
- Visualizations of logical models
- Access to pre-defined examples from theories
- Theory-specific adapters for consistent interfaces

## Installation

The Jupyter integration is included with the ModelChecker package. To use it, you need to install ModelChecker and the required dependencies for Jupyter integration:

```bash
pip install model-checker
pip install ipywidgets matplotlib networkx
```

For NixOS users:
```bash
# From the ModelChecker/Code directory
nix-shell
cd src
python -m pip install -e .
```

For more information using Jupyter notebooks in NixOS, see [NixOS User Guide](NixOS_jupyter.md).

## Basic Usage

### Simple Formula Checking

The most basic use case is checking if a formula is valid:

```python
from model_checker import check_formula

# Check a simple formula
result = check_formula("p → (q → p)")
```

This will display an HTML output showing whether the formula is valid and details about the model.

### Working with Premises

You can check logical consequences by providing premises:

```python
from model_checker import check_formula

# Check if premises entail a conclusion
check_formula("q", premises=["p", "p → q"])
```

### Finding Countermodels

To specifically look for countermodels to an invalid formula:

```python
from model_checker import find_countermodel

# Find a countermodel where p doesn't imply q
countermodel = find_countermodel("p → q")
```

### Interactive Explorer

For interactive exploration, use the `ModelExplorer`:

```python
from model_checker import ModelExplorer

# Create and display an interactive explorer
explorer = ModelExplorer()
explorer.display()
```

The explorer provides a UI with:
- Formula input field
- Premises input area
- Theory selector
- Settings panel
- Visualization options
- Buttons for checking formulas and finding alternative models

## Advanced Features

### Working with Different Theories

ModelChecker supports multiple semantic theories. You can specify which theory to use:

```python
from model_checker import check_formula

# Check a formula in the default theory
check_formula("□(p → q) → (□p → □q)", theory_name="default")

# Check a formula in the exclusion theory (if available)
check_formula(r"\exclude (P \uniwedge Q)", theory_name="exclusion")
```

### Custom Settings

You can customize the model checking settings:

```python
from model_checker import check_formula

# Custom settings
settings = {
    'N': 4,               # Number of atomic propositions
    'max_time': 10,       # Maximum time for solving (seconds)
    'contingent': True,   # Require contingent valuations
    'non_empty': True,    # Require non-empty verifiers
    'expectation': False  # Expect formula to be invalid
}

check_formula("p ∨ q ∨ r ∨ s", settings=settings)
```

### Unicode Operator Support

The integration supports both LaTeX and Unicode notations for operators:

```python
from model_checker import check_formula
from model_checker.jupyter.operators import unicode_to_latex, latex_to_unicode

# Using Unicode operators
check_formula("□p → p")  # Modal necessity
check_formula("p ∧ q")   # Conjunction
check_formula("p ∨ q")   # Disjunction
check_formula("¬p")      # Negation
check_formula("p → q")   # Implication

# Convert between notations
latex = unicode_to_latex("p → (q ∧ ¬r)")
unicode = latex_to_unicode("\\Box p \\rightarrow p")
```

### Loading Example Libraries

Access pre-defined examples from theories:

```python
from model_checker.jupyter.utils import load_examples, get_example_categories

# Load examples from a theory
examples = load_examples("default")

# Group examples by category
categories = get_example_categories(examples)

# Use an example
example = examples["example_name"]
premises, conclusions, settings = example
```

### Visualization Options

Models can be visualized as text or graphs:

```python
from model_checker import ModelExplorer

explorer = ModelExplorer()
explorer.display()

# Switch to graph visualization in the UI by selecting "Graph Visualization"
```

## Component Reference

### High-Level Functions

- **`check_formula(formula, theory_name="default", premises=None, settings=None)`**  
  Checks if a formula is valid, optionally with premises and in a specific theory.

- **`find_countermodel(formula, theory_name="default", premises=None, settings=None)`**  
  Searches for a countermodel to a formula.

- **`explore_formula(formula, theory_name="default", premises=None, settings=None)`**  
  Creates a pre-configured interactive explorer for a formula.

### UI Components

- **`ModelExplorer(theory_name="default")`**  
  Full-featured interactive UI for exploring models.
  - `display()`: Show the explorer UI
  - `set_formula(formula)`: Set the formula to check
  - `set_premises(premises)`: Set the premises
  - `update_settings(settings)`: Update model settings
  - `check_formula()`: Check the current formula
  - `find_next_model()`: Find an alternative model

- **`FormulaChecker(theory_name="default")`**  
  Simplified UI just for checking formulas.
  - `display()`: Show the checker UI
  - `set_formula(formula)`: Set the formula to check
  - `set_premises(premises)`: Set the premises
  - `check_formula()`: Check the current formula

### Utility Functions

- **`unicode_to_latex(formula)`**: Converts Unicode operators to LaTeX syntax
- **`latex_to_unicode(formula)`**: Converts LaTeX operators to Unicode symbols
- **`load_examples(theory_name, example_prefix=None)`**: Loads examples from a theory
- **`get_example_categories(examples)`**: Categorizes examples by type
- **`setup_environment()`**: Ensures the Python environment is correctly configured
- **`get_available_theories()`**: Returns a list of available semantic theories
- **`get_diagnostic_info()`**: Returns diagnostic information about the environment

## Troubleshooting

### Common Issues

1. **Missing Dependencies**  
   If you see errors about missing modules, install the required dependencies:
   ```bash
   pip install ipywidgets matplotlib networkx
   ```

2. **Import Errors**  
   If you encounter import errors, try setting up the environment manually:
   ```python
   from model_checker.jupyter.environment import manually_setup_paths
   manually_setup_paths("/path/to/ModelChecker/Code")
   ```

3. **Theory Not Found**  
   If a theory is not found, check available theories:
   ```python
   from model_checker.jupyter.environment import get_available_theories
   print(get_available_theories())
   ```

4. **Visualization Issues**  
   If graph visualization doesn't work, ensure matplotlib and networkx are installed and fall back to text visualization.

5. **Performance Issues**  
   For large models or complex formulas, increase the `max_time` setting or reduce the `N` value.

### Diagnostic Information

You can get diagnostic information about your environment:

```python
from model_checker.jupyter.environment import get_diagnostic_info
print(get_diagnostic_info())
```

## Developer Notes

The Jupyter integration is designed to be extensible, particularly for supporting new semantic theories. The key extension points are:

1. **Theory Adapters**  
   Add new adapters in `adapters.py` for custom theory visualizations.

2. **Operator Mappings**  
   Extend operator mappings in `operators.py` for theory-specific operators.

3. **UI Customization**  
   The UI components in `interactive.py` can be extended for custom interfaces.

4. **Visualization**  
   Custom visualizations can be added in `display.py`.

The architecture follows a modular design with clean separation of concerns:
- `__init__.py`: Public API
- `adapters.py`: Theory-specific adapters
- `display.py`: Visualization utilities
- `environment.py`: Environment setup
- `interactive.py`: UI components
- `operators.py`: Operator handling
- `utils.py`: Shared utilities

For further development guidance, see the implementation strategy in `notes/jupyter.md`.
