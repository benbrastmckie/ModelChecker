# ModelChecker Jupyter Integration

This package provides a robust integration between the ModelChecker framework and Jupyter notebooks, enabling interactive exploration of logical models, formula validation, and visualization.

## Table of Contents

1. [Overview](#overview)
2. [Installation](#installation)
3. [Syntax Guidelines](#syntax-guidelines)
   - [Well-Formed Formulas](#well-formed-formulas)
   - [Operator Notation](#operator-notation)
   - [Escaping Characters](#escaping-characters)
4. [Basic Usage](#basic-usage)
   - [Simple Formula Checking](#simple-formula-checking)
   - [Working with Premises](#working-with-premises)
   - [Finding Countermodels](#finding-countermodels)
   - [Interactive Explorer](#interactive-explorer)
5. [Advanced Features](#advanced-features)
   - [Working with Different Theories](#working-with-different-theories)
   - [Custom Settings](#custom-settings)
   - [Unicode Operator Support](#unicode-operator-support)
   - [Loading Example Libraries](#loading-example-libraries)
   - [Visualization Options](#visualization-options)
6. [Component Reference](#component-reference)
   - [High-Level Functions](#high-level-functions)
   - [UI Components](#ui-components)
   - [Utility Functions](#utility-functions)
7. [Troubleshooting](#troubleshooting)
8. [Developer Notes](#developer-notes)

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

The Jupyter integration is included with the ModelChecker package. The simplest way to install it with all required dependencies is:

```bash
pip install model-checker[jupyter]
```

This installs the base package along with all Jupyter-related dependencies (ipywidgets, matplotlib, networkx, jupyter, etc.).

If you prefer manual installation or need to troubleshoot dependencies:

```bash
# Install base package
pip install model-checker

# Install Jupyter dependencies separately
pip install ipywidgets matplotlib networkx jupyter
```

### Development Installation

For developers working with the codebase:

```bash
# Clone the repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Install in development mode with jupyter extras
pip install -e .[jupyter]
```

### NixOS-Specific Installation

For NixOS users:
```bash
# From the ModelChecker/Code directory
nix-shell
./jupyter_link.py --launch
```
Alternatively, run which chains the command above together:
```
./run_jupyter.sh
```

For more information using Jupyter notebooks in NixOS, see [NixOS User Guide](NixOS_jupyter.md).

## Basic Usage

### Getting Started with Jupyter Notebooks

To use ModelChecker with Jupyter notebooks, follow these steps:

1. **Start Jupyter Notebook Server**

   After installing the package and dependencies, start Jupyter:

   ```bash
   jupyter notebook
   ```

   This will open your default web browser with the Jupyter interface.

2. **Create a New Notebook**

   - Click "New" → "Python 3" to create a new notebook
   - Or navigate to an existing notebook and open it

3. **Import and Use ModelChecker**

   In a notebook cell, import the ModelChecker components:

   ```python
   # Import core components
   from model_checker.jupyter import check_formula, ModelExplorer
   ```

   Now you're ready to use the ModelChecker features in your notebook!

## Syntax Guidelines

When writing logical formulas in the ModelChecker, it's important to follow specific syntax rules to ensure proper parsing and evaluation.

### Well-Formed Formulas

A well-formed formula in the ModelChecker must be one of the following:

1. **Atomic Sentence**: 
   - A single letter or continuous string of alphanumeric characters (e.g., `p`, `q`, `prop1`)
   - Examples: `A`, `p`, `sentence1`

2. **Unary Operation**:
   - A unary operator followed by a formula
   - Format: `\\unary_operator formula`
   - Examples: `\\neg p`, `\\Box q`, `\\Diamond (p \\wedge q)`

3. **Binary Operation**:
   - Two formulas connected by a binary operator and wrapped in parentheses
   - Format: `(formula1 \\binary_operator formula2)`
   - Examples: `(p \\wedge q)`, `(p \\vee (q \\rightarrow r))`
   - **Note**: Outer parentheses are mandatory for binary operations

### Operator Notation

All operators must be prefixed with double backslashes (`\\`) to escape them properly. The most common operators include:

| Operator     | Notation      | Description     |
|--------------|---------------|-----------------|
| Negation     | `\\neg`       | Not             |
| Conjunction  | `\\wedge`     | And             |
| Disjunction  | `\\vee`       | Or              |
| Implication  | `\\rightarrow`| If-then         |
| Equivalence  | `\\leftrightarrow`| If and only if |
| Necessity    | `\\Box`       | Modal necessity |
| Possibility  | `\\Diamond`   | Modal possibility|
| Tautology    | `\\top`       | Always true     |
| Contradiction| `\\bot`       | Always false    |

### Escaping Characters

The requirement for double backslashes is due to how Python handles escape characters in strings. This is a common source of confusion when writing logical formulas.

**Problem**: In a Python string, a single backslash (`\`) is an escape character. For example, `\n` is interpreted as a newline, not the literal characters `\` and `n`.

**Solution**: To represent an actual backslash in a Python string, you need to escape it with another backslash. Therefore, to get a single `\` in the output, you need to write `\\` in your string.

**Examples**:
- To represent `\wedge` in a Python string, you must write `\\wedge`
- Incorrect: `"p \wedge q"` (Python will try to interpret `\w` as an escape sequence)
- Correct: `"p \\wedge q"` (Python will interpret this as `p \wedge q`)

**Alternative Approaches**:
1. **Raw strings**: Using Python raw strings with `r"..."` notation: `r"\wedge"`. However, for consistency and clarity, we recommend using double backslashes throughout the codebase.

2. **Unicode symbols**: For better readability, the ModelChecker supports Unicode symbols as alternatives to LaTeX notation (see [Unicode Operator Support](#unicode-operator-support)).

**Convention**: Throughout the ModelChecker, we consistently use double backslashes in operator notation to ensure clarity and prevent escaping issues.

## Running Example Notebooks

ModelChecker comes with pre-built example notebooks:

```bash
# Navigate to the examples directory
cd /path/to/model-checker/site-packages/model_checker/jupyter/notebooks

# Or if you've cloned the repository
cd ModelChecker/Code/src/model_checker/jupyter/notebooks

# Start Jupyter in that directory
jupyter notebook
```

Then open `basic_demo.ipynb` or `options_demo.ipynb` to see demonstrations of the package's features.

### Simple Formula Checking

The most basic use case is checking if a formula is valid:

```python
from model_checker.jupyter import check_formula

# Check a simple formula
result = check_formula("p → (q → p)")
```

This will display an HTML output showing whether the formula is valid and details about the model.

### Working with Premises

You can check logical consequences by providing premises:

```python
from model_checker.jupyter import check_formula

# Check if premises entail a conclusion
check_formula("q", premises=["p", "p → q"])
```

### Finding Countermodels

To specifically look for countermodels to an invalid formula:

```python
from model_checker.jupyter import find_countermodel

# Find a countermodel where p doesn't imply q
countermodel = find_countermodel("p → q")
```

### Interactive Explorer

For interactive exploration, use the `ModelExplorer`:

```python
from model_checker.jupyter import ModelExplorer

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
from model_checker.jupyter import check_formula

# Check a formula in the default theory
check_formula("□(p → q) → (□p → □q)", theory_name="default")

# Check a formula in the exclusion theory (if available)
check_formula(r"\exclude (P \uniwedge Q)", theory_name="exclusion")
```

### Custom Settings

You can customize the model checking settings:

```python
from model_checker.jupyter import check_formula

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

The integration supports both LaTeX and Unicode notations for operators for better readability in notebooks. However, it's important to understand that **Unicode characters are automatically converted to LaTeX notation** internally before being passed to the model checker.

```python
from model_checker.jupyter import check_formula
from model_checker.jupyter.unicode import unicode_to_latex, latex_to_unicode

# Using Unicode operators for better readability in notebooks
check_formula("□p → p")  # Modal necessity
check_formula("p ∧ q")   # Conjunction
check_formula("p ∨ q")   # Disjunction
check_formula("¬p")      # Negation
check_formula("p → q")   # Implication

# Convert between notations
latex = unicode_to_latex("p → (q ∧ ¬r)")  # Converts to "p \\rightarrow (q \\wedge \\neg r)"
unicode = latex_to_unicode("\\Box p \\rightarrow p")  # Converts to "□p → p"
```

#### Unicode to LaTeX Conversion

The system automatically normalizes formulas, converting Unicode operators to their LaTeX counterparts with double backslashes. This is necessary because the internal model checker only understands LaTeX notation.

| Unicode | LaTeX Equivalent | Description |
|---------|------------------|-------------|
| →       | `\\rightarrow`   | Implication |
| ∧       | `\\wedge`        | Conjunction |
| ∨       | `\\vee`          | Disjunction |
| ¬       | `\\neg`          | Negation    |
| □       | `\\Box`          | Necessity   |
| ◇       | `\\Diamond`      | Possibility |
| ↔       | `\\leftrightarrow`| Equivalence |
| ≡       | `\\equiv`        | Equivalence |
| ⊥       | `\\bot`          | False       |
| ⊤       | `\\top`          | True        |

#### Theory-Specific Unicode Operators

Some theories like the exclusion theory have specialized operators with Unicode representations:

| Unicode | LaTeX Equivalent | Description |
|---------|------------------|-------------|
| ⦻       | `\\exclude`      | Exclusion   |
| ⊓       | `\\uniwedge`     | Unilateral conjunction |
| ⊔       | `\\univee`       | Unilateral disjunction |
| ≔       | `\\uniequiv`     | Unilateral equivalence |

#### Important Notes on Unicode Usage

1. **Internal Conversion**: All Unicode operators are automatically converted to LaTeX notation before processing.
2. **Display Only**: Unicode is primarily for display and readability in notebooks.
3. **Formula Normalization**: When setting formulas in the ModelExplorer or FormulaChecker, the system calls `normalize_formula()` which handles conversion.
4. **Custom Operators**: If you define custom operators, they must have LaTeX notation with double backslashes and optionally Unicode equivalents.
5. **Error Prevention**: Using Unicode ensures proper escaping, avoiding common errors with backslash escaping in strings.

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
  
  ```python
  from model_checker.jupyter import check_formula
  check_formula("p → q", premises=["p"])
  ```

- **`find_countermodel(formula, theory_name="default", premises=None, settings=None)`**  
  Searches for a countermodel to a formula.
  
  ```python
  from model_checker.jupyter import find_countermodel
  find_countermodel("p → q")
  ```

- **`explore_formula(formula, theory_name="default", premises=None, settings=None)`**  
  Creates a pre-configured interactive explorer for a formula.
  
  ```python
  from model_checker.jupyter import explore_formula
  explore_formula("p → (q → p)")
  ```

### UI Components

- **`ModelExplorer(theory_name="default")`**  
  Full-featured interactive UI for exploring models.
  
  ```python
  from model_checker.jupyter import ModelExplorer
  explorer = ModelExplorer()
  explorer.display()
  ```
  
  Methods:
  - `display()`: Show the explorer UI
  - `set_formula(formula)`: Set the formula to check
  - `set_premises(premises)`: Set the premises
  - `update_settings(settings)`: Update model settings
  - `check_formula()`: Check the current formula
  - `find_next_model()`: Find an alternative model

- **`FormulaChecker(theory_name="default")`**  
  Simplified UI just for checking formulas.
  
  ```python
  from model_checker.jupyter import FormulaChecker
  checker = FormulaChecker()
  checker.display()
  ```
  
  Methods:
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
   If you see errors about missing modules or import errors for `ModelExplorer`:
   ```bash
   # Install the missing dependencies
   pip install model-checker[jupyter]
   
   # Or install dependencies individually
   pip install ipywidgets matplotlib networkx jupyter
   ```

2. **Import Errors**  
   If you encounter import errors like "cannot import name 'ModelExplorer'", make sure:
   - You're importing from the correct module: `from model_checker.jupyter import ModelExplorer`
   - You have all required dependencies installed
   
   If still having issues, try setting up the environment manually:
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

2. **Unicode Operator Mappings**  
   Extend Unicode operator mappings in `unicode.py` for theory-specific operators.

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
- `unicode.py`: Unicode operator handling and LaTeX conversions
- `utils.py`: Shared utilities

For further development guidance, see the implementation strategy in `notes/jupyter.md`.
