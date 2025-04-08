# ModelChecker Jupyter Integration

This document explains how to use ModelChecker in Jupyter notebooks using the interactive explorer and visualization features.

## Installation

To use ModelChecker in Jupyter notebooks, install the package with the optional dependencies:

```bash
pip install model-checker[notebook]
```

Or install the dependencies manually:

```bash
pip install ipywidgets matplotlib networkx
```

## Quick Start

### Basic Formula Checking

For simple formula checks:

```python
from model_checker.notebook import check_formula

# Check a simple formula
check_formula("p → (q → p)")

# Check a modal formula
check_formula("□(p → q) → (□p → □q)")

# Check with premises
check_formula("q", premises=["p", "p → q"])
```

### Interactive Explorer

For interactive exploration:

```python
from model_checker.notebook import InteractiveModelExplorer

# Create and display the explorer
explorer = InteractiveModelExplorer()
explorer.display()
```

## Features

### Interactive UI Components

The interactive explorer includes:

- Formula input field with syntax highlighting
- Premises textarea for multiple premise input
- Theory selector to choose between semantic theories
- Settings panel with sliders and checkboxes
- Buttons for formula checking and finding alternative models
- Visualization options (text or graph)

### Visualization Options

Two visualization modes are available:

1. **Text Output**: Shows the complete model details with ANSI colors converted to HTML
2. **Graph Visualization**: Displays a graphical representation of the model structure

### Model Settings

Customize the model with settings:

- **N**: Number of atomic propositions (1-10)
- **Max Time**: Maximum solver time in seconds
- **Contingent**: Use contingent valuations
- **Non-Empty**: Ensure non-empty valuations
- **Print Constraints**: Show Z3 constraints

### Multiple Models

Find and explore alternative models for the same formula using the "Find Next Model" button.

## Advanced Usage

### Working with Different Theories

Check the same formula in different theories:

```python
check_formula("□p → p", theory_name="default")
check_formula("□p → p", theory_name="exclusion")
```

### Custom Settings

Provide custom settings for formula checking:

```python
custom_settings = {
    'N': 4,
    'max_time': 10,
    'contingent': True,
    'non_empty': True,
}

check_formula("p ∨ q ∨ r ∨ s", settings=custom_settings)
```

### Programmatic Access to Results

Get the HTML output for further processing:

```python
explorer = InteractiveModelExplorer()
explorer.formula_input.value = "p ∧ q"
explorer.check_button.click()

html_output = explorer.get_output()
```

## Example Notebook

See the included `jupyter_demo.ipynb` notebook for a complete demonstration of all features.

## Troubleshooting

If you encounter issues:

1. **ImportError**: Ensure all dependencies are installed
2. **Display issues**: Check that Jupyter has the ipywidgets extension enabled
3. **Long-running models**: Increase the max_time setting
4. **Memory errors**: Reduce the number of propositions (N setting)

## Tutorial Resources

For more information on modal logic and the theories implemented in ModelChecker, see:

- [ModelChecker Documentation](https://github.com/benbrastmckie/ModelChecker)
- Theory-specific READMEs in the ModelChecker source code
