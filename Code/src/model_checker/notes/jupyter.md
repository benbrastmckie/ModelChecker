# Jupyter Notebook Integration

> Compare usage in current architecture with extensions.

## Current Usage in Jupyter Notebooks

The ModelChecker framework can be used in Jupyter notebooks with the current API, though it's primarily designed for command-line usage. Here's how to use it in notebooks with the current architecture:

### Basic Setup

```python
# Import core components
from model_checker import BuildExample, get_theory
from model_checker.theory_lib import get_examples
from model_checker.theory_lib.default import Semantics, Proposition, ModelStructure, default_operators

# Configure display options for better notebook output
import IPython.display
from IPython.display import HTML, display

# Define a helper function to format terminal output for notebooks
def display_model_output(model):
    # Replace ANSI color codes with HTML/CSS
    output = model.get_output()
    formatted_output = convert_ansi_to_html(output)
    display(HTML(formatted_output))
```

### Creating and Checking Models

```python
# Load a semantic theory
theory = get_theory("default")

# Create a model 
settings = {
    'N': 3,                # Number of atomic propositions
    'contingent': True,    # Use contingent valuations
    'non_empty': True,     # Enforce non-empty valuations
    'max_time': 5,         # Maximum computation time (seconds)
}

# Create a custom example
example = [["p", r"p \rightarrow q"], ["q"], settings]
model = BuildExample("custom_example", theory, example)

# Display model results
display_model_output(model)
```

### Interactive Formula Checking

```python
def check_formula(formula, theory_name="default", premises=None):
    """Check a formula and display the results in a notebook-friendly way."""
    theory = get_theory(theory_name)
    premises = premises or []
    example = [premises, [formula], {'N': 3, 'max_time': 5}]
    model = BuildExample("formula_check", theory, example)
    return model.result

# Use in notebook
formula = "□(p → q) → (□p → □q)"
result = check_formula(formula)
display(HTML(f"<b>Formula:</b> {formula}<br><b>Valid:</b> {result}"))
```

## Limitations of Current Architecture in Notebooks

The current architecture has several limitations when used in Jupyter notebooks:

1. **Output Formatting**: Most output methods print directly to stdout rather than returning structured data
2. **Visualization**: Visualization is primarily text-based with terminal ANSI colors
3. **Interactivity**: Limited support for interactive exploration and parameter adjustment
4. **State Management**: No built-in mechanisms for saving/restoring model state between notebook cells
5. **Results Integration**: Difficult to integrate model checking results with other notebook tools

## Strategies for Jupyter Notebook Integration

Below are strategies to enhance the ModelChecker API for better Jupyter notebook integration, from simplest to most comprehensive.

### Strategy 1: Notebook Adapter Module

Create a lightweight adapter module specifically for notebook usage:

```python
# model_checker/notebook.py - Notebook integration module
import IPython.display
from IPython.display import HTML, display

class NotebookAdapter:
    """Adapter for using ModelChecker in Jupyter notebooks."""
    
    def __init__(self, theory_name="default"):
        """Initialize with the specified theory."""
        from model_checker import get_theory
        self.theory_name = theory_name
        self.theory = get_theory(theory_name)
    
    def check_formula(self, formula, premises=None, settings=None):
        """Check if a formula is valid given premises."""
        from model_checker import BuildExample
        premises = premises or []
        settings = settings or {'N': 3, 'max_time': 5}
        example = [premises, [formula], settings]
        model = BuildExample("notebook_check", self.theory, example)
        return self._format_result(model, formula)
    
    def find_model(self, formulas, settings=None):
        """Find a model satisfying all formulas."""
        from model_checker import BuildExample
        settings = settings or {'N': 3, 'max_time': 5}
        example = [formulas, [], settings]
        model = BuildExample("notebook_model", self.theory, example)
        return self._format_model(model)
    
    def _format_result(self, model, formula):
        """Format model checking results for notebook display."""
        valid = model.result
        model_html = self._convert_model_to_html(model)
        return HTML(f"""
        <div style="margin: 10px; padding: 10px; border: 1px solid #ddd;">
            <h3>Formula: {formula}</h3>
            <p><b>Valid:</b> {valid}</p>
            {model_html}
        </div>
        """)
    
    def _format_model(self, model):
        """Format a found model for notebook display."""
        # Implementation to convert model to HTML visualization
        pass
    
    def _convert_model_to_html(self, model):
        """Convert model output to HTML for notebook display."""
        # Implementation to convert ANSI text to HTML
        pass
```

Usage in notebooks would be much simpler:

```python
from model_checker.notebook import NotebookAdapter

checker = NotebookAdapter("default")
checker.check_formula("p → (q → p)")
```

Benefits:
- No changes to core architecture required
- Quick implementation
- Improved notebook user experience

Limitations:
- Limited to adapter capabilities
- No deep integration with notebook widgets
