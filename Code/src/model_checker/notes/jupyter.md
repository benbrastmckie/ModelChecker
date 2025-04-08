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
example = [["p", "p → q"], ["q"], settings]
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

### Strategy 2: Interactive Model Explorer

Create a more interactive model explorer using Jupyter widgets:

```python
import ipywidgets as widgets
from IPython.display import display, HTML

class InteractiveModelExplorer:
    """Interactive model explorer for Jupyter notebooks."""
    
    def __init__(self, theory_name="default"):
        """Initialize the explorer with a theory."""
        from model_checker import get_theory
        self.theory = get_theory(theory_name)
        self.settings = {'N': 3, 'max_time': 5}
        self._build_ui()
    
    def _build_ui(self):
        """Build the interactive UI components."""
        self.formula_input = widgets.Text(
            value='p → q',
            description='Formula:',
            style={'description_width': 'initial'}
        )
        
        self.premises_input = widgets.Textarea(
            value='',
            description='Premises:',
            style={'description_width': 'initial'}
        )
        
        self.check_button = widgets.Button(
            description='Check Formula',
            button_style='primary'
        )
        self.check_button.on_click(self._on_check_click)
        
        self.settings_accordion = self._build_settings_ui()
        self.output_area = widgets.Output()
        
        # Assemble UI components
        self.ui = widgets.VBox([
            self.formula_input,
            self.premises_input,
            self.check_button,
            self.settings_accordion,
            self.output_area
        ])
    
    def _build_settings_ui(self):
        """Build settings controls."""
        # Create widgets for various settings
        # Return accordion widget with settings controls
        pass
    
    def _on_check_click(self, button):
        """Handle check button click."""
        with self.output_area:
            self.output_area.clear_output()
            formula = self.formula_input.value
            premises = [p.strip() for p in self.premises_input.value.split('\n') if p.strip()]
            # Check formula and display results
            pass
    
    def display(self):
        """Display the explorer UI."""
        display(self.ui)
```

Usage would be:

```python
from model_checker.interactive import InteractiveModelExplorer

explorer = InteractiveModelExplorer()
explorer.display()
```

Benefits:
- Fully interactive UI for model exploration
- No changes to core architecture
- Better notebook integration

Limitations:
- More complex implementation
- Limited to current API capabilities

### Strategy 3: Notebook-Optimized API Extension

Create a more comprehensive API extension designed specifically for notebook usage, with rich visualization and integration:

```python
# model_checker/notebook_api.py

import networkx as nx
import matplotlib.pyplot as plt
import pandas as pd
import ipywidgets as widgets
from IPython.display import display, HTML

class ModelVisualization:
    """Rich visualization for models in notebooks."""
    
    @staticmethod
    def generate_graph(model):
        """Generate a NetworkX graph from a model."""
        G = nx.DiGraph()
        # Extract nodes and edges from model
        # Return graph for visualization
        pass
    
    @staticmethod
    def plot_model(model, figsize=(10, 6)):
        """Plot a model as a graph."""
        G = ModelVisualization.generate_graph(model)
        plt.figure(figsize=figsize)
        # Plot graph with matplotlib
        pass
    
    @staticmethod
    def model_to_dataframe(model):
        """Convert model to a pandas DataFrame."""
        # Extract model data into a DataFrame
        pass

class NotebookModelChecker:
    """Comprehensive notebook interface for model checking."""
    
    def __init__(self, theory_name="default"):
        """Initialize the model checker."""
        # Load theory and initialize state
        pass
    
    def check_validity(self, formula, premises=None, settings=None):
        """Check validity of a formula with rich result display."""
        # Check formula and return rich display object
        pass
    
    def find_models(self, formulas, count=1, settings=None):
        """Find multiple models satisfying formulas."""
        # Find models and return as DataFrame or visualization
        pass
    
    def compare_theories(self, formula, theory_names=None):
        """Compare formula evaluation across different theories."""
        # Evaluate in multiple theories and display comparison
        pass
    
    def export_model(self, model, format="latex"):
        """Export a model in various formats."""
        # Export model to LaTeX, JSON, etc.
        pass
    
    def interactive_playground(self):
        """Launch an interactive model exploration playground."""
        # Create and display interactive widgets
        pass
```

Usage:

```python
from model_checker.notebook_api import NotebookModelChecker

mc = NotebookModelChecker()

# Check a formula with rich output
mc.check_validity("□(p → q) → (□p → □q)")

# Find and visualize models
models = mc.find_models(["p", "◇q", "□(p → q)"], count=3)
models.visualize()

# Launch interactive playground
mc.interactive_playground()
```

Benefits:
- Rich visualization capabilities
- Comprehensive notebook integration
- Interactive exploration
- Integration with pandas, matplotlib
- Export capabilities for papers/presentations

Limitations:
- Requires significant development
- Separate API may diverge from core implementation

## Implementation Recommendations

To make ModelChecker more notebook-friendly with minimal changes to the core architecture:

1. **Short-term (Minimal Changes)**:
   - Create a simple `notebook.py` adapter module for basic notebook integration
   - Add HTML output formatting for model results
   - Provide helper functions for common notebook tasks
   - Create example notebooks demonstrating basic usage

2. **Medium-term (Moderate Enhancement)**:
   - Implement model serialization for saving/loading in notebooks
   - Create visualization functions using matplotlib/networkx
   - Add widget-based interactive controls
   - Provide pandas DataFrame integration for result analysis

3. **Long-term (Full Integration)**:
   - Develop a comprehensive notebook API with rich visualization
   - Create a model exploration playground with interactive widgets
   - Implement export capabilities for academic papers (LaTeX output)
   - Provide graphical model builder interface

## Example Notebook Usage

Here's a complete example of using ModelChecker in a notebook with the recommended adapter approach:

```python
# Import the notebook adapter
from model_checker.notebook import NotebookAdapter

# Create a model checker with default theory
mc = NotebookAdapter("default")

# Check a simple formula
mc.check_formula("p → (q → p)")

# Check modal formula with premises
mc.check_formula("□q", premises=["p", "p → □q"])

# Find a model satisfying a set of formulas
model = mc.find_model(["p", "◇q", "□(p → q)"])

# Export the model as LaTeX for an academic paper
latex_code = mc.export_model(model, format="latex")
```

With these enhancements, ModelChecker could become a powerful tool for interactive logical exploration in Jupyter notebooks, suitable for both teaching and research purposes.


