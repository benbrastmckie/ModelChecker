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

### Strategy: Notebook Adapter Module

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

## Comprehensive Refactoring Strategy for Jupyter Integration

Based on the current implementation and identified issues, below is a detailed strategy for refactoring the Jupyter notebook integration.

### 1. Current State Analysis

The current Jupyter integration has several issues:

1. **Dependency Management**: The current module relies on try/except blocks for importing dependencies which can lead to inconsistent behavior.
2. **Path Resolution**: Manual path manipulation is used to locate the model_checker package, making it brittle.
3. **Type Errors**: The exclusion theory example notebook reveals issues with type checking between imported modules.
4. **Unicode Operator Handling**: Duplicate code for handling unicode operators in different functions.
5. **Visualization Limitations**: Limited graph-based visualization that doesn't adapt to different semantic theories.
6. **Module Structure**: The jupyter integration is a single monolithic file rather than a package with well-defined components.
7. **Theory-Specific Features**: Poor integration with theory-specific visualization methods.
8. **Environment Setup**: Complex environment setup process, especially for NixOS users.

### 2. Refactoring Goals

1. **Modular Architecture**: Reorganize Jupyter integration as a proper package with specialized components
2. **Standardized Theory Interface**: Create a consistent interface for theories to define their visualization requirements
3. **Robust Dependency Management**: Improve importing and error reporting for dependencies
4. **Enhanced Visualizations**: Support more sophisticated visualizations with theory-specific customizations
5. **Better Unicode Support**: Centralize and improve handling of unicode operators
6. **Simplified API**: Provide high-level, easy-to-use functions for common tasks
7. **Cross-Platform Compatibility**: Ensure seamless operation across standard Python installations and NixOS
8. **Theory-Agnostic Design**: Ensure the framework operates consistently across all semantic theories

### 3. Proposed Architecture

```
model_checker/
├── jupyter/
│   ├── __init__.py             # Public API and imports
│   ├── adapters.py             # Theory-specific adapter classes
│   ├── display.py              # Visualization and output formatting
│   ├── environment.py          # Environment setup utilities
│   ├── interactive.py          # Interactive UI components
│   ├── operators.py            # Unicode operator handling
│   └── utils.py                # Shared utilities
```

### 4. Component Implementations

#### 4.1 Public API (`__init__.py`)

This will expose simplified, high-level functions and classes for notebook users:

```python
"""
ModelChecker Jupyter integration package.

This package provides tools for using ModelChecker in Jupyter notebooks
with interactive visualizations and simplified interfaces.

Basic usage:
    from model_checker.jupyter import check_formula
    check_formula("p → q", premises=["p"])
    
Interactive usage:
    from model_checker.jupyter import ModelExplorer
    explorer = ModelExplorer()
    explorer.display()
"""

# Public API
from .interactive import ModelExplorer, FormulaChecker
from .display import (
    display_model, 
    display_formula_check, 
    display_countermodel
)
from .operators import unicode_to_latex, latex_to_unicode
from .environment import setup_environment, get_available_theories
from .utils import load_examples

# Simplified API functions
def check_formula(formula, theory_name="default", premises=None, settings=None):
    """Check if a formula is valid given premises."""
    from .display import display_formula_check
    return display_formula_check(formula, theory_name, premises, settings)

def find_countermodel(formula, theory_name="default", premises=None, settings=None):
    """Find a countermodel for a formula with optional premises."""
    from .display import display_countermodel
    return display_countermodel(formula, theory_name, premises, settings)

def explore_formula(formula, theory_name="default", premises=None, settings=None):
    """Create an interactive explorer for a specific formula."""
    explorer = ModelExplorer(theory_name)
    explorer.set_formula(formula)
    if premises:
        explorer.set_premises(premises)
    if settings:
        explorer.update_settings(settings)
    explorer.check_formula()
    return explorer
```

#### 4.2 Theory Adapters (`adapters.py`)

This module will provide theory-specific adapters to handle differences in visualization and model representation:

```python
"""
Theory-specific adapters for Jupyter integration.

These adapters provide a consistent interface for working with different
semantic theories in the notebook environment.
"""

from abc import ABC, abstractmethod

class TheoryAdapter(ABC):
    """Base class for theory-specific adapters."""
    
    @abstractmethod
    def model_to_graph(self, model):
        """Convert a model to a networkx graph for visualization."""
        pass
        
    @abstractmethod
    def format_formula(self, formula):
        """Format a formula for display."""
        pass
    
    @abstractmethod
    def format_model(self, model):
        """Format a model for display."""
        pass
    
    @classmethod
    def get_adapter(cls, theory_name):
        """Factory method to get the appropriate adapter."""
        # Registry of theory adapters
        registry = {
            "default": DefaultTheoryAdapter,
            "exclusion": ExclusionTheoryAdapter,
            "imposition": ImpositionTheoryAdapter,
            "bimodal": BimodalTheoryAdapter,
        }
        
        adapter_class = registry.get(theory_name, DefaultTheoryAdapter)
        return adapter_class()


class DefaultTheoryAdapter(TheoryAdapter):
    """Adapter for the default hyperintensional theory."""
    
    def model_to_graph(self, model):
        """Convert default model to graph."""
        import networkx as nx
        # Implementation for default theory
        # ...
        
    def format_formula(self, formula):
        """Format formula for default theory."""
        # Implementation for default theory
        # ...
        
    def format_model(self, model):
        """Format model for default theory."""
        # Implementation for default theory
        # ...


class ExclusionTheoryAdapter(TheoryAdapter):
    """Adapter for exclusion theory."""
    
    def model_to_graph(self, model):
        """Convert exclusion model to graph."""
        import networkx as nx
        # Exclusion-specific implementation
        # ...
        
    def format_formula(self, formula):
        """Format formula for exclusion theory."""
        # Exclusion-specific implementation
        # ...
        
    def format_model(self, model):
        """Format model for exclusion theory."""
        # Exclusion-specific implementation
        # ...

# Additional theory adapters...
```

#### 4.3 Display Utilities (`display.py`)

This module will handle all visualization and display formatting:

```python
"""
Display utilities for Jupyter notebooks.

This module provides tools for formatting and displaying ModelChecker
outputs in Jupyter notebooks, including HTML formatting and visualizations.
"""

from IPython.display import display, HTML
import matplotlib.pyplot as plt
import io
from contextlib import redirect_stdout

def convert_ansi_to_html(ansi_text):
    """Convert ANSI terminal output to HTML."""
    # Implementation
    # ...

def capture_output(obj, method_name, *args, **kwargs):
    """Capture stdout output from an object method."""
    output_buffer = io.StringIO()
    with redirect_stdout(output_buffer):
        method = getattr(obj, method_name)
        method(*args, **kwargs)
    return output_buffer.getvalue()

def display_model(model, visualization_type="text", show_details=True):
    """Display a model with text or graph visualization."""
    from .adapters import TheoryAdapter
    
    if not model:
        return HTML("<p>No model available</p>")
    
    # Get the appropriate adapter
    theory_name = getattr(model, "theory_name", "default")
    adapter = TheoryAdapter.get_adapter(theory_name)
    
    if visualization_type == "text":
        # Text-based visualization
        output = capture_output(model.model_structure, 'print_all', 
                                model.example_settings, "model", theory_name)
        return HTML(convert_ansi_to_html(output))
    elif visualization_type == "graph":
        # Graph-based visualization
        fig = _create_graph_visualization(model, adapter)
        display(fig)
        plt.close(fig)
        
        # Show key information as HTML
        return HTML(adapter.format_model(model))
    else:
        return HTML(f"<p>Unsupported visualization type: {visualization_type}</p>")

def _create_graph_visualization(model, adapter):
    """Create a graph visualization of a model."""
    import matplotlib.pyplot as plt
    
    # Use the adapter to get a graph representation
    G = adapter.model_to_graph(model.model_structure)
    
    fig, ax = plt.subplots(figsize=(10, 6))
    # Common graph rendering logic
    # ...
    return fig

def display_formula_check(formula, theory_name="default", premises=None, settings=None):
    """Display formula checking results."""
    from .operators import normalize_formula
    from model_checker import BuildExample, get_theory
    
    # Normalize formula and premises
    formula = normalize_formula(formula)
    if premises:
        premises = [normalize_formula(p) for p in premises]
    else:
        premises = []
        
    # Use default settings if not provided
    if not settings:
        settings = {'N': 3, 'max_time': 5, 'model': True}
    
    # Create model and check formula
    theory = get_theory(theory_name)
    example = [premises, [formula], settings]
    
    # Create build module object with needed attributes
    build_module = type('BuildModule', (), {
        'module': type('Module', (), {'general_settings': {}}),
        'module_flags': type('Flags', (), {})
    })
    
    # Build model
    model = BuildExample(build_module, theory, example)
    
    # Format and display result
    valid = model.check_result()
    color = "green" if valid else "red"
    
    # Get text output
    output = capture_output(model.model_structure, 'print_all',
                          model.example_settings, "formula_check", theory_name)
    
    html = HTML(
        f"<h3>Formula: {formula}</h3>"
        f"<p><b>Valid:</b> <span style='color:{color}'>{valid}</span></p>"
        f"{convert_ansi_to_html(output)}"
    )
    
    return html

def display_countermodel(formula, theory_name="default", premises=None, settings=None):
    """Display a countermodel for a formula if one exists."""
    # Similar to display_formula_check but with model=True in settings
    # ...
```

#### 4.4 Environment Setup (`environment.py`)

This module will handle environment setup, path resolution, and dependency management:

```python
"""
Environment setup utilities for Jupyter notebooks.

This module ensures the ModelChecker package is properly configured
in the notebook environment, handling path resolution and imports.
"""

import os
import sys
import importlib
import warnings

def setup_environment():
    """
    Set up the environment for notebooks by adding the correct paths
    to sys.path and ensuring all modules can be imported properly.
    
    Returns:
        dict: Information about the setup environment
    """
    # Auto-detect project root
    current_dir = os.getcwd()
    project_root = _find_project_root(current_dir)
    
    if not project_root:
        warnings.warn(
            "Could not automatically find ModelChecker project root. "
            "If you experience import errors, please specify the path manually."
        )
        return {"status": "warning", "message": "Could not find project root"}
    
    # Add paths to sys.path if needed
    paths_to_add = [
        project_root,
        os.path.join(project_root, 'src'),
    ]
    
    for path in paths_to_add:
        if path not in sys.path:
            sys.path.insert(0, path)
    
    # Try importing model_checker
    try:
        import model_checker
        return {
            "status": "success",
            "project_root": project_root,
            "model_checker_path": model_checker.__file__,
            "model_checker_version": model_checker.__version__
        }
    except ImportError as e:
        return {
            "status": "error",
            "message": f"Could not import model_checker: {str(e)}",
            "project_root": project_root
        }

def _find_project_root(start_dir):
    """
    Find the ModelChecker project root by looking for key identifiers.
    
    Args:
        start_dir: Directory to start searching from
        
    Returns:
        str or None: Path to project root if found, None otherwise
    """
    # Search strategies:
    # 1. Look for pyproject.toml with model_checker in it
    # 2. Look for src/model_checker directory
    # 3. Look for common installation paths
    
    # Implementation
    # ...

def get_available_theories():
    """
    Get the list of available semantic theories.
    
    Returns:
        list: Names of available theories
    """
    try:
        from model_checker.theory_lib import AVAILABLE_THEORIES
        return AVAILABLE_THEORIES
    except ImportError:
        return ["default"]  # Fallback to default theory
```

#### 4.5 Interactive UI (`interactive.py`)

This module will provide interactive UI components using ipywidgets:

```python
"""
Interactive UI components for Jupyter notebooks.

This module provides widget-based interfaces for interacting with 
ModelChecker in Jupyter notebooks.
"""

import ipywidgets as widgets
from IPython.display import display, clear_output

class ModelExplorer:
    """Interactive model explorer for Jupyter notebooks."""
    
    def __init__(self, theory_name="default"):
        """Initialize with a theory."""
        from .environment import setup_environment
        
        # Ensure environment is set up
        env_status = setup_environment()
        if env_status["status"] != "success":
            print(f"Warning: {env_status['message']}")
        
        # Import dependencies
        from model_checker import get_theory
        
        self.theory_name = theory_name
        self.theory = get_theory(theory_name)
        
        self.settings = {
            'N': 3,
            'max_time': 5,
            'contingent': True,
            'non_empty': True,
            'model': True  # Default to looking for a satisfying model
        }
        
        self.model = None
        self._build_ui()
    
    def _build_ui(self):
        """Build the interactive UI components."""
        # Implementation similar to current code but more modular
        # ...
    
    def set_formula(self, formula):
        """Set the formula to check."""
        from .operators import normalize_formula
        self.formula_input.value = normalize_formula(formula)
    
    def set_premises(self, premises):
        """Set the premises."""
        from .operators import normalize_formula
        if isinstance(premises, list):
            self.premises_input.value = "\n".join(
                [normalize_formula(p) for p in premises]
            )
        else:
            self.premises_input.value = normalize_formula(premises)
    
    def update_settings(self, settings):
        """Update model settings."""
        for key, value in settings.items():
            if key in self.settings:
                self.settings[key] = value
                # Update UI controls if they exist
                # ...
    
    def display(self):
        """Display the explorer UI."""
        display(self.ui)
    
    def check_formula(self):
        """Check the current formula."""
        # Implementation
        # ...
    
    def find_next_model(self):
        """Find the next model satisfying the formula."""
        # Implementation
        # ...
        
class FormulaChecker:
    """Simple formula checking widget."""
    
    def __init__(self, theory_name="default"):
        """Initialize with a theory."""
        # Simpler version of ModelExplorer
        # ...
```

#### 4.6 Operator Utilities (`operators.py`)

This module will centralize all operator handling logic:

```python
"""
Operator utilities for Jupyter notebooks.

This module provides tools for working with logical operators in 
different notations (Unicode, LaTeX) in Jupyter notebooks.
"""

def normalize_formula(formula, format_type="latex"):
    """
    Normalize a formula to a specific format.
    
    Args:
        formula: The formula to normalize
        format_type: The target format ('latex', 'unicode', 'ascii')
        
    Returns:
        str: Normalized formula
    """
    if not isinstance(formula, str):
        return str(formula)
    
    if format_type == "latex":
        return unicode_to_latex(formula)
    elif format_type == "unicode":
        return latex_to_unicode(formula)
    else:
        return formula

def unicode_to_latex(formula):
    """Convert Unicode operators to LaTeX notation."""
    # Unicode to LaTeX mappings
    replacements = {
        '→': '\\rightarrow',
        '∧': '\\wedge',
        '∨': '\\vee',
        '¬': '\\neg',
        '□': '\\Box',
        '◇': '\\Diamond',
        '↔': '\\leftrightarrow',
        '≡': '\\equiv',
        '⊥': '\\bot',
        '⊤': '\\top'
    }
    
    # Theory-specific mappings
    theory_mappings = {
        "exclusion": {
            "exclude": "\\exclude",
            "uniwedge": "\\uniwedge",
            "univee": "\\univee",
            "uniequiv": "\\uniequiv"
        }
    }
    
    # Apply Unicode replacements
    for unicode_op, latex_op in replacements.items():
        formula = formula.replace(unicode_op, latex_op)
    
    # Ensure proper parenthesization
    formula = ensure_parentheses(formula)
    
    return formula

def latex_to_unicode(formula):
    """Convert LaTeX notation to Unicode operators."""
    # LaTeX to Unicode mappings (reverse of unicode_to_latex)
    # ...
    
def ensure_parentheses(formula):
    """Ensure binary operators are wrapped in parentheses."""
    binary_operators = [
        '\\rightarrow', '\\wedge', '\\vee', '\\leftrightarrow', '\\equiv',
        '\\uniwedge', '\\univee', '\\uniequiv'
    ]
    
    for op in binary_operators:
        if op in formula and not (formula.startswith('(') and formula.endswith(')')):
            formula = f"({formula})"
            break
    
    return formula
```

#### 4.7 Shared Utilities (`utils.py`)

This module will provide shared utility functions:

```python
"""
Shared utilities for Jupyter integration.

This module provides common utility functions used across the 
Jupyter integration package.
"""

import importlib
from typing import Dict, List, Any, Optional

def load_examples(theory_name, example_prefix=None):
    """
    Load examples from a theory's examples module.
    
    Args:
        theory_name: Name of the theory to load examples from
        example_prefix: Optional prefix to filter examples
        
    Returns:
        dict: Dictionary of example name to example data
    """
    try:
        # Dynamic import of the examples module
        examples_module = importlib.import_module(
            f"model_checker.theory_lib.{theory_name}.examples"
        )
        
        # Filter examples by prefix if provided
        examples = {}
        for name in dir(examples_module):
            if name.startswith('__'):
                continue
                
            if example_prefix and not name.startswith(example_prefix):
                continue
                
            value = getattr(examples_module, name)
            if isinstance(value, list) and len(value) == 3:
                # Assume it's an example if it's a list of length 3
                examples[name] = value
                
        return examples
    except ImportError:
        return {}

def get_example_categories(examples):
    """
    Categorize examples by type.
    
    Args:
        examples: Dictionary of examples
        
    Returns:
        dict: Examples grouped by category
    """
    categories = {}
    
    for name, example in examples.items():
        # Use naming conventions to infer categories
        if "_CM_" in name:
            category = "Countermodels"
        elif "_TH_" in name:
            category = "Theorems"
        else:
            category = "Other"
            
        if category not in categories:
            categories[category] = {}
            
        categories[category][name] = example
        
    return categories

def format_settings(settings):
    """
    Format settings dictionary for display.
    
    Args:
        settings: Settings dictionary
        
    Returns:
        str: Formatted HTML for settings
    """
    if not settings:
        return "<p>No settings</p>"
        
    settings_html = "<ul>"
    for key, value in settings.items():
        settings_html += f"<li><b>{key}:</b> {value}</li>"
    settings_html += "</ul>"
    
    return settings_html
```

### 5. Theory-Specific Extensions

Each theory should implement specific methods to support custom visualizations:

1. Add a `visualize()` method to each `ModelStructure` class that returns a matplotlib figure
2. Implement theory-specific graph representations
3. Provide theory-specific formula formatting functions

### 6. Migration Strategy

1. Implement the new modular architecture in parallel with the existing implementation
2. Create compatibility functions to ensure existing notebooks continue to work
3. Gradually deprecate the old monolithic module
4. Update the documentation and tutorials to use the new architecture

### 7. Testing Strategy

1. Create test notebooks for each theory
2. Test with both standard Python and NixOS environments
3. Verify compatibility with existing notebooks
4. Perform regression testing against the current implementation

### 8. Documentation Updates

1. Create a Jupyter-specific tutorial
2. Update the main documentation with Jupyter integration examples
3. Provide theory-specific visualization examples
4. Include troubleshooting guidance for common issues
