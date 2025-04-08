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

## Implementation Plan: Strategy 2 - Interactive Model Explorer

This implementation plan outlines how to create an interactive model explorer for Jupyter notebooks using the ModelChecker framework and Jupyter widgets.

### 1. Dependencies and Requirements

The interactive model explorer will require the following dependencies:

```python
# Core dependencies (already in the project)
from model_checker import BuildExample, get_theory
from model_checker.theory_lib import get_examples

# New dependencies for notebook integration
import ipywidgets as widgets
from IPython.display import display, HTML, clear_output
import matplotlib.pyplot as plt
import networkx as nx
```

These additional libraries will need to be added to the project's dependencies in `pyproject.toml`:

```toml
dependencies = [
    "z3-solver",
    "ipywidgets",  # For interactive UI components
    "matplotlib",  # For visualization
    "networkx",    # For graph representation
]
```

### 2. Project Structure

Create a new module `notebook.py` in the `model_checker` package:

```
model_checker/
├── __init__.py
├── ...
└── notebook.py  # New file for notebook integration
```

### 3. Implementation Components

#### 3.1. ANSI Color Conversion

First, implement a utility function to convert ANSI color codes to HTML for proper display in Jupyter:

```python
def convert_ansi_to_html(ansi_text):
    """Convert ANSI color codes to HTML for Jupyter notebook display."""
    # ANSI color to CSS mapping
    ansi_to_css = {
        "\033[0m": "</span>",   # Reset
        "\033[31m": "<span style='color:red'>",  # Red
        "\033[32m": "<span style='color:green'>",  # Green
        "\033[33m": "<span style='color:orange'>",  # Orange/Yellow
        "\033[34m": "<span style='color:blue'>",  # Blue
        "\033[35m": "<span style='color:purple'>",  # Purple
        "\033[36m": "<span style='color:cyan'>",  # Cyan
        "\033[37m": "<span style='color:lightgray'>",  # Light Gray
        "\033[1m": "<span style='font-weight:bold'>",  # Bold
    }
    
    # Replace ANSI codes with their HTML equivalents
    html_text = ansi_text
    for ansi_code, html_code in ansi_to_css.items():
        html_text = html_text.replace(ansi_code, html_code)
    
    # Ensure all spans are closed
    open_spans = html_text.count("<span")
    close_spans = html_text.count("</span>")
    if open_spans > close_spans:
        html_text += "</span>" * (open_spans - close_spans)
    
    # Wrap in a pre tag to preserve formatting
    return f"<pre>{html_text}</pre>"
```

#### 3.2. Model Output Capture

Implement a wrapper to capture the model output (which normally goes to stdout) for display in Jupyter:

```python
def capture_model_output(model, method, *args, **kwargs):
    """Capture the output of a model method that prints to stdout.
    
    Args:
        model: The model object
        method: The method name to call (e.g., 'print_all')
        *args, **kwargs: Arguments to pass to the method
        
    Returns:
        str: The captured output
    """
    import io
    from contextlib import redirect_stdout
    
    output_buffer = io.StringIO()
    with redirect_stdout(output_buffer):
        getattr(model, method)(*args, **kwargs)
    return output_buffer.getvalue()
```

#### 3.3. Model Visualization

Implement graph-based visualization of models:

```python
def model_to_graph(model):
    """Convert a model to a NetworkX graph for visualization.
    
    Args:
        model: ModelStructure object
        
    Returns:
        G: NetworkX DiGraph representing the model
    """
    G = nx.DiGraph()
    
    # Add nodes (states)
    for state in model.z3_world_states:
        state_str = model.semantics.bitvec_to_substates(state, model.N)
        attrs = {"world": True}
        G.add_node(state_str, **attrs)
    
    # If you have accessibility relations, add edges
    # (This depends on your specific model structure)
    # ...
    
    return G

def visualize_model(model, figsize=(10, 6)):
    """Visualize a model as a graph.
    
    Args:
        model: ModelStructure object
        figsize: Figure size
        
    Returns:
        fig: Matplotlib figure
    """
    G = model_to_graph(model)
    
    fig, ax = plt.subplots(figsize=figsize)
    pos = nx.spring_layout(G)
    
    # Draw nodes
    world_nodes = [n for n, d in G.nodes(data=True) if d.get("world", False)]
    other_nodes = [n for n in G.nodes() if n not in world_nodes]
    
    nx.draw_networkx_nodes(G, pos, nodelist=world_nodes, 
                          node_color="lightblue", node_size=500)
    nx.draw_networkx_nodes(G, pos, nodelist=other_nodes, 
                          node_color="lightgray", node_size=300)
    
    # Draw edges
    nx.draw_networkx_edges(G, pos, arrows=True)
    
    # Draw labels
    nx.draw_networkx_labels(G, pos)
    
    plt.axis("off")
    plt.tight_layout()
    
    return fig
```

#### 3.4. Interactive Model Explorer Class

The main class for the interactive model explorer:

```python
class InteractiveModelExplorer:
    """Interactive model explorer for Jupyter notebooks."""
    
    def __init__(self, theory_name="default"):
        """Initialize the explorer with a theory.
        
        Args:
            theory_name: Name of the semantic theory to use
        """
        from model_checker import get_theory
        
        self.theory_name = theory_name
        self.theory = get_theory(theory_name)
        self.settings = {
            'N': 3,
            'max_time': 5,
            'contingent': True,
            'non_empty': True,
            'print_constraints': False
        }
        self.model = None
        self._build_ui()
    
    def _build_ui(self):
        """Build the interactive UI components."""
        # Formula input
        self.formula_input = widgets.Text(
            value='p → q',
            description='Formula:',
            style={'description_width': 'initial'}
        )
        
        # Premises input
        self.premises_input = widgets.Textarea(
            value='',
            description='Premises:',
            placeholder='Enter premises (one per line)',
            style={'description_width': 'initial'}
        )
        
        # Settings accordion
        self.settings_accordion = self._build_settings_ui()
        
        # Theory selector
        self.theory_selector = widgets.Dropdown(
            options=self._get_available_theories(),
            value=self.theory_name,
            description='Theory:',
            style={'description_width': 'initial'}
        )
        self.theory_selector.observe(self._on_theory_change, names='value')
        
        # Check button
        self.check_button = widgets.Button(
            description='Check Formula',
            button_style='primary'
        )
        self.check_button.on_click(self._on_check_click)
        
        # Next model button
        self.next_model_button = widgets.Button(
            description='Find Next Model',
            button_style='info',
            disabled=True
        )
        self.next_model_button.on_click(self._on_next_model_click)
        
        # Visualization selector
        self.viz_selector = widgets.RadioButtons(
            options=['Text Output', 'Graph Visualization'],
            value='Text Output',
            description='View:',
            style={'description_width': 'initial'}
        )
        self.viz_selector.observe(self._on_viz_change, names='value')
        
        # Output area
        self.output_area = widgets.Output()
        
        # Assemble UI components
        control_panel = widgets.VBox([
            self.formula_input,
            self.premises_input,
            self.theory_selector,
            self.settings_accordion,
            widgets.HBox([self.check_button, self.next_model_button]),
            self.viz_selector
        ])
        
        self.ui = widgets.HBox([
            control_panel,
            self.output_area
        ])
    
    def _build_settings_ui(self):
        """Build settings controls."""
        # Number of atomic propositions
        self.n_slider = widgets.IntSlider(
            value=self.settings['N'],
            min=1,
            max=10,
            step=1,
            description='Num Props (N):',
            style={'description_width': 'initial'}
        )
        self.n_slider.observe(lambda change: self._update_setting('N', change['new']), names='value')
        
        # Max time
        self.max_time_slider = widgets.FloatSlider(
            value=self.settings['max_time'],
            min=1,
            max=30,
            step=1,
            description='Max Time (s):',
            style={'description_width': 'initial'}
        )
        self.max_time_slider.observe(
            lambda change: self._update_setting('max_time', change['new']), 
            names='value'
        )
        
        # Contingent checkbox
        self.contingent_checkbox = widgets.Checkbox(
            value=self.settings['contingent'],
            description='Contingent Valuations',
            style={'description_width': 'initial'}
        )
        self.contingent_checkbox.observe(
            lambda change: self._update_setting('contingent', change['new']), 
            names='value'
        )
        
        # Non-empty checkbox
        self.non_empty_checkbox = widgets.Checkbox(
            value=self.settings['non_empty'],
            description='Non-Empty Valuations',
            style={'description_width': 'initial'}
        )
        self.non_empty_checkbox.observe(
            lambda change: self._update_setting('non_empty', change['new']), 
            names='value'
        )
        
        # Print constraints checkbox
        self.print_constraints_checkbox = widgets.Checkbox(
            value=self.settings['print_constraints'],
            description='Print Constraints',
            style={'description_width': 'initial'}
        )
        self.print_constraints_checkbox.observe(
            lambda change: self._update_setting('print_constraints', change['new']), 
            names='value'
        )
        
        # Create accordion
        accordion = widgets.Accordion(
            children=[
                widgets.VBox([
                    self.n_slider,
                    self.max_time_slider,
                    self.contingent_checkbox,
                    self.non_empty_checkbox,
                    self.print_constraints_checkbox
                ])
            ],
            selected_index=None
        )
        accordion.set_title(0, 'Settings')
        
        return accordion
    
    def _get_available_theories(self):
        """Get the list of available theories."""
        from model_checker.theory_lib import get_semantic_theories
        return list(get_semantic_theories().keys())
    
    def _update_setting(self, key, value):
        """Update a setting value."""
        self.settings[key] = value
    
    def _on_theory_change(self, change):
        """Handle theory change."""
        self.theory_name = change['new']
        self.theory = get_theory(self.theory_name)
    
    def _on_viz_change(self, change):
        """Handle visualization change."""
        if self.model is not None:
            self._display_result()
    
    def _on_check_click(self, button):
        """Handle check button click."""
        with self.output_area:
            clear_output()
            
            # Get formula and premises
            formula = self.formula_input.value.strip()
            premises = [p.strip() for p in self.premises_input.value.split('\n') if p.strip()]
            
            if not formula:
                print("Please enter a formula to check.")
                return
            
            # Create example for the model checker
            example = [premises, [formula], self.settings]
            
            try:
                # Create a minimal BuildModule for the BuildExample
                from model_checker.builder import BuildModule
                build_module = type('BuildModule', (), {
                    'module': None,
                    'module_flags': type('Flags', (), {})
                })
                
                # Build and check the model
                self.model = BuildExample(build_module, self.theory, example)
                self.next_model_button.disabled = False
                
                # Display the result
                self._display_result()
                
            except Exception as e:
                print(f"Error checking formula: {str(e)}")
    
    def _on_next_model_click(self, button):
        """Handle next model button click."""
        if self.model is None:
            return
            
        with self.output_area:
            clear_output()
            print("Searching for alternative model...")
            
            # Get current Z3 model
            current_z3_model = self.model.model_structure.z3_model
            
            # Try to find the next model
            if self.model.find_next_model(current_z3_model):
                print("Found alternative model:")
                self._display_result()
            else:
                print("No alternative models found.")
    
    def _display_result(self):
        """Display the current model result."""
        if self.model is None:
            return
            
        view_type = self.viz_selector.value
        
        with self.output_area:
            if view_type == 'Text Output':
                # Capture and display text output
                output = capture_model_output(
                    self.model.model_structure, 
                    'print_all',
                    self.model.example_settings,
                    'interactive_check',
                    self.theory_name
                )
                html_output = convert_ansi_to_html(output)
                display(HTML(html_output))
                
                # Show validity result
                formula = self.formula_input.value
                valid = self.model.check_result()
                color = "green" if valid else "red"
                display(HTML(
                    f"<h3>Formula: {formula}</h3>"
                    f"<p><b>Valid:</b> <span style='color:{color}'>{valid}</span></p>"
                ))
                
            elif view_type == 'Graph Visualization':
                # Display graph visualization
                try:
                    fig = visualize_model(self.model.model_structure)
                    display(fig)
                    
                    # Show text summary alongside graph
                    formula = self.formula_input.value
                    valid = self.model.check_result()
                    color = "green" if valid else "red"
                    display(HTML(
                        f"<h3>Formula: {formula}</h3>"
                        f"<p><b>Valid:</b> <span style='color:{color}'>{valid}</span></p>"
                    ))
                    
                except Exception as e:
                    print(f"Error creating visualization: {str(e)}")
                    # Fall back to text display
                    self.viz_selector.value = 'Text Output'
    
    def display(self):
        """Display the explorer UI."""
        display(self.ui)

    def get_output(self):
        """Get the current model output as HTML.
        
        Returns:
            str: HTML representation of the current model output
        """
        if self.model is None:
            return "<p>No model has been created yet.</p>"
            
        output = capture_model_output(
            self.model.model_structure, 
            'print_all',
            self.model.example_settings,
            'interactive_check',
            self.theory_name
        )
        return convert_ansi_to_html(output)
```

### 4. Example Usage

```python
from model_checker.notebook import InteractiveModelExplorer

# Create the explorer with default theory
explorer = InteractiveModelExplorer()

# Display the interactive UI
explorer.display()
```

### 5. Integration with Existing Notebooks

To make it easy to use with existing notebooks, add helper functions:

```python
def check_formula_interactive(formula, theory_name="default", premises=None):
    """Create an interactive model explorer for a specific formula.
    
    Args:
        formula: The formula to check
        theory_name: The semantic theory to use
        premises: Optional list of premises
        
    Returns:
        Explorer widget
    """
    explorer = InteractiveModelExplorer(theory_name)
    explorer.formula_input.value = formula
    if premises:
        explorer.premises_input.value = "\n".join(premises)
    
    # Automatically check the formula
    explorer.check_button.click()
    
    # Return the explorer for further interaction
    return explorer
```

### 6. Implementation Challenges and Solutions

1. **Model Builder Integration**:
   - Challenge: The BuildExample class expects a BuildModule object with certain attributes
   - Solution: Create a minimal BuildModule-like object with the necessary attributes

2. **ANSI Color Conversion**:
   - Challenge: Terminal output uses ANSI colors that don't display in notebooks
   - Solution: Implement a conversion function for ANSI codes to HTML

3. **State Visualization**:
   - Challenge: Creating a visual representation of the model structure
   - Solution: Use NetworkX to create a graph representation of states and relations

4. **Output Capture**:
   - Challenge: Model methods print to stdout instead of returning values
   - Solution: Use redirect_stdout to capture printed output

5. **Asynchronous Model Checking**:
   - Challenge: Long-running model checks can block the notebook UI
   - Solution: Future improvement - use IPython's background tasks for non-blocking execution

### 7. Future Enhancements

1. **Advanced Visualization**: 
   - Implement interactive graph visualization with zooming/panning
   - Add node highlighting to visualize formula evaluation

2. **Formula Builder**:
   - Add a visual formula builder with logical operator buttons
   - Provide syntax validation for user input

3. **Result Export**:
   - Add options to export models as LaTeX or JSON
   - Enable saving visualizations as PNG/SVG

4. **Theory Comparison**:
   - Add side-by-side comparison of the same formula in different theories
   - Highlight semantic differences between theories

5. **Tutorial Integration**:
   - Create example notebooks showcasing logical concepts
   - Build interactive exercises with feedback

### 8. Implementation Timeline

1. **Phase 1 (Core Functionality)**:
   - Implement ANSI to HTML conversion
   - Create the InteractiveModelExplorer class with basic UI
   - Add formula checking and results display

2. **Phase 2 (Visualization)**:
   - Implement model to graph conversion
   - Add basic visualization using NetworkX/Matplotlib
   - Create alternative model finding UI

3. **Phase 3 (Advanced Features)**:
   - Add theory comparison capabilities
   - Implement export functionality
   - Create example notebooks and documentation

### 9. Testing

Develop tests for the Jupyter integration:

1. Test the ANSI to HTML conversion with various model outputs
2. Verify model checking results match the CLI version
3. Test with complex formulas across different theories
4. Ensure compatibility with various Jupyter environments

### 10. Documentation

Create comprehensive documentation:

1. Add docstrings to all functions and classes
2. Create example notebooks showcasing the interactive explorer
3. Add usage instructions to the main README.md
4. Document integration with existing workflows


