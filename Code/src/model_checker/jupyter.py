"""
Jupyter Notebook integration module for ModelChecker.

This module provides interactive tools for using ModelChecker in Jupyter notebooks,
including widgets for model exploration, visualization capabilities, and notebook-friendly
output formatting.

Main components:
- InteractiveModelExplorer: Class for interactive model exploration
- convert_ansi_to_html: Utility for converting ANSI terminal output to HTML
- model_to_graph/visualize_model: Functions for visualizing models graphically
- setup_environment: Sets up the Python path for notebooks
- import_notebook_modules: Imports and returns key modules needed for notebooks
- diagnostic_info: Returns diagnostic information about the environment

Usage:
    from model_checker.jupyter import InteractiveModelExplorer
    
    # Create and display explorer
    explorer = InteractiveModelExplorer()
    explorer.display()
    
    # Check a specific formula
    from model_checker.jupyter import check_formula_interactive
    check_formula_interactive("□(p → q) → (□p → □q)")
"""

import io
from contextlib import redirect_stdout
from typing import List, Dict, Any, Optional, Union, Callable
import os
import sys
import importlib

# Core dependencies
try:
    from model_checker import BuildExample, get_theory
    from model_checker.theory_lib import get_examples, get_semantic_theories
except ImportError:
    # We may need to set up the environment first
    pass

# Interactive UI and visualization
try:
    import ipywidgets as widgets
    from IPython.display import display, HTML, clear_output
    import matplotlib.pyplot as plt
    import networkx as nx
    HAVE_IPYWIDGETS = True
except ImportError:
    HAVE_IPYWIDGETS = False


def setup_environment():
    """
    Set up the environment for notebooks by adding the correct paths
    to sys.path and ensuring all modules can be imported properly.
    """
    # Get the location of this file
    current_file = os.path.abspath(__file__)
    # Up 3 directories: jupyter.py -> model_checker -> src -> Code
    project_root = os.path.dirname(os.path.dirname(os.path.dirname(current_file)))
    
    # Add project root and src directory to path if not already there
    paths_to_add = [
        project_root,
        os.path.join(project_root, 'src'),
    ]
    
    for path in paths_to_add:
        if path not in sys.path:
            sys.path.insert(0, path)
    
    # Try to import model_checker and reload if necessary
    try:
        import model_checker
        # If already imported but from wrong location, reload
        if hasattr(model_checker, '__file__'):
            expected_path = os.path.join(project_root, 'src', 'model_checker')
            if not model_checker.__file__.startswith(expected_path):
                importlib.reload(model_checker)
                # Also reload this module to ensure it has the correct imports
                importlib.reload(sys.modules[__name__])
    except ImportError:
        pass  # Will be caught when notebook tries to import
    
    return {
        'project_root': project_root,
        'sys_path': sys.path
    }


def import_notebook_modules():
    """
    Import and return the key modules needed for notebooks.
    Returns a dictionary with the imported modules.
    """
    # First ensure environment is set up
    setup_environment()
    
    try:
        import model_checker
        from model_checker.jupyter import InteractiveModelExplorer, check_formula
        from model_checker.theory_lib import get_semantic_theories
        
        return {
            'model_checker': model_checker,
            'InteractiveModelExplorer': InteractiveModelExplorer,
            'check_formula': check_formula,
            'get_semantic_theories': get_semantic_theories
        }
    except ImportError as e:
        print(f"Error importing modules: {e}")
        print("Current sys.path:")
        for p in sys.path:
            print(f"  {p}")
        return {}


def diagnostic_info():
    """
    Return diagnostic information about the environment
    """
    env_info = setup_environment()
    
    # Try imports
    try:
        import model_checker
        mc_location = model_checker.__file__
        mc_version = model_checker.__version__
    except ImportError:
        mc_location = "Not found"
        mc_version = "Not found"
    
    # Check this module
    try:
        jupyter_location = __file__
    except NameError:
        jupyter_location = "Not found"
    
    return {
        'project_root': env_info['project_root'],
        'sys_path': env_info['sys_path'],
        'model_checker_location': mc_location,
        'model_checker_version': mc_version,
        'jupyter_module_location': jupyter_location,
    }


def convert_ansi_to_html(ansi_text: str) -> str:
    """Convert ANSI color codes to HTML for Jupyter notebook display.
    
    Args:
        ansi_text: Text containing ANSI color codes
        
    Returns:
        HTML formatted text with ANSI codes converted to CSS styles
    """
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
    return f"<pre style='white-space: pre-wrap;'>{html_text}</pre>"


def capture_model_output(model, method: str, *args, **kwargs) -> str:
    """Capture the output of a model method that prints to stdout.
    
    Args:
        model: The model object
        method: The method name to call (e.g., 'print_all')
        *args, **kwargs: Arguments to pass to the method
        
    Returns:
        str: The captured output
    """
    output_buffer = io.StringIO()
    with redirect_stdout(output_buffer):
        getattr(model, method)(*args, **kwargs)
    return output_buffer.getvalue()


def model_to_graph(model):
    """Convert a model to a NetworkX graph for visualization.
    
    Args:
        model: ModelStructure object
        
    Returns:
        G: NetworkX DiGraph representing the model
    """
    import networkx as nx
    
    G = nx.DiGraph()
    
    # Add nodes (states)
    for state in model.z3_world_states:
        # Convert BitVec to string representation
        if hasattr(model.semantics, 'bitvec_to_substates'):
            state_str = model.semantics.bitvec_to_substates(state, model.N)
        else:
            # Fallback if the specific method isn't available
            from model_checker.utils import bitvec_to_substates
            state_str = bitvec_to_substates(state, model.N)
            
        attrs = {"world": True}
        G.add_node(state_str, **attrs)
    
    # Add the main/evaluation world with special attribute
    main_world = model.main_point["world"]
    if hasattr(model.semantics, 'bitvec_to_substates'):
        main_str = model.semantics.bitvec_to_substates(main_world, model.N)
    else:
        from model_checker.utils import bitvec_to_substates
        main_str = bitvec_to_substates(main_world, model.N)
    
    # Update the node or add it if it doesn't exist
    if main_str in G.nodes:
        G.nodes[main_str]['main'] = True
    else:
        G.add_node(main_str, world=True, main=True)
    
    # If we have potential accessibility relations in different theories 
    # (specific to modal logics)
    if hasattr(model, 'accessibility_relation'):
        # This would need to be customized based on how accessibility is represented
        # in each theory
        pass
        
    return G


def visualize_model(model, figsize=(10, 6)):
    """Visualize a model as a graph.
    
    Args:
        model: ModelStructure object
        figsize: Figure size
        
    Returns:
        fig: Matplotlib figure
    """
    import matplotlib.pyplot as plt
    import networkx as nx
    
    G = model_to_graph(model)
    
    fig, ax = plt.subplots(figsize=figsize)
    pos = nx.spring_layout(G)
    
    # Draw nodes
    world_nodes = [n for n, d in G.nodes(data=True) if d.get("world", False) and not d.get("main", False)]
    main_node = [n for n, d in G.nodes(data=True) if d.get("main", False)]
    other_nodes = [n for n in G.nodes() if n not in world_nodes and n not in main_node]
    
    # Main evaluation world
    if main_node:
        nx.draw_networkx_nodes(G, pos, nodelist=main_node, 
                              node_color="gold", node_size=700)
    
    # Regular world states
    nx.draw_networkx_nodes(G, pos, nodelist=world_nodes, 
                          node_color="lightblue", node_size=500)
    
    # Other states
    if other_nodes:
        nx.draw_networkx_nodes(G, pos, nodelist=other_nodes, 
                              node_color="lightgray", node_size=300)
    
    # Draw edges
    nx.draw_networkx_edges(G, pos, arrows=True)
    
    # Draw labels
    nx.draw_networkx_labels(G, pos)
    
    plt.axis("off")
    plt.tight_layout()
    
    return fig


class InteractiveModelExplorer:
    """Interactive model explorer for Jupyter notebooks."""
    
    def __init__(self, theory_name="default"):
        """Initialize the explorer with a theory.
        
        Args:
            theory_name: Name of the semantic theory to use
        """
        # Ensure environment is set up
        setup_environment()
        
        if not HAVE_IPYWIDGETS:
            raise ImportError(
                "ipywidgets is required for InteractiveModelExplorer. "
                "Install it with: pip install ipywidgets matplotlib networkx"
            )
            
        # Import necessary components now that environment is set up
        from model_checker import get_theory
        from model_checker.theory_lib import get_semantic_theories
        
        self.theory_name = theory_name
        # Fix the TypeError by getting semantic theories first
        semantic_theories = get_semantic_theories()
        self.theory = get_theory(theory_name, semantic_theories)
        self.settings = {
            'N': 3,
            'max_time': 5,
            'contingent': True,
            'non_empty': True,
            'print_constraints': False,
            'model': True  # Default to looking for a satisfying model
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
        # Ensure model_checker is properly imported
        setup_environment()
        
        try:
            from model_checker.theory_lib import get_semantic_theories
            theories = list(get_semantic_theories().keys())
            return theories
        except Exception as e:
            print(f"Error getting available theories: {e}")
            return [self.theory_name]
    
    def _update_setting(self, key, value):
        """Update a setting value."""
        self.settings[key] = value
    
    def _on_theory_change(self, change):
        """Handle theory change."""
        from model_checker import get_theory
        from model_checker.theory_lib import get_semantic_theories
        self.theory_name = change['new']
        semantic_theories = get_semantic_theories()
        self.theory = get_theory(self.theory_name, semantic_theories)
    
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
                from model_checker import BuildExample
                
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
                import traceback
                traceback.print_exc()
    
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
            clear_output()
            if view_type == 'Text Output':
                # Capture and display text output
                try:
                    output = capture_model_output(
                        self.model.model_structure, 
                        'print_all',
                        self.model.example_settings,
                        'interactive_check',
                        self.theory_name
                    )
                    html_output = convert_ansi_to_html(output)
                    display(HTML(html_output))
                except Exception as e:
                    print(f"Error displaying text output: {str(e)}")
                    import traceback
                    traceback.print_exc()
                
                # Show validity result
                try:
                    formula = self.formula_input.value
                    valid = self.model.check_result()
                    color = "green" if valid else "red"
                    display(HTML(
                        f"<h3>Formula: {formula}</h3>"
                        f"<p><b>Valid:</b> <span style='color:{color}'>{valid}</span></p>"
                    ))
                except Exception as e:
                    print(f"Error displaying validity result: {str(e)}")
                
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
                    import traceback
                    traceback.print_exc()
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
            
        try:
            output = capture_model_output(
                self.model.model_structure, 
                'print_all',
                self.model.example_settings,
                'interactive_check',
                self.theory_name
            )
            return convert_ansi_to_html(output)
        except Exception as e:
            return f"<p>Error getting output: {str(e)}</p>"


def check_formula_interactive(formula, theory_name="default", premises=None):
    """Create an interactive model explorer for a specific formula.
    
    Args:
        formula: The formula to check
        theory_name: The semantic theory to use
        premises: Optional list of premises
        
    Returns:
        Explorer widget
    """
    # Convert any Unicode operators to their LaTeX equivalents
    def normalize_formula(f):
        # First ensure we're dealing with a string
        if not isinstance(f, str):
            return f
        
        # The operators in the ModelChecker expect double backslashes in normal strings
        # We need to use double backslashes here since we're not using raw strings
        # Common Unicode to LaTeX mappings
        replacements = {
            '→': '\\\\rightarrow',  # This becomes \\rightarrow in memory
            '∧': '\\\\wedge',
            '∨': '\\\\vee',
            '¬': '\\\\neg',
            '□': '\\\\Box',
            '◇': '\\\\Diamond',
            '↔': '\\\\leftrightarrow',
            '≡': '\\\\equiv',
            '⊥': '\\\\bot',
            '⊤': '\\\\top'
        }
        
        # Add support for exclusion operators
        exclusion_replacements = {
            '\\exclude': '\\\\exclude',  # For exclusion theory
            '\\uniwedge': '\\\\uniwedge',
            '\\univee': '\\\\univee',
            '\\uniequiv': '\\\\uniequiv'
        }
        
        # First handle Unicode operators
        for unicode_op, latex_op in replacements.items():
            f = f.replace(unicode_op, latex_op)
            
        # Then handle exclusion operators if found in normal strings (not raw strings)
        if '\\e' in f and not f.startswith('r"') and not f.startswith("r'"):
            for ex_op, ex_latex_op in exclusion_replacements.items():
                f = f.replace(ex_op, ex_latex_op)
        
        return f
    
    # Helper function to ensure binary operators are properly parenthesized
    def ensure_parentheses(f):
        """Ensure binary operators are wrapped in parentheses."""
        binary_operators = [
            '\\rightarrow', '\\wedge', '\\vee', '\\leftrightarrow', '\\equiv',
            '\\uniwedge', '\\univee', '\\uniequiv'
        ]
        
        for op in binary_operators:
            if op in f and not (f.startswith('(') and f.endswith(')')):
                # If it contains a binary operator and isn't already parenthesized, wrap it
                f = f"({f})"
                break  # Only add one set of outer parentheses
        
        return f
    
    # Normalize the formula and premises
    formula = normalize_formula(formula)
    formula = ensure_parentheses(formula)
    
    if premises:
        # Make sure each premise has parentheses if it's an operator expression
        normalized_premises = []
        for p in premises:
            p = normalize_formula(p)
            p = ensure_parentheses(p)
            normalized_premises.append(p)
        premises = normalized_premises
        
    explorer = InteractiveModelExplorer(theory_name)
    explorer.formula_input.value = formula
    if premises:
        explorer.premises_input.value = "\n".join(premises)
    
    # Automatically check the formula
    explorer.check_button.click()
    
    # Return the explorer for further interaction
    return explorer


def check_formula(formula, theory_name="default", premises=None, settings=None):
    """Check a formula and return the result in a notebook-friendly way.
    
    This is a simpler alternative to the interactive explorer for quick checks.
    
    Args:
        formula: The formula to check
        theory_name: The semantic theory to use
        premises: Optional list of premises 
        settings: Optional dict of settings
        
    Returns:
        HTML display of the result
    """
    # Ensure environment is set up
    setup_environment()
    
    # Convert any Unicode operators to their LaTeX equivalents
    def normalize_formula(f):
        # First ensure we're dealing with a string
        if not isinstance(f, str):
            return f
        
        # The operators in the ModelChecker expect double backslashes in normal strings
        # We need to use double backslashes here since we're not using raw strings
        # Common Unicode to LaTeX mappings
        replacements = {
            '→': '\\\\rightarrow',  # This becomes \\rightarrow in memory
            '∧': '\\\\wedge',
            '∨': '\\\\vee',
            '¬': '\\\\neg',
            '□': '\\\\Box',
            '◇': '\\\\Diamond',
            '↔': '\\\\leftrightarrow',
            '≡': '\\\\equiv',
            '⊥': '\\\\bot',
            '⊤': '\\\\top'
        }
        
        # Add support for exclusion operators
        exclusion_replacements = {
            '\\exclude': '\\\\exclude',  # For exclusion theory
            '\\uniwedge': '\\\\uniwedge',
            '\\univee': '\\\\univee',
            '\\uniequiv': '\\\\uniequiv'
        }
        
        # First handle Unicode operators
        for unicode_op, latex_op in replacements.items():
            f = f.replace(unicode_op, latex_op)
            
        # Then handle exclusion operators if found in normal strings (not raw strings)
        if '\\e' in f and not f.startswith('r"') and not f.startswith("r'"):
            for ex_op, ex_latex_op in exclusion_replacements.items():
                f = f.replace(ex_op, ex_latex_op)
        
        return f
    
    # Helper function to ensure binary operators are properly parenthesized
    def ensure_parentheses(f):
        """Ensure binary operators are wrapped in parentheses."""
        binary_operators = [
            '\\rightarrow', '\\wedge', '\\vee', '\\leftrightarrow', '\\equiv',
            '\\uniwedge', '\\univee', '\\uniequiv'
        ]
        
        for op in binary_operators:
            if op in f and not (f.startswith('(') and f.endswith(')')):
                # If it contains a binary operator and isn't already parenthesized, wrap it
                f = f"({f})"
                break  # Only add one set of outer parentheses
        
        return f
        
    # Normalize the formula and premises
    formula = normalize_formula(formula)
    formula = ensure_parentheses(formula)
    
    if premises:
        # Make sure each premise has parentheses if it's an operator expression
        normalized_premises = []
        for p in premises:
            p = normalize_formula(p)
            p = ensure_parentheses(p)
            normalized_premises.append(p)
        premises = normalized_premises
    
    # Import dependencies
    from IPython.display import display, HTML
    from model_checker import BuildExample
    from model_checker.builder import BuildModule
    from model_checker.theory_lib import get_semantic_theories
    
    # Get semantic theories and then the specific theory
    semantic_theories = get_semantic_theories(theory_name)
    from model_checker.utils import get_theory
    
    # TODO: avoid special case by getting to the bottom of the issue
    # Handle special case for default theory which is named "Brast-McKie" in semantic_theories
    if theory_name == "default" and "default" not in semantic_theories and "Brast-McKie" in semantic_theories:
        theory = semantic_theories["Brast-McKie"]
    else:
        # If semantic_theories has only one entry, use that regardless of the name
        if len(semantic_theories) == 1:
            theory_key = list(semantic_theories.keys())[0]
            theory = semantic_theories[theory_key]
        else:
            # Otherwise, try to get the theory by name
            theory = get_theory(theory_name, semantic_theories)
    premises = premises or []
    _settings = {'N': 3, 'max_time': 5, 'model': True}
    if settings:
        _settings.update(settings)
    
    example = [premises, [formula], _settings]
    
    # Create a minimal BuildModule for the BuildExample with all required attributes
    build_module = type('BuildModule', (), {
        'module': type('Module', (), {'general_settings': {}}),
        'module_flags': type('Flags', (), {})
    })
    
    # Build and check the model
    model = BuildExample(build_module, theory, example)
    
    # Get the output
    output = capture_model_output(
        model.model_structure,
        'print_all',
        model.example_settings,
        'formula_check',
        theory_name
    )
    
    # Format and display
    valid = model.check_result()
    color = "green" if valid else "red"
    
    html_result = HTML(
        f"<h3>Formula: {formula}</h3>"
        f"<p><b>Valid:</b> <span style='color:{color}'>{valid}</span></p>"
        f"{convert_ansi_to_html(output)}"
    )
    
    return html_result
