"""
Display utilities for Jupyter notebooks.

This module provides tools for formatting and displaying ModelChecker
outputs in Jupyter notebooks, including HTML formatting and visualizations.
"""

import io
from contextlib import redirect_stdout
from typing import Dict, List, Any, Optional, Union

# These imports can be problematic in some environments, so we import them when needed
# from IPython.display import display, HTML, clear_output
# import matplotlib.pyplot as plt
# import networkx as nx

# Define high-level display functions
def display_model(*args, **kwargs):
    """Display a model visualization."""
    try:
        from IPython.display import display, HTML
        # Implementation goes here
        return HTML("<div>Model display (placeholder)</div>")
    except ImportError:
        raise ImportError("IPython is required for this feature. Install with 'pip install model-checker[jupyter]'")

def display_formula_check(formula, theory_name="default", premises=None, settings=None):
    """Display results of checking if a formula is valid given premises."""
    try:
        from IPython.display import display, HTML
        # Implementation goes here
        result = {"valid": True, "formula": formula, "theory": theory_name}
        return HTML(f"<div>Formula check: {formula} in {theory_name} (placeholder)</div>")
    except ImportError:
        raise ImportError("IPython is required for this feature. Install with 'pip install model-checker[jupyter]'")

def display_countermodel(formula, theory_name="default", premises=None, settings=None):
    """Display a countermodel for a formula with optional premises."""
    try:
        from IPython.display import display, HTML
        # Implementation goes here
        return HTML(f"<div>Countermodel for: {formula} in {theory_name} (placeholder)</div>")
    except ImportError:
        raise ImportError("IPython is required for this feature. Install with 'pip install model-checker[jupyter]'")


def convert_ansi_to_html(ansi_text: str) -> str:
    """
    Convert ANSI terminal output to HTML for Jupyter notebook display.
    
    Args:
        ansi_text: Text containing ANSI color codes
        
    Returns:
        str: HTML formatted text with ANSI codes converted to CSS styles
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


def capture_output(obj: Any, method_name: str, *args, **kwargs) -> str:
    """
    Capture stdout output from an object method.
    
    Args:
        obj: The object to call the method on
        method_name: Name of the method to call
        *args, **kwargs: Arguments to pass to the method
        
    Returns:
        str: Captured stdout output
    """
    output_buffer = io.StringIO()
    with redirect_stdout(output_buffer):
        method = getattr(obj, method_name)
        method(*args, **kwargs)
    return output_buffer.getvalue()


def display_model(model: Any, visualization_type: str = "text", show_details: bool = True) -> Any:
    """
    Display a model with text or graph visualization.
    
    Args:
        model: Model object to display. Can be:
             - BuildExample instance
             - ModelStructure instance 
             - An object with model_structure attribute
             - A custom wrapper with model_structure and example_settings attributes
        visualization_type: Type of visualization ('text' or 'graph')
        show_details: Whether to show detailed model information
        
    Returns:
        IPython.display.HTML: HTML representation of the model
    """
    from IPython.display import display, HTML
    from .adapters import TheoryAdapter
    import inspect
    
    if model is None:
        return HTML("<p>No model available</p>")
    
    # Extract model_structure and example_settings based on the type of model
    if hasattr(model, 'model_structure'):
        # Case 1: Model has a model_structure attribute (like BuildExample or wrapper)
        model_structure = model.model_structure
        example_settings = getattr(model, 'example_settings', {})
        theory_name = getattr(model, 'theory_name', "default")
    elif hasattr(model, 'print_all') and inspect.ismethod(model.print_all):
        # Case 2: Model is a ModelStructure itself
        model_structure = model
        # Try to get settings from the model structure
        example_settings = getattr(model, 'settings', {})
        theory_name = "default"
    else:
        # Unknown model type
        return HTML(f"<p>Unsupported model type: {type(model).__name__}. "
                   "Expected BuildExample, ModelStructure, or an object with model_structure attribute.</p>")
    
    if not model_structure:
        return HTML("<p>No model structure available</p>")
    
    # Get the appropriate adapter
    adapter = TheoryAdapter.get_adapter(theory_name)
    
    if visualization_type == "text":
        # Text-based visualization
        try:
            output = capture_output(
                model_structure, 
                'print_all',
                example_settings,
                "model",
                theory_name
            )
            return HTML(convert_ansi_to_html(output))
        except Exception as e:
            return HTML(f"<p>Error displaying text output: {str(e)}</p>")
            
    elif visualization_type == "graph":
        # Graph-based visualization
        try:
            fig = _create_graph_visualization(model_structure, adapter)
            display(fig)
            import matplotlib.pyplot as plt
            plt.close(fig)
            
            # Show key information as HTML
            if show_details:
                return HTML(adapter.format_model(model))
            return HTML("")
        except Exception as e:
            return HTML(f"<p>Error creating visualization: {str(e)}</p>")
    else:
        return HTML(f"<p>Unsupported visualization type: {visualization_type}</p>")


def _create_graph_visualization(model: Any, adapter: Any) -> 'plt.Figure': # type: ignore
    """
    Create a graph visualization of a model.
    
    Args:
        model: ModelStructure object
        adapter: TheoryAdapter instance
        
    Returns:
        plt.Figure: Matplotlib figure with graph visualization
    """
    import matplotlib.pyplot as plt
    import networkx as nx
    
    # Use the adapter to get a graph representation
    G = adapter.model_to_graph(model)
    
    fig, ax = plt.subplots(figsize=(10, 6))
    
    # Position nodes using spring layout
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
    if world_nodes:
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


def display_formula_check(formula: str, 
                          theory_name: str = "default", 
                          premises: Optional[List[str]] = None, 
                          settings: Optional[Dict[str, Any]] = None) -> 'HTML': # type: ignore
    """
    Display formula checking results.
    
    Args:
        formula: The formula to check
        theory_name: The semantic theory to use
        premises: Optional list of premises
        settings: Optional dict of settings
        
    Returns:
        IPython.display.HTML: HTML display of the result
    """
    from IPython.display import HTML
    from .unicode import normalize_formula
    
    try:
        from model_checker import BuildExample, get_theory
        from model_checker.theory_lib import get_semantic_theories
    except ImportError:
        from .environment import setup_environment
        setup_environment()
        from model_checker import BuildExample, get_theory
    
    try:
        # Normalize formula and premises
        formula = normalize_formula(formula)
        if premises:
            premises = [normalize_formula(p) for p in premises]
        else:
            premises = []
            
        # Use default settings if not provided
        if not settings:
            settings = {'N': 3, 'max_time': 5, 'model': True, 'expectation': True}
        else:
            # Make sure we have the minimal required settings
            if 'N' not in settings:
                settings['N'] = 3
            if 'max_time' not in settings:
                settings['max_time'] = 5
            if 'expectation' not in settings:
                settings['expectation'] = True
        
        # Get semantic theories and then the specific theory
        semantic_theories = get_semantic_theories(theory_name)
        
        # Handle special case for default theory which is named "Brast-McKie" in some older versions
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
        
        example = [premises, [formula], settings]
        
        # Create a minimal BuildModule for the BuildExample with all required attributes
        build_module = type('BuildModule', (), {
            'module': type('Module', (), {'general_settings': {}}),
            'module_flags': type('Flags', (), {})
        })
        
        # Build and check the model
        model = BuildExample(build_module, theory, example)
        model.theory_name = theory_name  # Add theory_name attribute for later use
        
        # Get the output
        output = capture_output(
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
    except Exception as e:
        # If anything goes wrong, show an error message
        return HTML(f"<p>Error checking formula: {str(e)}</p>")


def display_countermodel(formula: str, 
                         theory_name: str = "default", 
                         premises: Optional[List[str]] = None, 
                         settings: Optional[Dict[str, Any]] = None) -> 'HTML': # type: ignore
    """
    Display a countermodel for a formula if one exists.
    
    Args:
        formula: The formula to check
        theory_name: The semantic theory to use
        premises: Optional list of premises
        settings: Optional dict of settings
        
    Returns:
        IPython.display.HTML: HTML display of the result
    """
    from IPython.display import HTML, display
    
    # Make sure settings includes model=True to find a countermodel
    if not settings:
        settings = {'N': 3, 'max_time': 5, 'model': True, 'expectation': False}
    else:
        settings = settings.copy()  # Make a copy to avoid modifying the original
        settings['model'] = True
        settings['expectation'] = False
    
    # Use display_formula_check with adjusted settings
    result = display_formula_check(formula, theory_name, premises, settings)
    
    # Extract the model from the BuildExample for visualization
    try:
        from model_checker import BuildExample, get_theory
        from model_checker.theory_lib import get_semantic_theories
        
        # Create the model again to get access to it
        semantic_theories = get_semantic_theories(theory_name)
        
        if theory_name == "default" and "default" not in semantic_theories and "Brast-McKie" in semantic_theories:
            theory = semantic_theories["Brast-McKie"]
        else:
            if len(semantic_theories) == 1:
                theory_key = list(semantic_theories.keys())[0]
                theory = semantic_theories[theory_key]
            else:
                theory = get_theory(theory_name, semantic_theories)
        
        # Create a minimal BuildModule for the BuildExample
        build_module = type('BuildModule', (), {
            'module': type('Module', (), {'general_settings': {}}),
            'module_flags': type('Flags', (), {})
        })
        
        example = [premises or [], [formula], settings]
        model = BuildExample(build_module, theory, example)
        
        # Check if we found a countermodel
        valid = model.check_result()
        
        if not valid:
            # Show the graph visualization below the text result
            display(result)
            
            # Return the graph visualization
            return display_model(model, visualization_type="graph")
    except Exception as e:
        # If visualization fails, just return the text result
        pass
    
    return result
