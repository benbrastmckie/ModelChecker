"""
Interactive UI components for Jupyter notebooks.

This module provides widget-based interfaces for interacting with
ModelChecker in Jupyter notebooks.
"""

from typing import Dict, List, Any, Optional, Union, Callable
import os
import sys

try:
    import ipywidgets as widgets
    from IPython.display import display, clear_output, HTML
    HAVE_IPYWIDGETS = True
except ImportError:
    HAVE_IPYWIDGETS = False

# Import UI builders if available
if HAVE_IPYWIDGETS:
    from .ui_builders import ModelExplorerUIBuilder, FormulaCheckerUIBuilder

# Define high-level utility functions
def check_formula(formula, theory_name="logos", premises=None, settings=None):
    """Check if a formula is valid given premises."""
    if not HAVE_IPYWIDGETS:
        raise ImportError(
            "ipywidgets is required for interactive features. "
            "Install with: pip install model-checker[jupyter]"
        )
    
    try:
        from IPython.display import display, HTML
        from model_checker.jupyter.builder_utils import create_build_example
        from model_checker.theory_lib import logos, exclusion
        
        # Get the appropriate theory
        if theory_name == "logos":
            theory = logos.get_theory()
        elif theory_name == "exclusion":
            theory = {
                'semantics': exclusion.WitnessSemantics,
                'proposition': exclusion.WitnessProposition,
                'model': exclusion.WitnessStructure,
                'operators': exclusion.witness_operators
            }
        else:
            # Fall back to logos for unsupported theories
            theory = logos.get_theory()
            theory_name = "logos"
        
        # Set up default settings
        if settings is None:
            settings = {'N': 3, 'max_time': 5}
        
        # Set up premises
        if premises is None:
            premises = []
        elif isinstance(premises, str):
            premises = [premises]
        
        # Create example and check
        example = [premises, [formula], settings]
        model = create_build_example("jupyter_check", theory, example)
        
        # Get result
        valid = model.check_result()
        
        # Create HTML output
        color = "green" if valid else "red"
        premises_text = " with premises: " + ", ".join(premises) if premises else ""
        
        html_output = f"""
        <div style="border: 1px solid #ddd; padding: 10px; margin: 10px 0;">
            <h3>Formula Check Result</h3>
            <p><strong>Theory:</strong> {theory_name}</p>
            <p><strong>Formula:</strong> {formula}{premises_text}</p>
            <p><strong>Result:</strong> <span style='color:{color}; font-weight:bold'>{'Valid' if valid else 'Invalid'}</span></p>
        </div>
        """
        
        return HTML(html_output)
        
    except ImportError:
        raise ImportError("IPython is required for this feature. Install with 'pip install model-checker[jupyter]'")
    except Exception as e:
        return HTML(f"<div style='color: red;'>Error checking formula: {str(e)}</div>")

def find_countermodel(formula, theory_name="logos", premises=None, settings=None):
    """Find a countermodel for a formula with optional premises."""
    if not HAVE_IPYWIDGETS:
        raise ImportError(
            "ipywidgets is required for interactive features. "
            "Install with: pip install model-checker[jupyter]"
        )
    
    try:
        from IPython.display import display, HTML
        from model_checker.jupyter.builder_utils import create_build_example
        from model_checker.theory_lib import logos, exclusion
        from io import StringIO
        
        # Get the appropriate theory
        if theory_name == "logos":
            theory = logos.get_theory()
        elif theory_name == "exclusion":
            theory = {
                'semantics': exclusion.WitnessSemantics,
                'proposition': exclusion.WitnessProposition,
                'model': exclusion.WitnessStructure,
                'operators': exclusion.witness_operators
            }
        else:
            # Fall back to logos for unsupported theories
            theory = logos.get_theory()
            theory_name = "logos"
        
        # Set up default settings for countermodel search
        if settings is None:
            settings = {'N': 3, 'max_time': 5, 'expectation': False}  # Expect invalid for countermodel
        else:
            settings = settings.copy()
            settings['expectation'] = False  # Override to search for countermodel
        
        # Set up premises
        if premises is None:
            premises = []
        elif isinstance(premises, str):
            premises = [premises]
        
        # Create example and check for countermodel
        example = [premises, [formula], settings]
        model = create_build_example("jupyter_countermodel", theory, example)
        
        # Get result
        valid = model.check_result()
        
        # Create HTML output
        if not valid:
            # Found a countermodel - capture model output
            output = StringIO()
            try:
                model.model_structure.print_all(output=output)
                model_output = output.getvalue()
            except:
                model_output = "Model details unavailable"
            
            premises_text = " with premises: " + ", ".join(premises) if premises else ""
            
            html_output = f"""
            <div style="border: 1px solid #ddd; padding: 10px; margin: 10px 0;">
                <h3>Countermodel Found</h3>
                <p><strong>Theory:</strong> {theory_name}</p>
                <p><strong>Formula:</strong> {formula}{premises_text}</p>
                <p><strong>Result:</strong> <span style='color:red; font-weight:bold'>Invalid (countermodel exists)</span></p>
                <details>
                    <summary>Show Countermodel</summary>
                    <pre style="background: #f5f5f5; padding: 10px; margin-top: 10px;">{model_output}</pre>
                </details>
            </div>
            """
        else:
            # No countermodel found - formula is valid
            premises_text = " with premises: " + ", ".join(premises) if premises else ""
            
            html_output = f"""
            <div style="border: 1px solid #ddd; padding: 10px; margin: 10px 0;">
                <h3>No Countermodel</h3>
                <p><strong>Theory:</strong> {theory_name}</p>
                <p><strong>Formula:</strong> {formula}{premises_text}</p>
                <p><strong>Result:</strong> <span style='color:green; font-weight:bold'>Valid (no countermodel found)</span></p>
            </div>
            """
        
        return HTML(html_output)
        
    except ImportError:
        raise ImportError("IPython is required for this feature. Install with 'pip install model-checker[jupyter]'")
    except Exception as e:
        return HTML(f"<div style='color: red;'>Error searching for countermodel: {str(e)}</div>")

def explore_formula(formula, theory_name="logos", premises=None, settings=None):
    """Create an interactive explorer for a specific formula."""
    if not HAVE_IPYWIDGETS:
        raise ImportError(
            "ipywidgets is required for interactive features. "
            "Install with: pip install model-checker[jupyter]"
        )
    explorer = ModelExplorer(theory_name)
    
    # These methods should be defined in the ModelExplorer class
    if hasattr(explorer, 'set_formula'):
        explorer.set_formula(formula)
        
    if premises and hasattr(explorer, 'set_premises'):
        explorer.set_premises(premises)
        
    if settings and hasattr(explorer, 'update_settings'):
        explorer.update_settings(settings)
        
    if hasattr(explorer, 'check_formula'):
        explorer.check_formula()
        
    return explorer


class ModelExplorer:
    """Interactive model explorer for Jupyter notebooks."""
    
    def __init__(self, theory_name: str = "default"):
        """
        Initialize with a theory.
        
        Args:
            theory_name: Name of the semantic theory to use
        """
        # Check for required dependencies
        if not HAVE_IPYWIDGETS:
            raise ImportError(
                "ipywidgets is required for ModelExplorer. "
                "Install it with: pip install ipywidgets matplotlib networkx"
            )
        
        from .environment import setup_environment, get_available_theories
        
        # Ensure environment is set up
        env_status = setup_environment()
        if env_status["status"] != "success":
            print(f"Warning: {env_status['message']}")
        
        # Import dependencies now that environment is set up
        from model_checker import get_theory
        from model_checker.theory_lib import get_semantic_theories
        
        self.theory_name = theory_name
        self.available_theories = get_available_theories()
        
        # Get semantic theories from the specified theory
        semantic_theories = get_semantic_theories(theory_name)
        
        # Handle special case for default theory
        if theory_name == "default" and "default" not in semantic_theories and "Brast-McKie" in semantic_theories:
            self.theory = semantic_theories["Brast-McKie"]
        else:
            if len(semantic_theories) == 1:
                theory_key = list(semantic_theories.keys())[0]
                self.theory = semantic_theories[theory_key]
            else:
                self.theory = get_theory(theory_name, semantic_theories)
        
        self.settings = {
            'N': 3,
            'max_time': 5,
            'contingent': True,
            'non_empty': True,
            'print_constraints': False,
            'model': True,  # Default to looking for a satisfying model
            'expectation': True  # Default to expecting valid formulas
        }
        
        self.model = None
        self._build_ui()
    
    def _build_ui(self):
        """Build the interactive UI components using the UI builder."""
        builder = ModelExplorerUIBuilder(self)
        self.ui = builder.build_main_ui()
    
    
    def _update_setting(self, key: str, value: Any):
        """
        Update a setting value.
        
        Args:
            key: Setting key
            value: New value
        """
        self.settings[key] = value
    
    def _on_theory_change(self, change):
        """
        Handle theory change.
        
        Args:
            change: Change event
        """
        from model_checker import get_theory
        from model_checker.theory_lib import get_semantic_theories
        
        self.theory_name = change['new']
        
        # Get semantic theories from the specified theory
        semantic_theories = get_semantic_theories(self.theory_name)
        
        # Try to get the specified theory, or handle "default" special case
        if self.theory_name == "default" and "default" not in semantic_theories and "Brast-McKie" in semantic_theories:
            self.theory = semantic_theories["Brast-McKie"]
        else:
            if len(semantic_theories) == 1:
                theory_key = list(semantic_theories.keys())[0]
                self.theory = semantic_theories[theory_key]
            else:
                self.theory = get_theory(self.theory_name, semantic_theories)
    
    def _on_viz_change(self, change):
        """
        Handle visualization change.
        
        Args:
            change: Change event
        """
        if self.model is not None:
            self._display_result()
    
    def _on_check_click(self, button):
        """
        Handle check button click.
        
        Args:
            button: Button widget
        """
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
                # Create the model using the helper function
                from model_checker.jupyter.builder_utils import create_build_example
                
                # Build and check the model
                self.model = create_build_example('jupyter_interactive', self.theory, example)
                self.model.theory_name = self.theory_name  # Add theory_name attribute for later use
                self.next_model_button.disabled = False
                
                # Display the result
                self._display_result()
                
            except Exception as e:
                print(f"Error checking formula: {str(e)}")
                import traceback
                traceback.print_exc()
    
    def _on_next_model_click(self, button):
        """
        Handle next model button click.
        
        Args:
            button: Button widget
        """
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
            
            # Import display module functions
            from .display import capture_output, convert_ansi_to_html, display_model
            
            if view_type == 'Text Output':
                # Capture and display text output
                try:
                    output = capture_output(
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
                    display_model(self.model, visualization_type="graph")
                    
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
    
    def get_output(self) -> str:
        """
        Get the current model output as HTML.
        
        Returns:
            str: HTML representation of the current model output
        """
        from .display import capture_output, convert_ansi_to_html
        
        if self.model is None:
            return "<p>No model has been created yet.</p>"
            
        try:
            output = capture_output(
                self.model.model_structure, 
                'print_all',
                self.model.example_settings,
                'interactive_check',
                self.theory_name
            )
            return convert_ansi_to_html(output)
        except Exception as e:
            return f"<p>Error getting output: {str(e)}</p>"
    
    def set_formula(self, formula: str):
        """
        Set the formula to check.
        
        Args:
            formula: Formula string
        """
        from .unicode import normalize_formula
        self.formula_input.value = normalize_formula(formula)
    
    def set_premises(self, premises: Union[List[str], str]):
        """
        Set the premises.
        
        Args:
            premises: List of premise strings or a single string
        """
        from .unicode import normalize_formula
        
        if isinstance(premises, list):
            self.premises_input.value = "\n".join(
                [normalize_formula(p) for p in premises]
            )
        else:
            self.premises_input.value = normalize_formula(premises)
    
    def update_settings(self, settings: Dict[str, Any]):
        """
        Update model settings.
        
        Args:
            settings: Dictionary of settings to update
        """
        for key, value in settings.items():
            if key in self.settings:
                self.settings[key] = value
                
                # Update UI controls if they exist
                if key == 'N' and hasattr(self, 'n_slider'):
                    self.n_slider.value = value
                elif key == 'max_time' and hasattr(self, 'max_time_slider'):
                    self.max_time_slider.value = value
                elif key == 'contingent' and hasattr(self, 'contingent_checkbox'):
                    self.contingent_checkbox.value = value
                elif key == 'non_empty' and hasattr(self, 'non_empty_checkbox'):
                    self.non_empty_checkbox.value = value
                elif key == 'print_constraints' and hasattr(self, 'print_constraints_checkbox'):
                    self.print_constraints_checkbox.value = value
                elif key == 'expectation' and hasattr(self, 'expectation_selector'):
                    self.expectation_selector.value = value
    
    def check_formula(self):
        """Check the current formula."""
        self.check_button.click()
    
    def find_next_model(self):
        """Find the next model satisfying the formula."""
        self.next_model_button.click()


class FormulaChecker:
    """Simple formula checking widget."""
    
    def __init__(self, theory_name: str = "default"):
        """
        Initialize with a theory.
        
        Args:
            theory_name: Name of the theory
        """
        # Check for required dependencies
        if not HAVE_IPYWIDGETS:
            raise ImportError(
                "ipywidgets is required for FormulaChecker. "
                "Install it with: pip install ipywidgets"
            )
        
        from .environment import setup_environment, get_available_theories
        
        # Ensure environment is set up
        env_status = setup_environment()
        if env_status["status"] != "success":
            print(f"Warning: {env_status['message']}")
        
        self.theory_name = theory_name
        self.available_theories = get_available_theories()
        
        self.settings = {
            'N': 3,
            'max_time': 5,
            'expectation': True
        }
        
        self._build_ui()
    
    def _build_ui(self):
        """Build the UI components using the UI builder."""
        builder = FormulaCheckerUIBuilder(self)
        self.ui = builder.build_main_ui()
    
    def _on_check_click(self, button):
        """
        Handle check button click.
        
        Args:
            button: Button widget
        """
        with self.output_area:
            clear_output()
            
            # Get formula and premises
            formula = self.formula_input.value.strip()
            premises = [p.strip() for p in self.premises_input.value.split('\n') if p.strip()]
            
            if not formula:
                print("Please enter a formula to check.")
                return
            
            # Get theory name
            theory_name = self.theory_selector.value
            
            # Check the formula
            from .display import display_formula_check
            result = display_formula_check(formula, theory_name, premises, self.settings)
            display(result)
    
    def display(self):
        """Display the checker UI."""
        display(self.ui)
    
    def set_formula(self, formula: str):
        """
        Set the formula to check.
        
        Args:
            formula: Formula string
        """
        from .unicode import normalize_formula
        self.formula_input.value = normalize_formula(formula)
    
    def set_premises(self, premises: Union[List[str], str]):
        """
        Set the premises.
        
        Args:
            premises: List of premise strings or a single string
        """
        from .unicode import normalize_formula
        
        if isinstance(premises, list):
            self.premises_input.value = "\n".join(
                [normalize_formula(p) for p in premises]
            )
        else:
            self.premises_input.value = normalize_formula(premises)
    
    def check_formula(self):
        """Check the current formula."""
        self.check_button.click()
