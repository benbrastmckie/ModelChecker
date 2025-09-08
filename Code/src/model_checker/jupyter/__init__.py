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

import importlib.util
import warnings

# Define core utilities (these don't require optional dependencies)
from .unicode import unicode_to_latex, latex_to_unicode
from .environment import setup_environment, get_available_theories
from .utils import load_examples
from .builder_utils import create_build_example, build_and_check
from .exceptions import (
    JupyterError,
    JupyterEnvironmentError,
    JupyterDependencyError,
    JupyterWidgetError,
    JupyterVisualizationError,
    JupyterFormulaError,
    JupyterTheoryError,
    JupyterTimeoutError
)

# Base API that's always available
__all__ = [
    "unicode_to_latex",
    "latex_to_unicode",
    "setup_environment",
    "get_available_theories",
    "load_examples",
    "create_build_example",
    "build_and_check",
    # Exceptions
    "JupyterError",
    "JupyterEnvironmentError",
    "JupyterDependencyError",
    "JupyterWidgetError",
    "JupyterVisualizationError",
    "JupyterFormulaError",
    "JupyterTheoryError",
    "JupyterTimeoutError",
]

# Function to check if dependencies are available
def has_jupyter_dependencies():
    """Check if Jupyter-related dependencies are available."""
    deps = ["ipywidgets", "matplotlib", "networkx"]
    for dep in deps:
        if importlib.util.find_spec(dep) is None:
            return False
    return True

# Stub functions that will be replaced if dependencies are available
def check_formula(*args, **kwargs):
    """Check if a formula is valid given premises."""
    raise JupyterDependencyError("ipywidgets", "check_formula")

def find_countermodel(*args, **kwargs):
    """Find a countermodel for a formula with optional premises."""
    raise JupyterDependencyError("ipywidgets", "find_countermodel")

def explore_formula(*args, **kwargs):
    """Create an interactive explorer for a specific formula."""
    raise JupyterDependencyError("ipywidgets", "explore_formula")

def display_model(*args, **kwargs):
    """Display a model visualization."""
    raise JupyterDependencyError("matplotlib", "display_model")

def display_formula_check(*args, **kwargs):
    """Display results of checking a formula."""
    raise JupyterDependencyError("IPython", "display_formula_check")

def display_countermodel(*args, **kwargs):
    """Display a countermodel."""
    raise JupyterDependencyError("IPython", "display_countermodel")

class FormulaChecker:
    """Formula checking widget (stub class)."""
    def __init__(self, *args, **kwargs):
        raise JupyterDependencyError("ipywidgets", "FormulaChecker")

# Add stub functions to API
__all__.extend([
    "check_formula",
    "find_countermodel",
    "explore_formula",
    "display_model",
    "display_formula_check",
    "display_countermodel",
    "has_jupyter_dependencies",
    "FormulaChecker"
])

# Import implementations if dependencies are available
if has_jupyter_dependencies():
    from .display import display_model, display_formula_check, display_countermodel
    from .interactive import ModelExplorer, check_formula, find_countermodel, explore_formula, FormulaChecker
    
    # Add ModelExplorer and FormulaChecker to API
    __all__.extend(["ModelExplorer", "FormulaChecker"])
