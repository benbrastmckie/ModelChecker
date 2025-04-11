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

"""
ModelChecker Jupyter integration package.

This package provides tools for using ModelChecker in Jupyter notebooks
with interactive visualizations and simplified interfaces.
"""

import importlib.util
import warnings

# Define core utilities (these don't require optional dependencies)
from .unicode import unicode_to_latex, latex_to_unicode
from .environment import setup_environment, get_available_theories
from .utils import load_examples

# Base API that's always available
__all__ = [
    "unicode_to_latex",
    "latex_to_unicode",
    "setup_environment",
    "get_available_theories",
    "load_examples",
]

# Function to check if dependencies are available
def has_jupyter_dependencies():
    """Check if Jupyter-related dependencies are available."""
    deps = ["ipywidgets", "matplotlib", "networkx"]
    for dep in deps:
        if importlib.util.find_spec(dep) is None:
            return False
    return True

# Define stub functions for missing features
def missing_dependencies_error(feature_name):
    """Raise error for missing dependencies."""
    raise ImportError(
        f"{feature_name} requires additional dependencies. "
        "Install with 'pip install model-checker[jupyter]' to enable this feature."
    )

# Stub functions that will be replaced if dependencies are available
def check_formula(*args, **kwargs):
    """Check if a formula is valid given premises."""
    missing_dependencies_error("check_formula")

def find_countermodel(*args, **kwargs):
    """Find a countermodel for a formula with optional premises."""
    missing_dependencies_error("find_countermodel")

def explore_formula(*args, **kwargs):
    """Create an interactive explorer for a specific formula."""
    missing_dependencies_error("explore_formula")

def display_model(*args, **kwargs):
    """Display a model visualization."""
    missing_dependencies_error("display_model")

def display_formula_check(*args, **kwargs):
    """Display results of checking a formula."""
    missing_dependencies_error("display_formula_check")

def display_countermodel(*args, **kwargs):
    """Display a countermodel."""
    missing_dependencies_error("display_countermodel")

class FormulaChecker:
    """Formula checking widget (stub class)."""
    def __init__(self, *args, **kwargs):
        missing_dependencies_error("FormulaChecker")

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
