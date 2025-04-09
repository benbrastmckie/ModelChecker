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

# Define the public API
__all__ = [
    # High-level functions
    "check_formula",
    "find_countermodel",
    "explore_formula",
    
    # UI Components
    "ModelExplorer",
    "FormulaChecker",
    
    # Display Functions
    "display_model",
    "display_formula_check",
    "display_countermodel",
    
    # Utilities
    "unicode_to_latex",
    "latex_to_unicode",
    "setup_environment",
    "get_available_theories",
    "load_examples",
]

# Public API - UI Components
from .interactive import ModelExplorer, FormulaChecker

# Public API - Display Functions
from .display import (
    display_model, 
    display_formula_check, 
    display_countermodel
)

# Public API - Utilities
from .unicode import unicode_to_latex, latex_to_unicode
from .environment import setup_environment, get_available_theories
from .utils import load_examples

# Simplified API functions
def check_formula(formula, theory_name="default", premises=None, settings=None):
    """Check if a formula is valid given premises."""
    return display_formula_check(formula, theory_name, premises, settings)

def find_countermodel(formula, theory_name="default", premises=None, settings=None):
    """Find a countermodel for a formula with optional premises."""
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
