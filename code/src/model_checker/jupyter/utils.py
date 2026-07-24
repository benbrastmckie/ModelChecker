"""
Shared utilities for Jupyter integration.

This module provides common utility functions used across the 
Jupyter integration package.
"""

import importlib
import inspect
import sys
import os
from typing import Dict, List, Any, Optional, Tuple, Union


def load_examples(theory_name: str, example_prefix: Optional[str] = None) -> Dict[str, List]:
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


def get_example_categories(examples: Dict[str, List]) -> Dict[str, Dict[str, List]]:
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


def format_settings(settings: Dict[str, Any]) -> str:
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


def get_theory_details(theory_name: str) -> Dict[str, Any]:
    """
    Get details about a theory implementation.
    
    Args:
        theory_name: Name of the theory
        
    Returns:
        dict: Dictionary with theory details
    """
    try:
        # Import the theory module
        theory_module = importlib.import_module(f"model_checker.theory_lib.{theory_name}")
        
        # Get README if available
        readme_path = os.path.join(os.path.dirname(theory_module.__file__), "README.md")
        readme_content = None
        if os.path.exists(readme_path):
            with open(readme_path, "r") as f:
                readme_content = f.read()
        
        # Get available examples
        examples = load_examples(theory_name)
        
        # Get theory components
        components = {}
        for name in dir(theory_module):
            if name.startswith("__"):
                continue
                
            obj = getattr(theory_module, name)
            if inspect.isclass(obj):
                components[name] = {
                    "type": "class",
                    "doc": obj.__doc__
                }
            elif inspect.isfunction(obj):
                components[name] = {
                    "type": "function",
                    "doc": obj.__doc__
                }
        
        return {
            "name": theory_name,
            "readme": readme_content,
            "examples_count": len(examples),
            "examples": list(examples.keys()),
            "components": components,
            "module": theory_module.__name__,
            "path": theory_module.__file__
        }
        
    except ImportError:
        return {
            "name": theory_name,
            "error": f"Could not import theory module: model_checker.theory_lib.{theory_name}"
        }


def sanitize_formula(formula: str) -> str:
    """
    Sanitize a formula for HTML display by escaping special characters.
    
    Args:
        formula: Formula string
        
    Returns:
        str: Sanitized formula
    """
    # Replace HTML special characters
    return (formula.replace("&", "&amp;")
                  .replace("<", "&lt;")
                  .replace(">", "&gt;")
                  .replace('"', "&quot;")
                  .replace("'", "&#39;"))


def extract_premise_conclusion(example: List) -> Tuple[List[str], List[str]]:
    """
    Extract premises and conclusions from an example.
    
    Args:
        example: Example list from examples module
        
    Returns:
        tuple: (premises, conclusions)
    """
    if not isinstance(example, list) or len(example) < 3:
        return ([], [])
    
    return (example[0], example[1])


def merge_settings(default_settings: Dict[str, Any], 
                   user_settings: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """
    Merge default settings with user-provided settings.
    
    Args:
        default_settings: Default settings
        user_settings: User-provided settings to override defaults
        
    Returns:
        dict: Merged settings
    """
    if not user_settings:
        return default_settings.copy()
    
    result = default_settings.copy()
    result.update(user_settings)
    return result