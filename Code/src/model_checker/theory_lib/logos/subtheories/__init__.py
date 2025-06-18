"""
Subtheory discovery and loading system for logos theory.

This module provides the registry of all available subtheories and utilities
for discovering and loading them dynamically.

API:
    AVAILABLE_SUBTHEORIES: List of all available subtheory names
    get_subtheory_module(name): Load a specific subtheory module
    list_subtheories(): Get list of available subtheory names with descriptions
"""

import importlib

AVAILABLE_SUBTHEORIES = [
    'extensional',
    'modal', 
    'constitutive',
    'counterfactual',
    'relevance'
]

SUBTHEORY_DESCRIPTIONS = {
    'extensional': 'Truth-functional operators (¬,∧,∨,→,↔,⊤,⊥)',
    'modal': 'Necessity and possibility operators (□,◇)',
    'constitutive': 'Ground, essence, and identity operators (≡,≤,⊑,≼)',
    'counterfactual': 'Counterfactual conditional operators (□→,◇→)',
    'relevance': 'Content-sensitive relevance operators'
}

def get_subtheory_module(name):
    """
    Load a specific subtheory module.
    
    Args:
        name: Name of the subtheory to load
        
    Returns:
        The loaded subtheory module
        
    Raises:
        ImportError: If subtheory cannot be loaded
        ValueError: If subtheory name is not available
    """
    if name not in AVAILABLE_SUBTHEORIES:
        raise ValueError(f"Unknown subtheory: {name}. Available: {AVAILABLE_SUBTHEORIES}")
    
    module_path = f"model_checker.theory_lib.logos.subtheories.{name}"
    return importlib.import_module(module_path)

def list_subtheories():
    """
    Get list of available subtheory names with descriptions.
    
    Returns:
        dict: Dictionary mapping subtheory names to descriptions
    """
    return SUBTHEORY_DESCRIPTIONS.copy()

__all__ = [
    'AVAILABLE_SUBTHEORIES',
    'SUBTHEORY_DESCRIPTIONS', 
    'get_subtheory_module',
    'list_subtheories'
]