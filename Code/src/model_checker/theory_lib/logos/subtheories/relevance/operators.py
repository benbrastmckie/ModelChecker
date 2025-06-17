"""
Relevance operators for hyperintensional logic.

This module implements relevance logical operators. Note that relevance
logic is handled within the constitutive operators module, so this
module simply imports the relevance operator from there.
"""

# Import the relevance operator from constitutive
from ..constitutive.operators import RelevanceOperator


def get_operators():
    """
    Get all relevance operators.
    
    Returns:
        dict: Dictionary mapping operator names to operator classes
    """
    return {
        "\\preceq": RelevanceOperator,
    }