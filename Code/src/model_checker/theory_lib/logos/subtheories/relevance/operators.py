"""
Relevance operators for hyperintensional logic.

This module implements relevance logical operators. Note that relevance
logic is handled within the constitutive operators module, so this
module simply imports the relevance operator from there.
"""

from ..constitutive.operators import RelevanceOperator




# Import the relevance operator from constitutive


def get_operators():
    """
    Get all relevance operators.
    
    Returns:
        dict: Dictionary mapping operator names to operator classes
    """
    return {
        "\\preceq": RelevanceOperator,
    }