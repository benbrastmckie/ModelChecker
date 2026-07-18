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

    Note: The relevance operator (\\preceq) is provided by the constitutive subtheory.
    This module exists for organizational purposes but doesn't define any unique operators.

    Returns:
        dict: Dictionary mapping operator names to operator classes
    """
    return {
        # No operators defined here - relevance operators are provided by constitutive subtheory
    }