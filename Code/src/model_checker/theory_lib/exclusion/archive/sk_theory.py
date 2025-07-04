"""
Complete SK Theory Module for Exclusion Semantics

This module provides a complete theory implementation using SK operators
with correct recursive semantics.
"""

from model_checker.theory_lib.exclusion.sk_exclusion import (
    SK_ExclusionOperator,
    SK_UniAndOperator,
    SK_UniOrOperator,
    SK_UniIdentityOperator,
)
from model_checker.theory_lib.exclusion.sk_semantic import SKExclusionSemantics
from model_checker.theory_lib.exclusion.semantic import (
    UnilateralProposition,
    ExclusionStructure,
)
from model_checker.syntactic import OperatorCollection


# Create the SK operator collection
sk_operators = OperatorCollection()
sk_operators.add_operator(SK_ExclusionOperator)
sk_operators.add_operator(SK_UniAndOperator)
sk_operators.add_operator(SK_UniOrOperator)
sk_operators.add_operator(SK_UniIdentityOperator)


# Define the SK theory
sk_exclusion_theory = {
    "semantics": SKExclusionSemantics,
    "proposition": UnilateralProposition,
    "model": ExclusionStructure,
    "operators": sk_operators,
}