"""
Reduced theory module for exclusion semantics.

This module provides the integration point for the reduced semantics
implementation with the model checker framework.
"""

from model_checker import syntactic
from model_checker.theory_lib.exclusion.reduced_semantic import (
    ReducedExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure
)
from model_checker.theory_lib.exclusion.reduced_operators import (
    ExclusionOperator,
    UniAndOperator,
    UniOrOperator,
    UniIdentityOperator
)


def create_reduced_operators():
    """Create operator collection for reduced semantics."""
    operators = syntactic.OperatorCollection()
    operators.add_operator(ExclusionOperator)
    operators.add_operator(UniAndOperator)
    operators.add_operator(UniOrOperator)
    operators.add_operator(UniIdentityOperator)
    return operators


def reduced_exclusion_theory():
    """Return the components needed for the reduced exclusion theory."""
    return {
        'operators': create_reduced_operators(),
        'semantics': ReducedExclusionSemantics,
        'proposition': UnilateralProposition,
        'structure': ExclusionStructure
    }