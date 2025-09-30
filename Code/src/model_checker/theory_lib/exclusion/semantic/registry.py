"""
Witness predicate registry implementation.

This module contains the WitnessRegistry class that tracks witness predicates
for formulas in the model.
"""

# Standard library imports
from typing import Dict, Set, Tuple

# Third-party imports
import z3


class WitnessRegistry:
    """
    Registry for all witness predicates in the model.
    Tracks which formulas have associated witness functions.
    """

    def __init__(self, N: int) -> None:
        self.N: int = N
        self.predicates: Dict[str, z3.FuncDeclRef] = {}
        self.formula_mapping: Dict[str, Set[str]] = {}

    def register_witness_predicates(self, formula_str: str) -> Tuple[z3.FuncDeclRef, z3.FuncDeclRef]:
        """
        Register witness predicates h and y for a formula.
        Returns (h_predicate, y_predicate).
        """
        h_name = f"{formula_str}_h"
        y_name = f"{formula_str}_y"

        # Create Z3 functions for witness predicates
        h_pred = z3.Function(h_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))
        y_pred = z3.Function(y_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))

        self.predicates[h_name] = h_pred
        self.predicates[y_name] = y_pred

        self.formula_mapping[formula_str] = {h_name, y_name}

        return h_pred, y_pred

    def get_all_predicates(self) -> Dict[str, z3.FuncDeclRef]:
        """Get all registered witness predicates."""
        return self.predicates.copy()

    def clear(self) -> None:
        """Clear all registered predicates."""
        self.predicates.clear()
        self.formula_mapping.clear()