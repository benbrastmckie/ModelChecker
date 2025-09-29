"""
Witness-aware model implementation.

This module contains the WitnessAwareModel class that treats witness functions
as first-class predicates in the model.
"""

# Standard library imports
from typing import Any, Dict, Optional, Tuple

# Third-party imports
import z3


class WitnessAwareModel:
    """
    Model that treats witness functions as first-class predicates.

    In addition to standard predicates (verify, exclude, fusion, etc.),
    this model includes witness predicates for negation formulas.
    """

    def __init__(self, z3_model: z3.ModelRef, semantics: Any, witness_predicates: Dict[str, z3.FuncDeclRef]) -> None:
        self.z3_model = z3_model
        self.semantics = semantics
        self.witness_predicates = witness_predicates
        # Cache for evaluated predicates
        self._cache = {}

    def eval(self, expr):
        """Standard Z3 model evaluation."""
        return self.z3_model.eval(expr)

    def has_witness_for(self, formula_str: str) -> bool:
        """Check if model has witness predicates for given formula."""
        return f"{formula_str}_h" in self.witness_predicates

    def get_h_witness(self, formula_str: str, state: int) -> Optional[int]:
        """
        Get h(state) for the given formula.
        This is the key method that makes witnesses accessible.
        """
        h_pred = self.witness_predicates.get(f"{formula_str}_h")
        if h_pred is None:
            return None

        # Query the witness predicate
        state_bv = z3.BitVecVal(state, self.semantics.N)
        result = self.eval(h_pred(state_bv))
        if z3.is_bv_value(result):
            return result.as_long()
        return None

    def get_y_witness(self, formula_str: str, state: int) -> Optional[int]:
        """Get y(state) for the given formula."""
        y_pred = self.witness_predicates.get(f"{formula_str}_y")
        if y_pred is None:
            return None

        state_bv = z3.BitVecVal(state, self.semantics.N)
        result = self.eval(y_pred(state_bv))
        if z3.is_bv_value(result):
            return result.as_long()
        return None

    def get_all_witness_values(self, formula_str: str) -> Dict[int, Tuple[int, int]]:
        """Get all witness values for a formula."""
        witness_map = {}

        for state in range(2**self.semantics.N):
            h_val = self.get_h_witness(formula_str, state)
            y_val = self.get_y_witness(formula_str, state)
            if h_val is not None and y_val is not None:
                witness_map[state] = (h_val, y_val)

        return witness_map