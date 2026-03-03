"""
Witness predicate registry implementation.

This module contains the WitnessRegistry class that tracks witness predicates
for formulas in the model.
"""

# Standard library imports
from typing import Dict, Set, Tuple

# Third-party imports
import z3

# Local imports
from ...errors import WitnessRegistryError, WitnessPredicateError


class WitnessRegistry:
    """
    Registry for all witness predicates in the model.
    Tracks which formulas have associated witness functions.

    Performance optimizations:
    - Cached predicate lookups for frequent access
    - Pre-computed predicate name validation
    """

    def __init__(self, N: int) -> None:
        self.N: int = N
        self.predicates: Dict[str, z3.FuncDeclRef] = {}
        self.formula_mapping: Dict[str, Set[str]] = {}
        # Performance optimization: Cache for frequent lookups
        self._predicate_cache: Dict[str, Tuple[z3.FuncDeclRef, z3.FuncDeclRef]] = {}

    def register_witness_predicates(self, formula_str: str) -> Tuple[z3.FuncDeclRef, z3.FuncDeclRef]:
        """
        Register witness predicates h and y for a formula.
        Returns (h_predicate, y_predicate).
        """
        if not formula_str or not isinstance(formula_str, str):
            raise WitnessPredicateError(
                formula_str or "unknown",
                "registration",
                context={'invalid_formula_str': formula_str},
                suggestion="Provide a valid non-empty string formula identifier"
            )

        h_name = f"{formula_str}_h"
        y_name = f"{formula_str}_y"

        # Check if predicates already exist
        if h_name in self.predicates or y_name in self.predicates:
            raise WitnessRegistryError(
                f"Witness predicates for formula '{formula_str}' already registered",
                context={'formula_str': formula_str, 'existing_predicates': list(self.predicates.keys())},
                suggestion="Use get_witness_predicates() to retrieve existing predicates"
            )

        try:
            # Create Z3 functions for witness predicates
            h_pred = z3.Function(h_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))
            y_pred = z3.Function(y_name, z3.BitVecSort(self.N), z3.BitVecSort(self.N))

            self.predicates[h_name] = h_pred
            self.predicates[y_name] = y_pred

            self.formula_mapping[formula_str] = {h_name, y_name}

            # Cache the result for faster future access
            self._predicate_cache[formula_str] = (h_pred, y_pred)

            return h_pred, y_pred

        except Exception as e:
            raise WitnessPredicateError(
                formula_str,
                "registration",
                context={'original_error': str(e), 'N': self.N},
                suggestion="Check that N is valid and Z3 is properly initialized"
            ) from e

    def get_witness_predicates(self, formula_str: str) -> Tuple[z3.FuncDeclRef, z3.FuncDeclRef]:
        """
        Get existing witness predicates for a formula.
        Returns (h_predicate, y_predicate).

        Performance optimized with caching for frequent lookups.
        """
        # Fast path: Check cache first
        if formula_str in self._predicate_cache:
            return self._predicate_cache[formula_str]

        # Fallback: Traditional lookup with error handling
        if formula_str not in self.formula_mapping:
            raise WitnessPredicateError(
                formula_str,
                "retrieval",
                context={'available_formulas': list(self.formula_mapping.keys())},
                suggestion="Register predicates first using register_witness_predicates()"
            )

        h_name = f"{formula_str}_h"
        y_name = f"{formula_str}_y"

        try:
            h_pred = self.predicates[h_name]
            y_pred = self.predicates[y_name]
            # Update cache for future access
            self._predicate_cache[formula_str] = (h_pred, y_pred)
            return h_pred, y_pred
        except KeyError as e:
            raise WitnessRegistryError(
                f"Inconsistent registry state for formula '{formula_str}'",
                context={'missing_predicate': str(e), 'formula_str': formula_str},
                suggestion="Clear registry and re-register predicates"
            ) from e

    def get_all_predicates(self) -> Dict[str, z3.FuncDeclRef]:
        """Get all registered witness predicates."""
        return self.predicates.copy()

    def clear(self) -> None:
        """Clear all registered predicates."""
        self.predicates.clear()
        self.formula_mapping.clear()
        self._predicate_cache.clear()  # Clear cache as well