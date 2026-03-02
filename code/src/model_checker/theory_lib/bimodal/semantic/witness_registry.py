"""
Witness predicate registry implementation for bimodal theory.

This module contains the WitnessRegistry class that tracks accessible_world
witness predicates for modal formulas. Unlike exclusion theory's dual h/y predicates,
bimodal uses a single accessible_world predicate per formula.
"""

# Standard library imports
from typing import Dict, Set

# Third-party imports
import z3

# Local imports
from ...errors import WitnessRegistryError, WitnessPredicateError


class WitnessRegistry:
    """
    Registry for accessible_world witness predicates in bimodal theory.
    Tracks which formulas have associated witness functions.

    Unlike exclusion theory (which uses h/y dual predicates), bimodal uses
    a single accessible_world predicate per formula for modal accessibility.

    Performance optimizations:
    - Cached predicate lookups for frequent access
    - Pre-computed predicate name validation
    """

    def __init__(self, N: int, M: int) -> None:
        """Initialize witness registry.

        Args:
            N: BitVec size for world states
            M: Maximum time bound

        Note: N and M are stored for reference, but predicates use IntSort
        for world IDs and times (not BitVec) in bimodal theory.
        """
        self.N: int = N
        self.M: int = M
        self.predicates: Dict[str, z3.FuncDeclRef] = {}
        self.formula_mapping: Dict[str, Set[str]] = {}
        # Performance optimization: Cache for frequent lookups
        self._predicate_cache: Dict[str, z3.FuncDeclRef] = {}

    def register_witness_predicate(self, formula_str: str) -> z3.FuncDeclRef:
        """
        Register accessible_world witness predicate for a formula.
        Returns the created predicate function.

        Args:
            formula_str: String identifier for the formula (e.g., "Box_p")

        Returns:
            z3.FuncDeclRef: accessible_world function with signature (Int, Int) → Int

        Raises:
            WitnessPredicateError: If formula_str is empty or invalid
            WitnessRegistryError: If formula already has registered predicate
        """
        if not formula_str or not isinstance(formula_str, str):
            raise WitnessPredicateError(
                formula_str or "unknown",
                "registration",
                context={'invalid_formula_str': formula_str},
                suggestion="Provide a valid non-empty string formula identifier"
            )

        pred_name = f"{formula_str}_accessible_world"

        # Check if predicate already exists
        if pred_name in self.predicates:
            raise WitnessRegistryError(
                f"Witness predicate for formula '{formula_str}' already registered",
                context={'formula_str': formula_str, 'existing_predicates': list(self.predicates.keys())},
                suggestion="Use get_witness_predicate() to retrieve existing predicate"
            )

        try:
            # Create Z3 function for accessible_world witness predicate
            # Signature: (world: Int, time: Int) → Int (accessible world ID)
            accessible_world_pred = z3.Function(
                pred_name,
                z3.IntSort(),  # eval_world parameter
                z3.IntSort(),  # eval_time parameter
                z3.IntSort()   # returns: accessible_world ID
            )

            self.predicates[pred_name] = accessible_world_pred

            # Map formula to its predicate name (using Set for consistency with exclusion)
            self.formula_mapping[formula_str] = {pred_name}

            # Cache the result for faster future access
            self._predicate_cache[formula_str] = accessible_world_pred

            return accessible_world_pred

        except Exception as e:
            raise WitnessPredicateError(
                formula_str,
                "registration",
                context={'original_error': str(e), 'N': self.N, 'M': self.M},
                suggestion="Check that N, M are valid and Z3 is properly initialized"
            ) from e

    def get_witness_predicate(self, formula_str: str) -> z3.FuncDeclRef:
        """
        Get existing accessible_world witness predicate for a formula.

        Performance optimized with caching for frequent lookups.

        Args:
            formula_str: String identifier for the formula

        Returns:
            z3.FuncDeclRef: The accessible_world predicate

        Raises:
            WitnessPredicateError: If formula has no registered predicate
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
                suggestion="Register predicate first using register_witness_predicate()"
            )

        pred_name = f"{formula_str}_accessible_world"

        try:
            pred = self.predicates[pred_name]
            # Update cache for future access
            self._predicate_cache[formula_str] = pred
            return pred
        except KeyError as e:
            raise WitnessRegistryError(
                f"Inconsistent registry state for formula '{formula_str}'",
                context={'missing_predicate': str(e), 'formula_str': formula_str},
                suggestion="Clear registry and re-register predicates"
            ) from e

    def has_witness_predicate(self, formula_str: str) -> bool:
        """
        Check if formula has a registered witness predicate.

        Args:
            formula_str: String identifier for the formula

        Returns:
            bool: True if predicate exists, False otherwise
        """
        return formula_str in self.formula_mapping

    def get_all_predicates(self) -> Dict[str, z3.FuncDeclRef]:
        """
        Get all registered witness predicates.

        Returns:
            Dict[str, z3.FuncDeclRef]: Copy of predicates dictionary
        """
        return self.predicates.copy()

    def clear(self) -> None:
        """Clear all registered predicates and reset registry state."""
        self.predicates.clear()
        self.formula_mapping.clear()
        self._predicate_cache.clear()  # Clear cache as well
