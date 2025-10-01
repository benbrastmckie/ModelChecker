"""
Witness constraint generation implementation for bimodal theory.

This module contains the WitnessConstraintGenerator class that creates
Z3 constraints defining accessible_world witness predicates for modal operators.

Unlike exclusion's three-condition negation semantics, bimodal uses simpler
modal accessibility constraints: accessible_world must return a valid world
where the argument formula has a different truth value.
"""

# Standard library imports
from typing import Any, List

# Third-party imports
import z3

# Local imports
from ...errors import WitnessConstraintError


class WitnessConstraintGenerator:
    """
    Generates constraints that define accessible_world witness predicates
    for modal operators in bimodal theory.

    For Box operator false_at():
        accessible_world(eval_world, eval_time) returns a world where
        the argument is false.

    The constraints ensure:
    1. accessible_world returns a valid world ID
    2. The returned world exists in the model
    3. eval_time is valid for the accessible world
    4. The argument has the required truth value at (accessible_world, eval_time)
    """

    def __init__(self, semantics: Any) -> None:
        """Initialize constraint generator.

        Args:
            semantics: BimodalSemantics instance providing semantic methods
        """
        self.semantics: Any = semantics
        self.N: int = semantics.N
        self.M: int = semantics.M

    def generate_witness_constraints(
        self,
        formula_str: str,
        formula_ast: Any,
        accessible_world_pred: z3.FuncDeclRef
    ) -> List[z3.BoolRef]:
        """
        Generate constraints defining accessible_world witness predicate.

        Args:
            formula_str: String identifier for formula (e.g., "Box_p")
            formula_ast: AST node for the formula (currently unused, for future extension)
            accessible_world_pred: Z3 function (Int, Int) → Int

        Returns:
            List of Z3 constraints defining witness behavior

        Raises:
            WitnessConstraintError: If inputs are invalid
        """
        # Validate inputs
        if not formula_str or not isinstance(formula_str, str):
            raise WitnessConstraintError(
                "Cannot generate constraints for empty or invalid formula",
                context={'formula_str': formula_str},
                suggestion="Provide a valid non-empty formula string"
            )

        if accessible_world_pred is None:
            raise WitnessConstraintError(
                f"Invalid accessible_world predicate for formula '{formula_str}'",
                context={'formula_str': formula_str, 'predicate': accessible_world_pred},
                suggestion="Ensure witness predicate is properly registered"
            )

        try:
            constraints = []

            # Generate universal constraints over all eval points
            eval_world_var = z3.Int(f'{formula_str}_constraint_eval_world')
            eval_time_var = z3.Int(f'{formula_str}_constraint_eval_time')

            # Get the accessible world for this eval point
            witness_world = accessible_world_pred(eval_world_var, eval_time_var)

            # Main constraint: ForAll eval_world, eval_time:
            #   If (eval_world is valid AND eval_time is valid for eval_world)
            #   Then accessible_world must be a valid world
            #        AND eval_time must be valid for accessible_world
            main_constraint = z3.ForAll(
                [eval_world_var, eval_time_var],
                z3.Implies(
                    z3.And(
                        # Preconditions: eval point is valid
                        self.semantics.is_world(eval_world_var),
                        self.semantics.is_valid_time_for_world(eval_world_var, eval_time_var)
                    ),
                    z3.And(
                        # Postcondition 1: witness is a valid world
                        self.semantics.is_world(witness_world),
                        # Postcondition 2: eval_time is valid for witness world
                        self.semantics.is_valid_time_for_world(witness_world, eval_time_var)
                    )
                )
            )

            constraints.append(main_constraint)

            return constraints

        except Exception as e:
            raise WitnessConstraintError(
                f"Failed to generate witness constraints for formula '{formula_str}'",
                context={
                    'formula_str': formula_str,
                    'original_error': str(e),
                    'N': self.N,
                    'M': self.M
                },
                suggestion="Check that semantics methods (is_world, is_valid_time_for_world) are available"
            ) from e

    def _witness_constraint_for_falsity(
        self,
        formula_str: str,
        argument_ast: Any,
        accessible_world_pred: z3.FuncDeclRef
    ) -> z3.BoolRef:
        """
        Generate constraint ensuring accessible_world points to a world
        where the argument is false.

        This is used for Box.false_at() - the witness must satisfy falsity.

        Args:
            formula_str: String identifier for formula
            argument_ast: AST for the argument formula
            accessible_world_pred: The accessible_world predicate

        Returns:
            Z3 constraint ensuring argument is false at accessible_world

        Note: This method is currently a placeholder for Phase 4 integration.
        The full constraint requires recursive evaluation of argument_ast,
        which will be implemented when integrating with NecessityOperator.
        """
        # Placeholder for future Phase 4 implementation
        # Will need to call semantics.false_at(argument_ast, witness_eval_point)
        # to ensure argument is false at the witness world
        pass

    def _minimality_constraint(
        self,
        formula_str: str,
        accessible_world_pred: z3.FuncDeclRef
    ) -> z3.BoolRef:
        """
        Generate optional minimality constraint ensuring accessible_world
        returns the smallest valid world ID satisfying conditions.

        Args:
            formula_str: String identifier for formula
            accessible_world_pred: The accessible_world predicate

        Returns:
            Z3 constraint enforcing minimality

        Note: This is optional and can be omitted for initial implementation.
        Minimality helps with determinism but isn't required for correctness.
        """
        # Optional: Can be implemented if deterministic witness selection is desired
        # ForAll eval_world, eval_time:
        #   ForAll other_world < accessible_world(eval_world, eval_time):
        #     other_world does NOT satisfy the witness conditions
        pass
