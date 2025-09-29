"""
Core imposition semantics implementation.

This module contains the main ImpositionSemantics class that implements
Kit Fine's imposition semantics through inheritance from LogosSemantics.
"""

import z3

from model_checker.theory_lib.logos import LogosSemantics
from model_checker.utils import ForAll, Exists
from typing import Dict, Any, List, Optional


class ImpositionSemantics(LogosSemantics):
    """
    Kit Fine's imposition semantics as an independent theory.

    Inherits logos base functionality for consistency and code reuse,
    while implementing Fine's distinctive counterfactual semantics
    through the imposition operation. Developed as a separate theory
    for comparison with Brast-McKie hyperintensional semantics.

    This theory extends LogosSemantics with:
    - The imposition operation for counterfactual reasoning
    - Alternative world calculation based on imposition
    - Fine's specific semantic constraints
    """

    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'max_time': 1,
        'iterate': 1,
        'expectation': None,
    }

    # Optional: Add imposition-specific general settings
    ADDITIONAL_GENERAL_SETTINGS = {
        "derive_imposition": False,  # Theory-specific setting for imposition operations
    }

    def __init__(self, settings: Dict[str, Any]):
        """Initialize imposition semantics with settings."""
        # Initialize the parent LogosSemantics with settings
        super().__init__(combined_settings=settings)

        # Store derive_imposition setting (from ADDITIONAL_GENERAL_SETTINGS or user override)
        self.derive_imposition = settings.get('derive_imposition', False)

        # Define imposition-specific operations
        self._define_imposition_operation()

    def _define_imposition_operation(self) -> None:
        """Define the imposition operation as a Z3 function."""
        # Define the imposition function for Fine's semantics
        self.imposition = z3.Function(
            "imposition",
            z3.BitVecSort(self.N),  # state imposed
            z3.BitVecSort(self.N),  # world being imposed on
            z3.BitVecSort(self.N),  # outcome world
            z3.BoolSort()           # truth-value
        )

        # Define the frame constraints
        x, y, z, u = z3.BitVecs("frame_x frame_y, frame_z, frame_u", self.N)
        possibility_downard_closure = ForAll(
            [x, y],
            z3.Implies(z3.And(self.possible(y), self.is_part_of(x, y)), self.possible(x)),
        )
        is_main_world = self.is_world(self.main_world)
        inclusion = ForAll(
            [x, y, z],
            z3.Implies(
                self.imposition(x, y, z),
                self.is_part_of(x, z)
            )
        )
        actuality = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.is_part_of(x, y),
                    self.is_world(y)
                ),
                Exists(
                    z,
                    z3.And(
                        self.is_part_of(z, y),
                        self.imposition(x, y, z),
                    )
                )
            )
        )
        incorporation = ForAll(
            [x, y, z, u],
            z3.Implies(
                z3.And(
                    self.imposition(x, y, z),
                    self.is_part_of(u, z)
                ),
                self.imposition(self.fusion(x, u), y, z)
            )
        )
        completeness = ForAll(
            [x, y, z],
            z3.Implies(
                self.imposition(x, y, z),
                self.is_world(z)
            )
        )

        self.imposition_constraints = [
            inclusion,
            actuality,
            incorporation,
            completeness,
        ]

        # Check if we should derive imposition constraints
        if self.derive_imposition:
            # Use derived constraints instead of primitive imposition constraints
            self.imposition_constraints = self._derive_imposition()
            # Make premise and conclusion behaviors trivial (always true)
            # This ensures only the negated derived constraints contribute
            self.premise_behavior = lambda premise: z3.BoolVal(True)
            self.conclusion_behavior = lambda conclusion: z3.BoolVal(True)
        else:
            # Use normal imposition constraints and behaviors
            self.premise_behavior = lambda premise: self.true_at(premise, self.main_point)
            self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point)

        # Set frame constraints
        self.frame_constraints = [
            possibility_downard_closure,
            is_main_world,
        ] + self.imposition_constraints

    def alt_imposition(self, state_y: z3.BitVecRef, state_w: z3.BitVecRef, state_u: z3.BitVecRef) -> z3.BoolRef:
        """Determines if a state_u is an alternative world resulting from
        imposing state_y on state_w.

        This method permutes the arguments to provide an exact analog of the
        primitive imposition relation.

        Args:
            state_y: The state being imposed
            state_w: The world being imposed on
            state_u: The potential outcome world

        Returns:
            Z3 boolean expression for the alternative relation
        """
        return self.is_alternative(state_u, state_y, state_w)

    def _derive_imposition(self) -> List[z3.BoolRef]:
        """Given the definition of `is_alternative`, we may derive analogs
        of the frame constraints for imposition.

        When derive_imposition=True, this method returns the disjunction of negated
        derived constraints. This tests whether all derived constraints are entailed
        by the base imposition semantics. If Z3 finds no model (as expected), it
        proves that the frame constraints on primitive imposition fully entail all
        properties that would be imposed by the constructive is_alternative definition.

        Returns:
            List of derived constraint expressions
        """
        # Define the frame constraints
        x, y, z, u = z3.BitVecs("frame_x frame_y, frame_z, frame_u", self.N)
        alt_inclusion = ForAll(
            [x, y, z],
            z3.Implies(
                self.alt_imposition(x, y, z),
                self.is_part_of(x, z)
            )
        )
        alt_actuality = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.is_part_of(x, y),
                    self.is_world(y)
                ),
                Exists(
                    z,
                    z3.And(
                        self.is_part_of(z, y),
                        self.alt_imposition(x, y, z),
                    )
                )
            )
        )
        alt_incorporation = ForAll(
            [x, y, z, u],
            z3.Implies(
                z3.And(
                    self.alt_imposition(x, y, z),
                    self.is_part_of(u, z)
                ),
                self.alt_imposition(self.fusion(x, u), y, z)
            )
        )
        alt_completeness = ForAll(
            [x, y, z],
            z3.Implies(
                self.alt_imposition(x, y, z),
                self.is_world(z)
            )
        )

        # Negation of at least one of the derived constraints
        neg_alt_constraints = z3.Or(
            z3.Not(alt_inclusion),
            z3.Not(alt_actuality),
            z3.Not(alt_incorporation),
            z3.Not(alt_completeness),
        )

        # Return a list to combine
        return [neg_alt_constraints]

    def calculate_outcome_worlds(self, verifiers: List[z3.BitVecRef], eval_point: Dict[str, z3.BitVecRef], model_structure) -> set:
        """Calculate alternative worlds given verifiers and eval_point.

        Args:
            verifiers: List of verifying states
            eval_point: Evaluation point containing world information
            model_structure: The model structure containing Z3 model and world states

        Returns:
            Set of outcome worlds
        """
        eval = model_structure.z3_model.evaluate
        world_states = model_structure.z3_world_states
        eval_world = eval_point["world"]
        return {
            pw for ver in verifiers
            for pw in world_states
            if eval(self.imposition(ver, eval_world, pw))
        }