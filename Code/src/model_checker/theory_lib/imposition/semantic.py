##########################
### DEFINE THE IMPORTS ###
##########################

import z3

from model_checker.theory_lib.logos import LogosSemantics
from model_checker.utils import (
    ForAll,
    Exists,
)



##############################################################################
######################### SEMANTICS AND PROPOSITIONS #########################
##############################################################################

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
        'N' : 3,
        'contingent' : False,
        'non_empty' : False,
        'non_null' : False,
        'disjoint' : False,
        'max_time' : 1,
        'iterate' : 1,
        'expectation' : None,
    }
    
    # Default general settings for the imposition theory
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "maximize": False,
    }

    def __init__(self, settings):
        # Merge settings with defaults
        combined_settings = {}
        combined_settings.update(self.DEFAULT_EXAMPLE_SETTINGS)
        combined_settings.update(self.DEFAULT_GENERAL_SETTINGS)
        combined_settings.update(settings)  # User settings override defaults
        
        # Initialize the parent LogosSemantics with combined_settings
        super().__init__(combined_settings=combined_settings)
        
        # Define imposition-specific operations
        self._define_imposition_operation()
    
    def _define_imposition_operation(self):
        """Define the imposition operation as a Z3 function."""
        # Define the imposition function for Fine's semantics
        self.imposition = z3.Function(
            "imposition",
            z3.BitVecSort(self.N),  # state imposed
            z3.BitVecSort(self.N),  # world being imposed on
            z3.BitVecSort(self.N),  # outcome world
            z3.BoolSort()           # boolean result
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

        # Set frame constraints
        self.frame_constraints = [
            possibility_downard_closure,
            is_main_world,
            inclusion,
            actuality,
            incorporation,
            completeness,
        ]

        # Define invalidity conditions
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_point)
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point)

    def extended_verify(self, state, sentence, eval_point):
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.verify(state, sentence_letter)
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.extended_verify(state, *arguments, eval_point)
    
    def extended_falsify(self, state, sentence, eval_point):
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.falsify(state, sentence_letter)
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.extended_falsify(state, *arguments, eval_point)

    def calculate_outcome_worlds(self, verifiers, eval_point, model_structure):
        """Calculate alternative worlds given verifiers and eval_point."""
        eval = model_structure.z3_model.evaluate
        world_states = model_structure.z3_world_states
        eval_world = eval_point["world"]
        return {
            pw for ver in verifiers
            for pw in world_states
            if eval(self.imposition(ver, eval_world, pw))
        }
