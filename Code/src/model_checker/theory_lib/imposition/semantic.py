##########################
### DEFINE THE IMPORTS ###
##########################

import z3

# Try local imports first (for development)
try:
    from src.model_checker.model import (
        SemanticDefaults,
    )
    from src.model_checker.utils import (
        ForAll,
        Exists,
    )
    from src.model_checker import syntactic
except ImportError:
    # Fall back to installed package imports
    from model_checker.model import (
        SemanticDefaults,
    )
    from model_checker.utils import (
        ForAll,
        Exists,
    )
    from model_checker import syntactic



##############################################################################
######################### SEMANTICS AND PROPOSITIONS #########################
##############################################################################

class ImpositionSemantics(SemanticDefaults):
    """Includes the semantic primitives, semantic definitions, frame
    constraints, truth and falsity theories, and premise/conclusion behavior."""

    DEFAULT_EXAMPLE_SETTINGS = {
        'N' : 3,
        'contingent' : False,
        'non_empty' : False,
        'non_null' : False,
        'disjoint' : False,
        'max_time' : 1,
        'expectation' : None,
    }

    def __init__(self, settings):

        # Initialize the superclass to set defaults
        super().__init__(settings)

        # Define the Z3 primitives
        self.verify = z3.Function("verify", z3.BitVecSort(self.N), syntactic.AtomSort, z3.BoolSort())
        self.falsify = z3.Function("falsify", z3.BitVecSort(self.N), syntactic.AtomSort, z3.BoolSort())
        self.possible = z3.Function("possible", z3.BitVecSort(self.N), z3.BoolSort())
        self.imposition = z3.Function( # needed to encode Fine's semantics
            "imposition",
            z3.BitVecSort(self.N), # state imposed
            z3.BitVecSort(self.N), # world being imposed on
            z3.BitVecSort(self.N), # outcome world
            z3.BoolSort()     # bool
        )
        self.main_world = z3.BitVec("w", self.N)
        self.main_point = {
            "world" : self.main_world
        }

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
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_point["world"])
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point["world"])

    def compatible(self, bit_x, bit_y):
        """the fusion of bit_x and bit_y is possible
        returns a Z3 constraint"""
        return self.possible(self.fusion(bit_x, bit_y))

    def maximal(self, bit_w):
        """bit_w includes all compatible states as parts.
        returns a Z3 constraint"""
        x = z3.BitVec("max_x", self.N)
        return ForAll(
            x,
            z3.Implies(
                self.compatible(x, bit_w),
                self.is_part_of(x, bit_w),
            ),
        )

    def is_world(self, bit_w):
        """bit_w is both possible and maximal.
        returns a Z3 constraint"""
        return z3.And(
            self.possible(bit_w),
            self.maximal(bit_w),
        )

    def is_alternative(self, outcome_world, state, eval_point):
        """Returns whether outcome_world is an alternative to eval_point via state"""
        return self.imposition(state, eval_point, outcome_world)

    def true_at(self, sentence, eval_world):
        """
        derived_object is always a list, eval world a BitVector
        derived_object is the third kind of derived_object
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("t_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.verify(x, sentence_letter)))
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.true_at(*arguments, eval_world)

    def false_at(self, sentence, eval_world):
        """
        derived_object is always a list, eval world a BitVector
        derived_object is the third kind of derived_object
        """
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            x = z3.BitVec("f_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.falsify(x, sentence_letter)))
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.false_at(*arguments, eval_world)

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

    def calculate_alternative_worlds(self, verifiers, eval_point, model_structure):
        """Calculate alternative worlds given verifiers and eval_point."""
        imposition = model_structure.semantics.imposition
        eval = model_structure.z3_model.evaluate
        world_bits = model_structure.z3_world_bits
        eval_world = eval_point["world"]
        return {
            pw for ver in verifiers
            for pw in world_bits
            if eval(imposition(ver, eval_world, pw))
        }
