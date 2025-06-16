"""
Modal operators for necessity and possibility.

This module implements modal logical operators:
- Necessity (¡)
- Possibility (Ç)  
- Counterfactual Necessity (\CFBox)
- Counterfactual Possibility (\CFDiamond)
"""

import z3

from model_checker.utils import (
    ForAll,
    Exists,
)
from model_checker import syntactic


class NecessityOperator(syntactic.Operator):
    """Implementation of the necessity/universal modality (¡).
    
    This operator represents the modal necessity 'it is necessarily the case that',
    often written as ¡A. The semantics involves quantifying over all possible worlds
    in the model and checking if A is true in all of them.
    """
    name = "\\Box"
    arity = 1

    def true_at(self, argument, eval_point):
        """Defines truth conditions for necessity at an evaluation point."""
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return ForAll(
            u,
            z3.Implies(
                sem.is_world(u),
                sem.true_at(argument, u),
            ),
        )
    
    def false_at(self, argument, eval_point):
        """Defines falsity conditions for necessity at an evaluation point."""
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return Exists(
            u,
            z3.And(
                sem.is_world(u),
                sem.false_at(argument, u),
            ),
        )
    
    def extended_verify(self, state, argument, eval_point):
        """Defines verification conditions for necessity in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(argument, eval_point)
        )
    
    def extended_falsify(self, state, argument, eval_point):
        """Defines falsification conditions for necessity in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(argument, eval_point)
        )

    def find_verifiers_and_falsifiers(self, argument, eval_point):
        """Finds the verifiers and falsifiers for a necessity statement."""
        evaluate = argument.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(argument, eval_point))):
            return {self.semantics.null_state}, set()
        if bool(evaluate(self.false_at(argument, eval_point))):
            return set(), {self.semantics.null_state}
        raise ValueError(
            f"{self.name} {argument} "
            f"is neither true nor false in the world {eval_point}."
        )
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints modal operators with evaluation over all worlds."""
        all_worlds = sentence_obj.proposition.model_structure.z3_world_states
        self.print_over_worlds(sentence_obj, eval_point, all_worlds, indent_num, use_colors)


def get_operators():
    """
    Get all modal operators.
    
    Returns:
        dict: Dictionary mapping operator names to operator classes
    """
    return {
        "\\Box": NecessityOperator,
    }