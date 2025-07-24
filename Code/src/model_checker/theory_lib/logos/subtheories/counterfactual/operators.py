"""
Counterfactual operators for hypothetical reasoning.

This module implements counterfactual logical operators:
- Counterfactual Conditional 
- Might Counterfactual
- Imposition
- Might Imposition
"""

import z3

from model_checker.utils import (
    ForAll,
    Exists,
)
from model_checker import syntactic

# Import required operators for defined operators
from ..extensional.operators import NegationOperator


class CounterfactualOperator(syntactic.Operator):
    """Implementation of the counterfactual conditional.
    
    This operator represents the counterfactual conditional 'if A were the case, 
    then B would be the case'. The semantics involves evaluating the consequent 
    in the closest possible worlds where the antecedent holds.
    """

    name = "\\boxright"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for counterfactual conditional at an evaluation point."""
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("t_cf_x", N)
        u = z3.BitVec("t_cf_u", N)
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    semantics.extended_verify(x, leftarg, eval_point),
                    semantics.is_alternative(u, x, eval_point["world"])
                ),
                semantics.true_at(rightarg, {"world": u}),
            ),
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for counterfactual conditional at an evaluation point."""
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("f_cf_x", N)
        u = z3.BitVec("f_cf_u", N)
        return Exists(
            [x, u],
            z3.And(
                semantics.extended_verify(x, leftarg, eval_point),
                semantics.is_alternative(u, x, eval_point["world"]),
                semantics.false_at(rightarg, {"world": u})),
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for counterfactual conditional in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for counterfactual conditional in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for a counterfactual conditional."""
        evaluate = left_sent_obj.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(left_sent_obj, right_sent_obj, eval_point))):
            return {self.semantics.null_state}, set()
        if bool(evaluate(self.false_at(left_sent_obj, right_sent_obj, eval_point))):
            return set(), {self.semantics.null_state}
        raise ValueError(
            f"{self.name} {left_sent_obj} {right_sent_obj} "
            f"is neither true nor false in the world {eval_point}."
        )

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the counterfactual conditional with proper indentation and formatting.
        
        Shows the antecedent in the evaluation world and then the consequent in each
        alternative world where the antecedent holds.
        """
        # Calculate alternative worlds based on the antecedent
        semantics = self.semantics
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        
        # Get worlds where the antecedent is verified
        left_verifiers = left_argument_obj.proposition.verifiers
        
        # Fallback: find worlds that are alternatives via the antecedent states
        N = semantics.N
        eval = model_structure.z3_model.evaluate
        world_states = model_structure.z3_world_states
        eval_world = eval_point["world"]
        alt_worlds = set()
        
        for state in left_verifiers:
            for world in world_states:
                if eval(semantics.is_alternative(world, state, eval_world)):
                    alt_worlds.add(world)
        
        # Use print_over_worlds to show alternatives
        self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num, use_colors)


class MightCounterfactualOperator(syntactic.DefinedOperator):
    """Implementation of the might counterfactual.
    
    This operator represents the might counterfactual 'if A were the case, 
    then B might be the case'. It is defined as the negation of the 
    counterfactual conditional with negated consequent.
    """

    name = "\\diamondright"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        """Defines might counterfactual as negation of counterfactual with negated consequent."""
        return [NegationOperator, [CounterfactualOperator, leftarg, [NegationOperator, rightarg]]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the might counterfactual with proper indentation and formatting.
        
        Shows the antecedent in the evaluation world and then the consequent in each
        alternative world where the antecedent holds.
        """
        # For defined operators, we need to get the original arguments
        # The might counterfactual is defined as ¬(A □→ ¬B)
        # So we want to show alternatives based on A
        left_argument_obj = sentence_obj.original_arguments[0]
        
        # Get the semantics and model structure
        semantics = self.semantics
        model_structure = sentence_obj.proposition.model_structure
        
        # Get worlds where the antecedent is verified
        left_verifiers = left_argument_obj.proposition.verifiers
        
        # Find alternative worlds using the semantics
        if hasattr(semantics, 'calculate_alternative_worlds'):
            alt_worlds = semantics.calculate_alternative_worlds(
                left_verifiers, eval_point, model_structure
            )
        else:
            # Fallback: find worlds that are alternatives via the antecedent states
            N = semantics.N
            eval = model_structure.z3_model.evaluate
            world_states = model_structure.z3_world_states
            eval_world = eval_point["world"]
            alt_worlds = set()
            
            for state in left_verifiers:
                for world in world_states:
                    if eval(semantics.is_alternative(world, state, eval_world)):
                        alt_worlds.add(world)
        
        # Use print_over_worlds to show alternatives
        self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num, use_colors)




def get_operators():
    """
    Get all counterfactual operators.
    
    Returns:
        dict: Dictionary mapping operator names to operator classes
    """
    return {
        "\\boxright": CounterfactualOperator,
        "\\diamondright": MightCounterfactualOperator,
    }
