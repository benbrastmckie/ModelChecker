"""
Counterfactual operators for counterfactual reasoning.

This module implements counterfactual logical operators:
- Counterfactual Conditional 
- Might Counterfactual
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
    in the alternative possible worlds that contain a verifier for the antecedent
    together with a maximal part of the world of evaluation that is compatible
    with that verifier for the antecedent."""

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
        """A state verifies A □→ B at a world if the state is that world
        and A □→ B is true at that world."""
        world = eval_point["world"]
        return z3.And(
            state == world,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """A state falsifies A □→ B at a world if the state is that world
        and A □→ B is false at that world."""
        world = eval_point["world"]
        return z3.And(
            state == world,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        """Find verifiers and falsifiers for a counterfactual conditional.
        
        A counterfactual A □→ B is:
        - True at world w iff for all verifiers x of A and all worlds u 
          such that u is an x-alternative to w, B is true at u
        - False at world w iff there exists a verifier x of A and a world u
          such that u is an x-alternative to w and B is false at u
          
        This method checks each world to determine truth value and builds
        verifier/falsifier sets accordingly.
        """
        # Get model structure and semantics
        model = leftarg.proposition.model_structure
        semantics = self.semantics
        z3_model = model.z3_model
        
        # Initialize verifier and falsifier sets
        verifiers = set()
        falsifiers = set()
        
        # Get the verifiers of the antecedent
        leftarg_verifiers = leftarg.proposition.verifiers
        
        # Check each world to determine if A □→ B is true or false there
        for world in model.z3_world_states:
            # For THIS world, check if all A-alternatives satisfy B
            alternative_found = False
            all_alternatives_satisfy_B = True
            
            for x_state in leftarg_verifiers:
                # Check all possible alternative worlds
                for alt_world in model.z3_world_states:
                    # Check if alt_world is an x-alternative to this world
                    if z3_model.evaluate(semantics.is_alternative(alt_world, x_state, world)):
                        alternative_found = True
                        
                        # Check if B is true at the alternative world
                        B_truth = rightarg.proposition.truth_value_at(alt_world)
                        
                        if B_truth is False:
                            all_alternatives_satisfy_B = False
                            break
                
                if not all_alternatives_satisfy_B:
                    break
            
            # Determine truth at this world
            if not alternative_found:
                # No A-alternatives from this world - vacuously true
                verifiers.add(world)
            elif all_alternatives_satisfy_B:
                # All A-alternatives satisfy B - true at this world
                verifiers.add(world)
            else:
                # Some A-alternative falsifies B - false at this world
                falsifiers.add(world)
        
        return verifiers, falsifiers

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
