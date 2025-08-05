import z3

from model_checker.utils import (
    ForAll,
    Exists,
)
from model_checker import syntactic

# Import operator collections from logos subtheories for reuse
from model_checker.theory_lib.logos.subtheories.extensional.operators import (
    get_operators as get_extensional_operators,
    NegationOperator,
)
from model_checker.theory_lib.logos.subtheories.modal.operators import (
    NecessityOperator,
    PossibilityOperator,
)
from model_checker.theory_lib.logos.subtheories.counterfactual.operators import (
    CounterfactualOperator as LogosCounterfactualOperator,
    MightCounterfactualOperator as LogosMightCounterfactualOperator,
)

##############################################################################
####################### PRIMITIVE IMPOSITION OPERATORS #######################
##############################################################################

class ImpositionOperator(syntactic.Operator):
    """Implementation of the counterfactual conditional.
    
    This operator represents the counterfactual conditional 'if A were the case, 
    then B would be the case'. The semantics involves evaluating the consequent 
    in the outcome possible worlds that result from imposing verifier states for
    the antecedent on the world of evaluation."""

    name = "\\boxright"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("t_imp_x", N)
        u = z3.BitVec("t_imp_u", N)
        eval_world = eval_point["world"]
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    semantics.extended_verify(x, leftarg, eval_point),
                    semantics.imposition(x, eval_world, u)
                ),
                semantics.true_at(rightarg, {"world": u}),
            ),
        )
    
    def false_at(self, leftarg, rightarg, eval_point):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("f_imp_x", N)
        u = z3.BitVec("f_imp_u", N)
        eval_world = eval_point["world"]
        return Exists(
            [x, u],
            z3.And(
                sem.extended_verify(x, leftarg, eval_point),
                sem.imposition(x, eval_world, u),
                sem.false_at(rightarg, {"world": u})),
            )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """A state verifies A ⊡ B at a world if the state is that world
        and A ⊡ B is true at that world."""
        world = eval_point["world"]
        return z3.And(
            state == world,
            self.true_at(leftarg, rightarg, eval_point)
        )
    
    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """A state falsifies A ⊡ B at a world if the state is that world
        and A ⊡ B is false at that world."""
        world = eval_point["world"]
        return z3.And(
            state == world,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        """Find verifiers and falsifiers for an imposition statement.
        
        An imposition A ⊡ B is:
        - True at world w iff for all verifiers x of A and all worlds u 
          such that imposition(x, w, u) holds, B is true at u
        - False at world w iff there exists a verifier x of A and a world u
          such that imposition(x, w, u) holds and B is false at u
          
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
        
        # Check each world to determine if A ⊡ B is true or false there
        for world in model.z3_world_states:
            # For THIS world, check if all impositions lead to B being true
            imposition_found = False
            all_impositions_satisfy_B = True
            
            for x_state in leftarg_verifiers:
                # Check all possible outcome worlds FROM THIS WORLD
                for outcome_world in model.z3_world_states:
                    # Check if imposition(x_state, world, outcome_world) holds
                    if z3_model.evaluate(semantics.imposition(x_state, world, outcome_world)):
                        imposition_found = True
                        
                        # Check if B is true at the outcome world
                        B_truth = rightarg.proposition.truth_value_at(outcome_world)
                        
                        if B_truth is False:
                            all_impositions_satisfy_B = False
                            break
                
                if not all_impositions_satisfy_B:
                    break
            
            # Determine truth at this world
            if not imposition_found:
                # No impositions from this world - vacuously true
                verifiers.add(world)
            elif all_impositions_satisfy_B:
                # All impositions satisfy B - true at this world
                verifiers.add(world)
            else:
                # Some imposition falsifies B - false at this world
                falsifiers.add(world)
        
        return verifiers, falsifiers
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_point. Then
        print the consequent in each alternative to the evaluation world.
        """
        is_outcome = self.semantics.calculate_outcome_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        outcome_worlds = is_outcome(left_argument_verifiers, eval_point, model_structure)
        self.print_over_worlds(sentence_obj, eval_point, outcome_worlds, indent_num, use_colors)


##############################################################################
######################## DEFINED IMPOSITION OPERATORS ########################
##############################################################################

class MightImpositionOperator(syntactic.DefinedOperator):

    name = "\\diamondright"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        return [
            NegationOperator, [
                ImpositionOperator,
                leftarg,
                [NegationOperator, rightarg]
            ]
        ]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_point. Then
        print the consequent in each alternative to the evaluation world.
        """
        is_outcome = self.semantics.calculate_outcome_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_outcome(left_argument_verifiers, eval_point, model_structure)
        self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num, use_colors)

##############################################################################
##################### LOGOS COUNTERFACTUAL OPERATORS #########################
##############################################################################

class LogosCounterfactual(LogosCounterfactualOperator):
    """
    Logos counterfactual operator imported and renamed for use in imposition theory.
    This allows using both imposition semantics (\\boxright) and logos semantics 
    (\\boxrightlogos) in the same example.
    """
    name = "\\boxrightlogos"
    
class LogosMightCounterfactual(syntactic.DefinedOperator):
    """
    Logos might counterfactual operator imported and renamed for use in imposition theory.
    This allows using both imposition semantics (\\diamondright) and logos semantics
    (\\diamondrightlogos) in the same example.
    """
    name = "\\diamondrightlogos"
    arity = 2
    
    def derived_definition(self, leftarg, rightarg):
        """Defines might counterfactual as negation of counterfactual with negated consequent."""
        return [NegationOperator, [LogosCounterfactual, leftarg, [NegationOperator, rightarg]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Delegate to the original print method."""
        LogosMightCounterfactualOperator.print_method(self, sentence_obj, eval_point, indent_num, use_colors)

def get_imposition_operators():
    """Get imposition-specific operators."""
    return {
        '\\boxright': ImpositionOperator,
        '\\diamondright': MightImpositionOperator,
        '\\boxrightlogos': LogosCounterfactual,
        '\\diamondrightlogos': LogosMightCounterfactual,
    }

def get_all_operators():
    """Get all operators including inherited ones from logos."""
    operators = {}
    
    # Import base operators from logos subtheories
    operators.update(get_extensional_operators())  # Basic logical operators
    
    # Add specific modal operators (without counterfactual dependencies)
    operators.update({
        "\\Box": NecessityOperator,
        "\\Diamond": PossibilityOperator,
    })
    
    # Add imposition-specific operators
    operators.update(get_imposition_operators())
    
    return operators

# Create operator collection for backward compatibility
imposition_operators = syntactic.OperatorCollection()
for op_name, op_class in get_all_operators().items():
    imposition_operators.add_operator(op_class)
