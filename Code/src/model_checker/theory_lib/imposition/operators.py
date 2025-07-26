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

##############################################################################
####################### PRIMITIVE IMPOSITION OPERATORS #######################
##############################################################################

class ImpositionOperator(syntactic.Operator):
    name = "\\imposition"
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
        return self.true_at(leftarg, rightarg, eval_point)
    
    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        return self.false_at(leftarg, rightarg, eval_point)

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        evaluate = leftarg.proposition.model_structure.z3_model.evaluate
        null_state = self.semantics.null_state
        if bool(evaluate(self.true_at(leftarg, rightarg, eval_point))):
            return {null_state}, set()
        if bool(evaluate(self.false_at(leftarg, rightarg, eval_point))):
            return set(), {null_state}
        raise ValueError(
            f"{leftarg.name} {self.name} {rightarg.name} "
            f"is neither true nor false in the world {eval_point}."
        )
    
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

    name = "\\could"
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

def get_imposition_operators():
    """Get imposition-specific operators."""
    return {
        '\\imposition': ImpositionOperator,
        '\\could': MightImpositionOperator,
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
