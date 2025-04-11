import z3

# Try installed package imports first
from model_checker.utils import (
    ForAll,
    Exists,
)
from model_checker import syntactic
from model_checker.theory_lib.default.operators import (
    default_operators,
    NegationOperator,
)

##############################################################################
####################### PRIMITIVE IMPOSITION OPERATORS #######################
##############################################################################

class ImpositionOperator(syntactic.Operator):
    name = "\\imposition"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("t_imp_x", N)
        u = z3.BitVec("t_imp_u", N)
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.imposition(x, eval_point, u)
                ),
                sem.true_at(rightarg, u),
            ),
        )
    
    def false_at(self, leftarg, rightarg, eval_point):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("f_imp_x", N)
        u = z3.BitVec("f_imp_u", N)
        return Exists(
            [x, u],
            z3.And(
                sem.extended_verify(x, leftarg, eval_point),
                sem.imposition(x, eval_point, u),
                sem.false_at(rightarg, u)),
            )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        # TODO: add constraint which requires state to be the null_state
        return self.true_at(leftarg, rightarg, eval_point)
    
    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        # TODO: add constraint which requires state to be the null_state
        return self.false_at(leftarg, rightarg, eval_point)

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        evaluate = leftarg.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(leftarg, rightarg, eval_point))):
            return {self.semantics.null_state}, set()
        if bool(evaluate(self.false_at(leftarg, rightarg, eval_point))):
            return set(), {self.semantics.null_state}
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
        alt_worlds = is_outcome(left_argument_verifiers, eval_point, model_structure)
        self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num, use_colors)


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

imposition_operators = syntactic.OperatorCollection(
    # primitive operators
    ImpositionOperator,
    # defined operators
    MightImpositionOperator,
)
imposition_operators.add_operator(default_operators)
