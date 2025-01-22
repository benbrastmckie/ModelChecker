import z3

from model_checker.utils import (
    ForAll,
    Exists,
)

from model_checker import syntactic

from model_checker.primitive import (
    NegationOperator,
    AndOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    IdentityOperator,
    CounterfactualOperator,
    NecessityOperator,
)

from model_checker.defined import (
    ConditionalOperator,
    BiconditionalOperator,
    MightCounterfactualOperator,
    DefPossibilityOperator,
)

##############################################################################
####################### PRIMITIVE IMPOSITION OPERATORS #######################
##############################################################################

class ImpositionOperator(syntactic.Operator):
    name = "\\imposition"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("t_imp_x", N)
        u = z3.BitVec("t_imp_u", N)
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    sem.extended_verify(x, leftarg, eval_world),
                    sem.imposition(x, eval_world, u)
                ),
                sem.true_at(rightarg, u),
            ),
        )
    
    def false_at(self, leftarg, rightarg, eval_world):
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("f_imp_x", N)
        u = z3.BitVec("f_imp_u", N)
        return Exists(
            [x, u],
            z3.And(
                sem.extended_verify(x, leftarg, eval_world),
                sem.imposition(x, eval_world, u),
                sem.false_at(rightarg, u)),
            )

    def extended_verify(self, state, leftarg, rightarg, eval_world):
        # TODO: add constraint which requires state to be the null_bit
        return self.true_at(leftarg, rightarg, eval_world)
    
    def extended_falsify(self, state, leftarg, rightarg, eval_world):
        # TODO: add constraint which requires state to be the null_bit
        return self.false_at(leftarg, rightarg, eval_world)

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_world):
        evaluate = leftarg.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(leftarg, rightarg, eval_world))):
            return {self.semantics.null_bit}, set()
        if bool(evaluate(self.false_at(leftarg, rightarg, eval_world))):
            return set(), {self.semantics.null_bit}
        raise ValueError(
            f"{leftarg.name} {self.name} {rightarg.name} "
            f"is neither true nor false in the world {eval_world}."
        )
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        is_outcome = self.semantics.calculate_outcome_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_outcome(left_argument_verifiers, eval_world, model_structure)
        self.print_over_worlds(sentence_obj, eval_world, alt_worlds, indent_num, use_colors)


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

    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        is_outcome = self.semantics.calculate_outcome_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_outcome(left_argument_verifiers, eval_world, model_structure)
        self.print_over_worlds(sentence_obj, eval_world, alt_worlds, indent_num, use_colors)

combined_operators = syntactic.OperatorCollection(
    # default primitive operators
    NegationOperator,
    AndOperator,
    OrOperator,
    TopOperator,
    BotOperator,
    IdentityOperator,
    CounterfactualOperator,
    NecessityOperator,

    # default defined operators
    ConditionalOperator,
    BiconditionalOperator,
    MightCounterfactualOperator,
    DefPossibilityOperator,

    # primitive operators
    ImpositionOperator,

    # defined operators
    MightImpositionOperator,
)
