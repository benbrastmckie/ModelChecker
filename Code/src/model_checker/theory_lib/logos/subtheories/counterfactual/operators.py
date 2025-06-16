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
        sem = self.semantics
        u = z3.BitVec("t_cf_u", sem.N)
        v = z3.BitVec("t_cf_v", sem.N)
        
        return ForAll(
            [u, v],
            z3.Implies(
                z3.And(
                    sem.is_world(u),
                    sem.is_world(v),
                    sem.extended_verify(u, leftarg, eval_point),
                    sem.extended_verify(v, leftarg, eval_point),
                    sem.closer_world(u, v, eval_point)
                ),
                sem.extended_verify(u, rightarg, eval_point)
            ),
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for counterfactual conditional at an evaluation point."""
        sem = self.semantics
        u = z3.BitVec("f_cf_u", sem.N)
        
        return Exists(
            u,
            z3.And(
                sem.is_world(u),
                sem.extended_verify(u, leftarg, eval_point),
                sem.extended_falsify(u, rightarg, eval_point),
                ForAll(
                    z3.BitVec("f_cf_v", sem.N),
                    z3.Implies(
                        z3.And(
                            sem.is_world(z3.BitVec("f_cf_v", sem.N)),
                            sem.extended_verify(z3.BitVec("f_cf_v", sem.N), leftarg, eval_point)
                        ),
                        z3.Not(sem.closer_world(z3.BitVec("f_cf_v", sem.N), u, eval_point))
                    )
                )
            ),
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
        """Prints the counterfactual conditional with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class MightCounterfactualOperator(syntactic.DefinedOperator):
    """Implementation of the might counterfactual.
    
    This operator represents the might counterfactual 'if A were the case, 
    then B might be the case'. It is defined as the negation of the 
    counterfactual conditional with negated consequent.
    """

    name = "\\diamondright"
    arity = 2

    def connective_def(self, leftarg, rightarg):
        """Defines might counterfactual as negation of counterfactual with negated consequent."""
        negated_right = self.syntax.sentence("\\neg", rightarg)
        cf_conditional = self.syntax.sentence("\\boxright", leftarg, negated_right)
        return self.syntax.sentence("\\neg", cf_conditional)


class ImpositionOperator(syntactic.Operator):
    """Implementation of the imposition operator.
    
    This operator represents the imposition relation between propositions, where
    A imposes B. The semantics involves verifiers and falsifiers with specific 
    imposition conditions.
    """

    name = "\\imposition"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for imposition at an evaluation point."""
        sem = self.semantics
        u = z3.BitVec("t_imp_u", sem.N)
        v = z3.BitVec("t_imp_v", sem.N)
        
        return ForAll(
            [u, v],
            z3.Implies(
                z3.And(
                    sem.extended_verify(u, leftarg, eval_point),
                    sem.extended_verify(v, rightarg, eval_point)
                ),
                sem.extended_verify(sem.fusion(u, v), rightarg, eval_point)
            ),
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for imposition at an evaluation point."""
        sem = self.semantics
        u = z3.BitVec("f_imp_u", sem.N)
        v = z3.BitVec("f_imp_v", sem.N)
        
        return Exists(
            [u, v],
            z3.And(
                sem.extended_verify(u, leftarg, eval_point),
                sem.extended_verify(v, rightarg, eval_point),
                z3.Not(sem.extended_verify(sem.fusion(u, v), rightarg, eval_point))
            ),
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for imposition in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for imposition in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for an imposition relation."""
        product = self.semantics.product
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if product(Y_V, Z_V).issubset(Z_V):
            return {self.semantics.null_state}, set()
        return set(), {self.semantics.null_state}

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the imposition relation with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class MightImpositionOperator(syntactic.DefinedOperator):
    """Implementation of the might imposition operator.
    
    This operator represents the might imposition 'A could impose B'. 
    It is defined as the negation of the imposition with negated consequent.
    """

    name = "\\could"
    arity = 2

    def connective_def(self, leftarg, rightarg):
        """Defines might imposition as negation of imposition with negated consequent."""
        negated_right = self.syntax.sentence("\\neg", rightarg)
        imposition = self.syntax.sentence("\\imposition", leftarg, negated_right)
        return self.syntax.sentence("\\neg", imposition)


def get_operators():
    """
    Get all counterfactual operators.
    
    Returns:
        dict: Dictionary mapping operator names to operator classes
    """
    return {
        "\\boxright": CounterfactualOperator,
        "\\diamondright": MightCounterfactualOperator,
        "\\imposition": ImpositionOperator,
        "\\could": MightImpositionOperator,
    }