"""
Extensional operators for truth-functional logic.

This module implements the basic extensional logical operators:
- Negation (¬)
- Conjunction (∧)
- Disjunction (∨)
- Top (⊤)
- Bottom (⊥)
- Material Implication (→)
- Biconditional (↔)
"""

import z3

from model_checker.utils import (
    ForAll,
    Exists,
)
from model_checker import syntactic


class NegationOperator(syntactic.Operator):
    """Implementation of logical negation (¬).
    
    This operator implements both intensional truth/falsity conditions and
    hyperintensional verifier/falsifier semantics for logical negation. 
    It flips the truth value of its argument: if A is true, ¬A is false, 
    and if A is false, ¬A is true.
    """

    name = "\\neg"
    arity = 1

    def true_at(self, argument, eval_point):
        """Defines truth conditions for negation at an evaluation point."""
        return self.semantics.false_at(argument, eval_point)

    def false_at(self, argument, eval_point):
        """Defines falsity conditions for negation at an evaluation point."""
        return self.semantics.true_at(argument, eval_point)

    def extended_verify(self, state, argument, eval_point):
        """Defines verification conditions for negation in the extended semantics."""
        return self.semantics.extended_falsify(state, argument, eval_point)

    def extended_falsify(self, state, argument, eval_point):
        """Defines falsification conditions for negation in the extended semantics."""
        return self.semantics.extended_verify(state, argument, eval_point)

    def find_verifiers_and_falsifiers(self, argument, eval_point):
        """Finds the verifiers and falsifiers for a negated statement."""
        arg_V, arg_F = argument.proposition.find_proposition()
        return arg_F, arg_V

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the negation operator with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class AndOperator(syntactic.Operator):
    """Implementation of logical conjunction (∧).
    
    This operator represents the logical AND operation. A ∧ B is true when both
    A and B are true, and false otherwise. In hyperintensional semantics, the
    verifiers are the fusion of verifiers from both conjuncts.
    """

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for conjunction at an evaluation point."""
        return z3.And(
            self.semantics.true_at(leftarg, eval_point),
            self.semantics.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for conjunction at an evaluation point."""
        return z3.Or(
            self.semantics.false_at(leftarg, eval_point),
            self.semantics.false_at(rightarg, eval_point)
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for conjunction in the extended semantics."""
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("and_verify_x", N)
        y = z3.BitVec("and_verify_y", N)
        return Exists(
            [x, y],
            z3.And(
                sem.extended_verify(x, leftarg, eval_point),
                sem.extended_verify(y, rightarg, eval_point),
                state == sem.fusion(x, y)
            )
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for conjunction in the extended semantics."""
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("and_falsify_x", N)
        y = z3.BitVec("and_falsify_y", N)
        return z3.Or(
            sem.extended_falsify(state, leftarg, eval_point),
            sem.extended_falsify(state, rightarg, eval_point),
            Exists(
                [x, y],
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(y, rightarg, eval_point),
                    state == sem.fusion(x, y)
                )
            )
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for a conjunction."""
        left_V, left_F = left_sent_obj.proposition.find_proposition()
        right_V, right_F = right_sent_obj.proposition.find_proposition()
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        return product(left_V, right_V), coproduct(left_F, right_F)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the conjunction operator with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class OrOperator(syntactic.Operator):
    """Implementation of logical disjunction (∨).
    
    This operator represents the logical OR operation. A ∨ B is true when at least
    one of A or B is true, and false when both are false. In hyperintensional
    semantics, the verifiers are the coproduct of verifiers from both disjuncts.
    """

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for disjunction at an evaluation point."""
        return z3.Or(
            self.semantics.true_at(leftarg, eval_point),
            self.semantics.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for disjunction at an evaluation point."""
        return z3.And(
            self.semantics.false_at(leftarg, eval_point),
            self.semantics.false_at(rightarg, eval_point)
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for disjunction in the extended semantics."""
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("or_verify_x", N)
        y = z3.BitVec("or_verify_y", N)
        return z3.Or(
            sem.extended_verify(state, leftarg, eval_point),
            sem.extended_verify(state, rightarg, eval_point),
            Exists(
                [x, y],
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(y, rightarg, eval_point),
                    state == sem.fusion(x, y)
                )
            )
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for disjunction in the extended semantics."""
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("or_falsify_x", N)
        y = z3.BitVec("or_falsify_y", N)
        return Exists(
            [x, y],
            z3.And(
                sem.extended_falsify(x, leftarg, eval_point),
                sem.extended_falsify(y, rightarg, eval_point),
                state == sem.fusion(x, y)
            )
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for a disjunction."""
        left_V, left_F = left_sent_obj.proposition.find_proposition()
        right_V, right_F = right_sent_obj.proposition.find_proposition()
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        return coproduct(left_V, right_V), product(left_F, right_F)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the disjunction operator with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class TopOperator(syntactic.Operator):
    """Implementation of the top/tautology operator (⊤).
    
    This operator represents logical truth. ⊤ is always true regardless of the
    evaluation point or model. It has the null state as its sole verifier.
    """

    name = "\\top"
    arity = 0

    def true_at(self, eval_point):
        """Defines truth conditions for top at an evaluation point."""
        return z3.BoolVal(True)

    def false_at(self, eval_point):
        """Defines falsity conditions for top at an evaluation point."""
        return z3.BoolVal(False)

    def extended_verify(self, state, eval_point):
        """Defines verification conditions for top in the extended semantics."""
        return state == state

    def extended_falsify(self, state, eval_point):
        """Defines falsification conditions for top in the extended semantics."""
        return z3.BoolVal(False)

    def find_verifiers_and_falsifiers(self, eval_point):
        """Finds the verifiers and falsifiers for top."""
        return set(self.semantics.all_states), set()

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the top operator with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BotOperator(syntactic.Operator):
    """Implementation of the bottom/contradiction operator (⊥).
    
    This operator represents logical falsehood. ⊥ is always false regardless of the
    evaluation point or model. It has the null state as its sole falsifier.
    """

    name = "\\bot"
    arity = 0

    def true_at(self, eval_point):
        """Defines truth conditions for bottom at an evaluation point."""
        return z3.BoolVal(False)

    def false_at(self, eval_point):
        """Defines falsity conditions for bottom at an evaluation point."""
        return z3.BoolVal(True)

    def extended_verify(self, state, eval_point):
        """Defines verification conditions for bottom in the extended semantics."""
        return z3.BoolVal(False)

    def extended_falsify(self, state, eval_point):
        """Defines falsification conditions for bottom in the extended semantics."""
        return state == self.semantics.null_state

    def find_verifiers_and_falsifiers(self, eval_point):
        """Finds the verifiers and falsifiers for bottom."""
        return set(), {self.semantics.null_state}

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the bottom operator with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class ConditionalOperator(syntactic.DefinedOperator):
    """Implementation of the material conditional (→).
    
    This operator represents the material conditional. A → B is equivalent to
    ¬A ∨ B. It is false only when A is true and B is false.
    """

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        """Defines the conditional as negation of antecedent or consequent."""
        return [OrOperator, [NegationOperator, leftarg], rightarg]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the conditional operator with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BiconditionalOperator(syntactic.DefinedOperator):
    """Implementation of the biconditional (↔).
    
    This operator represents the biconditional. A ↔ B is equivalent to
    (A → B) ∧ (B → A). It is true when both A and B have the same truth value.
    """

    name = "\\leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        """Defines the biconditional as conjunction of two conditionals."""
        return [AndOperator, [ConditionalOperator, leftarg, rightarg], [ConditionalOperator, rightarg, leftarg]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the biconditional operator with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


def get_operators():
    """
    Get all extensional operators.
    
    Returns:
        dict: Dictionary mapping operator names to operator classes
    """
    return {
        "\\neg": NegationOperator,
        "\\wedge": AndOperator,
        "\\vee": OrOperator,
        "\\top": TopOperator,
        "\\bot": BotOperator,
        "\\rightarrow": ConditionalOperator,
        "\\leftrightarrow": BiconditionalOperator,
    }