"""
Extensional operators for truth-functional logic.

This module implements the basic extensional logical operators:
- Negation (¨)
- Conjunction (')
- Disjunction (()
- Top (§)
- Bottom (•)
- Material Implication (í)
- Biconditional (î)
"""

import z3

from model_checker.utils import (
    ForAll,
    Exists,
)
from model_checker import syntactic


class NegationOperator(syntactic.Operator):
    """Implementation of logical negation (¨).
    
    This operator implements both intensional truth/falsity conditions and
    hyperintensional verifier/falsifier semantics for logical negation. 
    It flips the truth value of its argument: if A is true, ¨A is false, 
    and if A is false, ¨A is true.
    
    In the hyperintensional semantics, the verifiers of ¨A are the falsifiers of A,
    and the falsifiers of ¨A are the verifiers of A.
    """

    name = "\\neg"
    arity = 1

    def true_at(self, argument, eval_point):
        """Defines truth conditions for negation at an evaluation point."""
        return self.semantics.false_at(argument, eval_point)

    def false_at(self, argument, eval_point):
        """Defines falsity conditions for negation at an evaluation point."""
        return self.semantics.true_at(argument, eval_point)

    def extended_verify(self, state, arg, eval_point):
        """Defines verification conditions for negation in the extended semantics."""
        return self.semantics.extended_falsify(state, arg, eval_point)
    
    def extended_falsify(self, state, arg, eval_point):
        """Defines falsification conditions for negation in the extended semantics."""
        return self.semantics.extended_verify(state, arg, eval_point)

    def find_verifiers_and_falsifiers(self, argument, eval_point):
        """Finds the verifiers and falsifiers for a negation of a proposition."""
        Y_V, Y_F = argument.proposition.find_proposition()
        return Y_F, Y_V

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its argument with proper indentation."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class AndOperator(syntactic.Operator):
    """Implementation of logical conjunction (').
    
    This operator implements both intensional truth/falsity conditions and
    hyperintensional verifier/falsifier semantics for conjunction. A conjunction
    A ' B is true when both A and B are true, and false when either A or B is false.
    """

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for conjunction at an evaluation point."""
        sem = self.semantics
        return z3.And(
            sem.true_at(leftarg, eval_point),
            sem.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for conjunction at an evaluation point."""
        sem = self.semantics
        return z3.Or(sem.false_at(leftarg, eval_point), sem.false_at(rightarg, eval_point))

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for conjunction in the extended semantics."""
        x = z3.BitVec("ex_and_ver_x", self.semantics.N)
        y = z3.BitVec("ex_and_ver_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                self.semantics.fusion(x, y) == state,
                self.semantics.extended_verify(x, leftarg, eval_point),
                self.semantics.extended_verify(y, rightarg, eval_point),
            )
        )
    
    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for conjunction in the extended semantics."""
        x = z3.BitVec("ex_and_fal_x", self.semantics.N)
        y = z3.BitVec("ex_and_fal_y", self.semantics.N)
        return z3.Or(
            self.semantics.extended_falsify(state, leftarg, eval_point),
            self.semantics.extended_falsify(state, rightarg, eval_point),
            Exists(
                [x, y],
                z3.And(
                    state == self.semantics.fusion(x, y),
                    self.semantics.extended_falsify(x, leftarg, eval_point),
                    self.semantics.extended_falsify(y, rightarg, eval_point),
                ),
            )
        )

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        """Finds the verifiers and falsifiers for a conjunction of two propositions."""
        sem = self.semantics
        Y_V, Y_F = leftarg.proposition.find_proposition()
        Z_V, Z_F = rightarg.proposition.find_proposition()
        return sem.product(Y_V, Z_V), sem.coproduct(Y_F, Z_F)
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class OrOperator(syntactic.Operator):
    """Implementation of logical disjunction (().
    
    This operator implements both intensional truth/falsity conditions and
    hyperintensional verifier/falsifier semantics for disjunction. A disjunction
    A ( B is true when either A or B (or both) are true, and false when both A and B are false.
    """

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for disjunction at an evaluation point."""
        sem = self.semantics
        return z3.Or(sem.true_at(leftarg, eval_point), sem.true_at(rightarg, eval_point))

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for disjunction at an evaluation point."""
        sem = self.semantics
        return z3.And(sem.false_at(leftarg, eval_point), sem.false_at(rightarg, eval_point))

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for disjunction in the extended semantics."""
        x = z3.BitVec("ex_or_ver_x", self.semantics.N)
        y = z3.BitVec("ex_or_ver_y", self.semantics.N)
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_point),
            self.semantics.extended_verify(state, rightarg, eval_point),
            Exists(
                [x, y],
                z3.And(
                    self.semantics.fusion(x, y) == state,
                    self.semantics.extended_verify(x, leftarg, eval_point),
                    self.semantics.extended_verify(y, rightarg, eval_point),
                )
            )
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for disjunction in the extended semantics."""
        x = z3.BitVec("ex_fal_x", self.semantics.N)
        y = z3.BitVec("ex_fal_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                state == self.semantics.fusion(x, y),
                self.semantics.extended_falsify(x, leftarg, eval_point),
                self.semantics.extended_falsify(y, rightarg, eval_point),
            ),
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for a disjunction of two propositions."""
        semantics = self.semantics
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        return semantics.coproduct(Y_V, Z_V), semantics.product(Y_F, Z_F)
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class TopOperator(syntactic.Operator):
    """Implementation of the tautology or top element (§).
    
    This operator represents the logical tautology or 'top' element of the
    propositional lattice. It is always true regardless of the evaluation point.
    """

    name = "\\top"
    arity = 0

    def true_at(self, eval_point):
        """Defines truth conditions for the top element at an evaluation point."""
        return 1 == 1

    def false_at(self, eval_point):
        """Defines falsity conditions for the top element at an evaluation point."""
        return 1 != 1

    def extended_verify(self, state, eval_point):
        """Defines verification conditions for top in the extended semantics."""
        return state == state

    def extended_falsify(self, state, eval_point):
        """Defines falsification conditions for top in the extended semantics."""
        return state == self.semantics.full_state

    def find_verifiers_and_falsifiers(self, eval_point):
        """Finds the verifiers and falsifiers for the top element."""
        return set(self.semantics.all_states), {self.semantics.full_state}

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the top element with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BotOperator(syntactic.Operator):
    """Implementation of the contradiction or bottom element (•).
    
    This operator represents logical contradiction or the 'bottom' element of the
    propositional lattice. It is always false regardless of the evaluation point.
    """

    name = "\\bot"
    arity = 0

    def true_at(self, eval_point):
        """Defines truth conditions for the bottom element at an evaluation point."""
        return 1 != 1

    def false_at(self, eval_point):
        """Defines falsity conditions for the bottom element at an evaluation point."""
        return 1 == 1

    def extended_verify(self, state, eval_point):
        """Defines verification conditions for bottom in the extended semantics."""
        return state != state

    def extended_falsify(self, state, eval_point):
        """Defines falsification conditions for bottom in the extended semantics."""
        return state == self.semantics.null_state

    def find_verifiers_and_falsifiers(self, eval_point):
        """Finds the verifiers and falsifiers for the bottom element."""
        return set(), {self.semantics.null_state}

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the bottom element with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class ConditionalOperator(syntactic.DefinedOperator):
    """Implementation of material implication/conditional (í).
    
    This operator represents the material conditional 'if A then B', defined as
    ¨A ( B. It is true when either A is false or B is true (or both).
    """

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        """Defines the material conditional A í B as ¨A ( B."""
        return [OrOperator, [NegationOperator, leftarg], rightarg]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the conditional with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BiconditionalOperator(syntactic.DefinedOperator):
    """Implementation of material biconditional/equivalence (êí).
    
    This operator represents the material biconditional 'A if and only if B',
    defined as (A í B) ' (B í A). It is true when A and B have the same truth value.
    """

    name = "\\leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        """Defines the material biconditional A êí B as (A í B) ' (B í A)."""
        right_to_left = [ConditionalOperator, leftarg, rightarg]
        left_to_right = [ConditionalOperator, rightarg, leftarg]
        return [AndOperator, right_to_left, left_to_right]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the biconditional with proper indentation and formatting."""
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