"""
Constitutive operators for hyperintensional logic.

This module implements constitutive logical operators:
- Identity (≡)
- Ground (≤)
- Essence (⊑)
- Relevance (≼)
- Reduction (⇒)
"""

import z3

from model_checker.utils import (
    ForAll,
    Exists,
)
from model_checker import syntactic

# Import required operators for defined operators
from ..extensional.operators import AndOperator


class IdentityOperator(syntactic.Operator):
    """Implementation of the identity operator (a).
    
    This operator represents the identity relation between propositions, where
    A a B means that A and B have exactly the same content. Two propositions
    are identical when they have the same verifiers and the same falsifiers.
    """

    name = "\\equiv"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for identity at an evaluation point."""
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("true_identity_x", N)
        return z3.And(
            ForAll(
                x,
                z3.Implies(
                    semantics.extended_verify(x, leftarg, eval_point),
                    semantics.extended_verify(x, rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    semantics.extended_falsify(x, leftarg, eval_point),
                    semantics.extended_falsify(x, rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    semantics.extended_verify(x, rightarg, eval_point),
                    semantics.extended_verify(x, leftarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    semantics.extended_falsify(x, rightarg, eval_point),
                    semantics.extended_falsify(x, leftarg, eval_point)
                ),
            )
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for identity at an evaluation point."""
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("false_identity_x", N)
        return z3.Or(
            Exists(
                x,
                z3.And(
                    semantics.extended_verify(x, leftarg, eval_point),
                    z3.Not(semantics.extended_verify(x, rightarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    semantics.extended_falsify(x, leftarg, eval_point),
                    z3.Not(semantics.extended_falsify(x, rightarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    semantics.extended_verify(x, rightarg, eval_point),
                    z3.Not(semantics.extended_verify(x, leftarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    semantics.extended_falsify(x, rightarg, eval_point),
                    z3.Not(semantics.extended_falsify(x, leftarg, eval_point))
                ),
            )
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for identity in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for identity in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for an identity relation between propositions."""
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if Y_V == Z_V and Y_F == Z_F:
            return {self.semantics.null_state}, set()
        return set(), {self.semantics.null_state}
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the identity relation with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class GroundOperator(syntactic.Operator):
    """Implementation of the ground/disjunctive-part operator (d).
    
    This operator represents the grounding relation between propositions, where
    A d B means that A grounds B or A is a disjunctive-part of B.
    """

    name = "\\leq"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for the ground relation at an evaluation point."""
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("true_ground_x", N)
        y = z3.BitVec("true_ground_y", N)
        return z3.And(
            ForAll(
                [x],
                z3.Implies(
                    semantics.extended_verify(x, leftarg, eval_point),
                    semantics.extended_verify(x, rightarg, eval_point)
                )
            ),
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        semantics.extended_falsify(x, leftarg, eval_point),
                        semantics.extended_falsify(y, rightarg, eval_point)
                    ),
                    semantics.extended_falsify(semantics.fusion(x, y), rightarg, eval_point)
                ),
            ),
            ForAll(
                [x],
                z3.Implies(
                    semantics.extended_falsify(x, rightarg, eval_point),
                    Exists(
                        y,
                        z3.And(
                            semantics.extended_falsify(y, leftarg, eval_point),
                            semantics.is_part_of(y, x),
                        )
                    )
                ),
            ),
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for the ground relation at an evaluation point."""
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("false_ground_x", N)
        y = z3.BitVec("false_ground_y", N)
        return z3.Or(
            Exists(
                [x],
                z3.And(
                    semantics.extended_verify(x, leftarg, eval_point),
                    z3.Not(semantics.extended_verify(x, rightarg, eval_point))
                )
            ),
            Exists(
                [x, y],
                z3.And(
                    semantics.extended_falsify(x, leftarg, eval_point),
                    semantics.extended_falsify(y, rightarg, eval_point),
                    z3.Not(semantics.extended_falsify(semantics.fusion(x, y), rightarg, eval_point))
                ),
            ),
            Exists(
                [x],
                z3.And(
                    semantics.extended_falsify(x, rightarg, eval_point),
                    ForAll(
                        y,
                        z3.Implies(
                            semantics.extended_falsify(y, leftarg, eval_point),
                            z3.Not(semantics.is_part_of(y, x)),
                        )
                    )
                ),
            ),
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for ground relation in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for ground relation in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for a ground relation between propositions."""
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if coproduct(Y_V, Z_V) == Z_V and product(Y_F, Z_F) == Z_F:
            return {self.semantics.null_state}, set()
        return set(), {self.semantics.null_state}

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the ground relation with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class EssenceOperator(syntactic.Operator):
    """Implementation of the essence operator (�).
    
    This operator represents the essence relation between propositions, where
    A � B means that A is the essence of B.
    """

    name = "\\sqsubseteq"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for essence relation at an evaluation point."""
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_seq_x", N)
        y = z3.BitVec("t_seq_y", N)
        return z3.And(
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_verify(x, leftarg, eval_point),
                        sem.extended_verify(y, rightarg, eval_point)
                    ),
                    sem.extended_verify(sem.fusion(x, y), rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, rightarg, eval_point),
                    Exists(
                        y,
                        z3.And(
                            sem.extended_verify(y, leftarg, eval_point),
                            sem.is_part_of(y, x),
                        )
                    )
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(x, rightarg, eval_point)
                )
            )
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for essence relation at an evaluation point."""
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_seq_x", N)
        y = z3.BitVec("f_seq_y", N)
        return z3.Or(
            Exists(
                [x, y],
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(y, rightarg, eval_point),
                    z3.Not(sem.extended_verify(sem.fusion(x, y), rightarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, rightarg, eval_point),
                    ForAll(
                        y,
                        z3.Implies(
                            sem.extended_verify(y, leftarg, eval_point),
                            z3.Not(sem.is_part_of(y, x)),
                        )
                    )
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    z3.Not(sem.extended_falsify(x, rightarg, eval_point))
                )
            )
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for essence relation in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for essence relation in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for an essence relation between propositions."""
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if product(Y_V, Z_V) == Z_V and coproduct(Y_F, Z_F) == Z_F:
            return {self.semantics.null_state}, set()
        return set(), {self.semantics.null_state}
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the essence relation with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class RelevanceOperator(syntactic.Operator):
    """Implementation of the relevance operator (|).
    
    This operator represents the relevance relation between propositions, where
    A | B means that A is relevant to B.
    """

    name = "\\preceq"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for relevance relation at an evaluation point."""
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_peq_x", N)
        y = z3.BitVec("t_peq_y", N)
        return z3.And(
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_verify(x, leftarg, eval_point),
                        sem.extended_verify(y, rightarg, eval_point)
                    ),
                    sem.extended_verify(sem.fusion(x, y), rightarg, eval_point)
                ),
            ),
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_falsify(x, leftarg, eval_point),
                        sem.extended_falsify(y, rightarg, eval_point)
                    ),
                    sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point)
                ),
            ),
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for relevance relation at an evaluation point."""
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_seq_x", N)
        y = z3.BitVec("f_seq_y", N)
        return z3.Or(
            Exists(
                [x, y],
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(y, rightarg, eval_point),
                    z3.Not(sem.extended_verify(sem.fusion(x, y), rightarg, eval_point))
                ),
            ),
            Exists(
                [x, y],
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(y, rightarg, eval_point),
                    z3.Not(sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point))
                ),
            ),
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for relevance relation in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for relevance relation in the extended semantics."""
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for a relevance relation between propositions."""
        product = self.semantics.product
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if product(Y_V, Z_V).issubset(Z_V) and product(Y_F, Z_F).issubset(Z_F):
            return {self.semantics.null_state}, set()
        return set(), {self.semantics.null_state}
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the relevance relation with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class ReductionOperator(syntactic.DefinedOperator):
    """Implementation of the reduction operator (\\Rightarrow).
    
    This operator represents the reduction relation between propositions, where
    A \\Rightarrow B means that A reduces to B. This is defined as the conjunction
    of ground and essence: (A ≤ B) ∧ (A ⊑ B).
    """

    name = "\\Rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):
        """Defines reduction as conjunction of ground and essence."""
        return [AndOperator, [GroundOperator, leftarg, rightarg], [EssenceOperator, leftarg, rightarg]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the reduction operator with proper indentation and formatting."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


def get_operators():
    """
    Get all constitutive operators.
    
    Returns:
        dict: Dictionary mapping operator names to operator classes
    """
    return {
        "\\equiv": IdentityOperator,
        "\\leq": GroundOperator,
        "\\sqsubseteq": EssenceOperator,
        "\\preceq": RelevanceOperator,
        "\\Rightarrow": ReductionOperator,
    }
