##########################
### DEFINE THE IMPORTS ###
##########################

import z3

try:  # Try local imports first (for development)
    from src.model_checker.utils import (
        ForAll,
        Exists,
    )
    from src.model_checker import syntactic
except ImportError:
    # Fall back to installed package imports
    from model_checker.utils import (
        ForAll,
        Exists,
    )
    from model_checker import syntactic

class ExclusionOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\exclude"
    arity = 1

    def true_at(self, arg, eval_point):
        """doc string place holder"""
        x = z3.BitVec(f"ver \\exclude {arg}", self.semantics.N) # think this has to be a unique name
        return Exists(
            x,
            z3.And(
                self.extended_verify(x, arg, eval_point),
                self.semantics.is_part_of(x, eval_point)
            )
        )

    def extended_verify(self, state, argument, eval_point):
        sem = self.semantics
        N, extended_verify, excludes = sem.N, sem.extended_verify, sem.excludes
        is_part_of = sem.is_part_of
        h = z3.Function(f"h_{(state, argument)}", z3.BitVecSort(N), z3.BitVecSort(N))
        v, x, y, z, s = z3.BitVecs("v x y z s", N)
        # return self.precludes(state, arg_set)
        return z3.And(
            ForAll( # 1. every extended_verifier v for arg has a part s where
                v,  # h(v) excludes s
                z3.Implies(
                    extended_verify(v, argument, eval_point), # member of argument's set of verifiers
                    Exists(
                        s,
                        z3.And(
                            excludes(h(v), s),
                            is_part_of(s, v)
                        )
                    )
                )
            ),
            ForAll( # 2. h(x) is a part of the state for all extended_veriers x of arg
                x,
                z3.Implies(
                    extended_verify(x, argument, eval_point),
                    is_part_of(h(x), state),
                )
            ),
            ForAll( # 3. the state is the smallest state to satisfy condition 2
                z,
                z3.Implies(
                    ForAll(
                        y,
                        z3.Implies(
                            extended_verify(y, argument, eval_point),
                            is_part_of(h(y), state)
                        )
                    ),
                    z == state
                )
            )
        )

    # # TODO: why doesn't this work?
    # def find_verifiers(self, argument, eval_point):
    #     model = argument.proposition.model_structure.z3_model
    #     all_bits = self.semantics.all_bits
    #     result = set()
    #     for x in all_bits:
    #         # Create and evaluate the formula with the model
    #         formula = self.extended_verify(x, argument, eval_point)
    #         if model.evaluate(formula):
    #             result.add(x)
    #     return result

    # TODO: might help to also find falsifiers here
    def find_verifiers(self, argument, eval_point):
        all_bits = self.semantics.all_bits
        result = set()
        for x in all_bits:
            # Get the extended verification conditions for this bit
            formula = self.extended_verify(x, argument, eval_point)
            # If the formula is True (not a Z3 expression), add x to results
            if formula is True:
                result.add(x)
        return result

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniAndOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\uniwedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """doc string place holder
        args are derived_objects I think, def original_type or derived_object
        (ie of second or third kind)
        """
        sem = self.semantics
        return z3.And(
            sem.true_at(leftarg, eval_point),
            sem.true_at(rightarg, eval_point)
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        x = z3.BitVec("ex_ver_x", self.semantics.N)
        y = z3.BitVec("ex_ver_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                self.semantics.fusion(x, y) == state,
                self.semantics.extended_verify(x, leftarg, eval_point),
                self.semantics.extended_verify(y, rightarg, eval_point),
            ),
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Takes sentences objects as arguments, finds their verifiers and
        falsifiers, and returns the verifiers and falsifiers for the operator"""
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return self.semantics.product(Y_V, Z_V)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniOrOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\univee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        sem = self.semantics
        return z3.Or(
            sem.true_at(leftarg, eval_point), sem.true_at(rightarg, eval_point)
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_point),
            self.semantics.extended_verify(state, rightarg, eval_point),
            # same as bilateral except no And in def
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return Y_V.union(Z_V)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)

class UniIdentityOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\uniequiv"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """doc string place holder"""
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_id_x", N)
        return z3.And(
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(x, rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, rightarg, eval_point),
                    sem.extended_verify(x, leftarg, eval_point)
                ),
            ),
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        return z3.And(
            state == self.semantics.null_bit,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return {self.semantics.null_bit} if Y_V == Z_V else set()
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


exclusion_operators = syntactic.OperatorCollection(
    UniAndOperator, UniOrOperator, ExclusionOperator, # extensional
    UniIdentityOperator, # constitutive
)
