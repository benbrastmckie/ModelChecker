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
        """Defines the extended verification conditions for the exclusion operator.
        
        This function implements the formal semantics of exclusion by defining when a state
        is an extended verifier of an exclusion formula. A state is an extended verifier if:
        
        1. For every extended verifier v of the argument, there exists a part s of v that is 
           excluded by h(v), where h is a function mapping verifiers to states
        2. For all extended verifiers x of the argument, h(x) is a part of the given state
        3. The given state is minimal with respect to condition 2
        
        Args:
            state: A bitvector representing the state to check
            argument: The argument of the exclusion operator
            eval_point: The evaluation point in the model
            
        Returns:
            A Z3 formula that is true iff the state is an extended verifier of the exclusion
            formula at the given evaluation point
        """

        # Abbreviations
        semantics = self.semantics
        N = semantics.N
        extended_verify = semantics.extended_verify
        excludes = semantics.excludes
        is_part_of = semantics.is_part_of

        # NOTE: that Z3 can introduce arbitrary functions demonstrates its expressive power
        h = z3.Function(
            f"h_{(state, argument)}",   # function name
            z3.BitVecSort(N),           # bitvector argument type
            z3.BitVecSort(N)            # bitvector return type
        )

        x, y, z, u, v = z3.BitVecs("x y z u v", N)
        return z3.And(
            ForAll( # 1. for every extended_verifiers x of the argument, there 
                x,  #    is some part y of x where h(x) excludes y                                    
                z3.Implies(
                    extended_verify(x, argument, eval_point), # member of argument's set of verifiers
                    Exists(
                        y,
                        z3.And(
                            is_part_of(y, x),
                            excludes(h(x), y)
                        )
                    )
                )
            ),
            ForAll( # 2. h(z) is a part of the state for all extended_verifiers z of the argument
                z,
                z3.Implies(
                    extended_verify(z, argument, eval_point),
                    is_part_of(h(z), state),
                )
            ),
            ForAll( # 3. the state is the smallest state to satisfy condition 2
                u,
                z3.Implies(
                    ForAll(
                        v,
                        z3.Implies(
                            extended_verify(v, argument, eval_point),
                            is_part_of(h(v), state)
                        )
                    ),
                    is_part_of(state, u)
                )
            )
        )

    def find_verifiers(self, argument, eval_point):
        """Returns the set of precluders for the argument's proposition."""
        return argument.proposition.precluders

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
