##########################
### DEFINE THE IMPORTS ###
##########################

import z3

from model_checker.utils import (
    ForAll,
    Exists,
)
from model_checker import syntactic


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
        """Returns a Z3 formula that is satisfied when the state verifies leftarg and rightarg at eval_point.
        
        Args:
            state: The state to check for verification
            leftarg: The left argument of the conjunction
            rightarg: The right argument of the conjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world at which to evaluate the sentence
                
        Returns:
            Z3 formula that is satisfied when state verifies the conjunction at eval_point
        """
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
        """Returns a Z3 formula that is satisfied when the state verifies leftarg or rightarg at eval_point.
        
        Args:
            state: The state to check for verification
            leftarg: The left argument of the disjunction
            rightarg: The right argument of the disjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world at which to evaluate the sentence
                
        Returns:
            Z3 formula that is satisfied when state verifies the disjunction at eval_point
        """
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_point),
            self.semantics.extended_verify(state, rightarg, eval_point)
            # Same as bilateral except no And in definition
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
        """Returns a Z3 formula that is satisfied when the state verifies the identity between leftarg and rightarg at eval_point.
        
        Args:
            state: The state to check for verification
            leftarg: The left argument of the identity relation
            rightarg: The right argument of the identity relation
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world at which to evaluate the sentence
                
        Returns:
            Z3 formula that is satisfied when state verifies the identity relation at eval_point
        """
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return {self.semantics.null_state} if Y_V == Z_V else set()
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class ExclusionOperatorBase(syntactic.Operator):
    """doc string place holder"""

    name = "\\exclude"
    arity = 1

    def true_at(self, arg, eval_point):
        """Returns a Z3 formula that is satisfied when the exclusion of arg is true at eval_point.
        
        Args:
            arg: The argument to exclude
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world at which to evaluate the sentence
                
        Returns:
            Z3 formula that is satisfied when the exclusion of arg is true at eval_point
        """
        x = z3.BitVec(f"ver \\exclude {arg}", self.semantics.N)
        return Exists(
            x,
            z3.And(
                self.extended_verify(x, arg, eval_point),
                self.semantics.is_part_of(x, eval_point["world"])
            )
        )

    def find_verifiers(self, argument, eval_point):
        """Returns the set of verifiers for the exclusion of the argument's proposition.
        
        This method evaluates which states actually verify the exclusion formula in the current model,
        not which states could potentially verify it in some model.
        """
        all_states = self.semantics.all_states
        z3_model = argument.proposition.model_structure.z3_model
        
        # Find verifiers by evaluating the formula for each state
        result = set()
        for state in all_states:
            # Check if this state verifies the exclusion formula in the current model
            formula = self.extended_verify(state, argument, eval_point)
            eval_result = z3_model.evaluate(formula)
            
            if z3.is_true(eval_result):
                result.add(state)
                
        return result

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class ExclusionOperatorQuantifyArrays(ExclusionOperatorBase):

    name = "\\exclude"
    arity = 1

    def extended_verify(self, state, argument, eval_point):
        """Returns a Z3 formula that is satisfied when the state verifies the exclusion of the argument at the eval_point.
        
        This implementation quantifies over Z3 Arrays, providing a way to represent the exclusion function.
        
        Args:
            state: The state to check for verification
            argument: The argument to exclude
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world at which to evaluate the sentence
                
        Returns:
            Z3 formula that is satisfied when state verifies the exclusion relation at eval_point
        """
        # Abbreviations
        semantics = self.semantics
        N = semantics.N
        extended_verify = semantics.extended_verify
        excludes = semantics.excludes
        is_part_of = semantics.is_part_of
        counter = semantics.counter
        semantics.counter += 1
        # Use consistent name 'h' for all arrays to make extraction easier
        h = z3.Array(f"h", z3.BitVecSort(N), z3.BitVecSort(N))
        
        x, y, z, u, v = z3.BitVecs("excl_ver_x excl_ver_y excl_ver_z excl_ver_u excl_ver_v", N)

        return z3.Exists(h, z3.And(
            # Condition 1: For every verifier x of argument, there is a part y of x where h[x] excludes y
            ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), 
                                Exists(y, z3.And(is_part_of(y, x), excludes(h[x], y))))),
            
            # Upper Bound: For every verifier x of argument, h[x] is part of state
            ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), 
                                is_part_of(h[x], state))),
            
            # Least Upper Bound: state is the smallest state that satisfies the UB condition
            ForAll(z, z3.Implies(
                ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(h[x], z))), 
                is_part_of(state, z)))
            ))
    

class ExclusionOperatorQuantifyIndices(ExclusionOperatorBase):

    name = "\\exclude"
    arity = 1

    def extended_verify(self, state, argument, eval_point):
        """this implementation quantifies over a bound range of indices. 
        Bound is 2^(N+3). Calculated based on reasonable upper bound estimates for number of
        negations per sentence (2) times number of sentences (4) times number of verifiers (O(n))
        
        Advantages: slow and STEADY wins the race

        Disadvantages: SLOW and steady wins the race
        """
        # Abbreviations
        semantics = self.semantics
        N = semantics.N
        extended_verify = semantics.extended_verify
        excludes = semantics.excludes
        is_part_of = semantics.is_part_of
        # ix = semantics.h_ix
        H = semantics.H
        semantics.counter += 1
        ix = z3.BitVec(f"ix_{semantics.counter}", N)

        x, y, z, u, v = z3.BitVecs("x y z u v", N)

        return z3.Exists(ix, z3.And(
            ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), Exists(y, z3.And(is_part_of(y, x), excludes(H(ix)[x], y))))), # cond 1
            ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(H(ix)[x], state))), # UB
            ForAll(z, z3.Implies(ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(H(ix)[x], z))), is_part_of(state, z))) # LUB
            ))


class ExclusionOperatorBoundedQuantifyIndices(ExclusionOperatorBase):

    name = "\\exclude"
    arity = 1

    def extended_verify(self, state, argument, eval_point):
        """this implementation quantifies over a bound range of indices. 
        Bound is 2^(N+5). Calculated based on reasonable upper bound estimates for number of
        negations per sentence (2) times number of sentences (4) times number of verifiers (O(n)),
        and then adding 2 to that (2^(N+3+2)). 

        The reason for this bound is that the bound for the space of functions is O(n^n), n=2^N,
        which gets huge very fast. So if you want to try quantifying over a bounded set of indices
        to avoid using Z3 quantifiers, this is what you should do. 
        
        Advantages: slow and STEADY wins the race—avoids unpredictable runtime of Z3 quantifiers

        Disadvantages: SLOW and steady wins the race. Also it could be the case that more indices
        than the bound estimate provides are needed. 
        """
        # Abbreviations
        semantics = self.semantics
        N = semantics.N
        extended_verify = semantics.extended_verify
        excludes = semantics.excludes
        is_part_of = semantics.is_part_of
        ix = semantics.B_h_ix
        H = semantics.BH

        x, y, z, u, v = z3.BitVecs("x y z u v", N)

        return Exists(ix, z3.And(
            ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), Exists(y, z3.And(is_part_of(y, x), excludes(H(ix)[x], y))))), # cond 1
            ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(H(ix)[x], state))), # UB
            ForAll(z, z3.Implies(ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(H(ix)[x], z))), is_part_of(state, z))) # LUB
            ))
    

class ExclusionOperatorNameFunctions(ExclusionOperatorBase):

    name = "\\exclude"
    arity = 1

    def extended_verify(self, state, argument, eval_point):
        """this implementation names h functions, using an increasing counter to ensure
        they're distinct. 
        
        Advantages: TYPE HERE

        Disadvantages: TYPE HERE
        """
        # Abbreviations
        semantics = self.semantics
        N = semantics.N
        extended_verify = semantics.extended_verify
        excludes = semantics.excludes
        is_part_of = semantics.is_part_of

        semantics.counter += 1
        h = z3.Function(f"h_{semantics.counter}", z3.BitVecSort(N), z3.BitVecSort(N))
        # print(h, semantics.counter)

        x, y, z, u, v = z3.BitVecs("x y z u v", N)

        # constraint = z3.And(
        #     ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), Exists(y, z3.And(is_part_of(y, x), excludes(h(x), y))))), # cond 1
        #     ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(h(x), state))), # UB
        #     ForAll(z, z3.Implies(ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(h(x), z))), is_part_of(state, z))) # LUB
        #     )
        
        constraint = z3.And(
            ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), Exists(y, z3.And(is_part_of(y, x), excludes(h(x), y))))), # cond 1
            ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(h(x), state))), # UB
            ForAll(z, z3.Implies(ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(h(x), z))), is_part_of(state, z))) # LUB
            )

        if semantics.counter in {1,2,3}:
            print(argument)
            print(constraint)

        return constraint
        # return z3.And(
        #     ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), Exists(y, z3.And(is_part_of(y, x), excludes(h(x), y))))), # cond 1
        #     ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(h(x), state))), # UB
        #     ForAll(z, z3.Implies(ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(h(x), z))), is_part_of(state, z))) # LUB
        #     )
    

class ExclusionOperatorNameArrays(ExclusionOperatorBase):

    name = "\\exclude"
    arity = 1

    def extended_verify(self, state, argument, eval_point):
        """this implementation names h functions, using an increasing counter to ensure
        they're distinct. 
        
        Advantages: TYPE HERE

        Disadvantages: TYPE HERE
        """
        # Abbreviations
        semantics = self.semantics
        N = semantics.N
        extended_verify = semantics.extended_verify
        excludes = semantics.excludes
        is_part_of = semantics.is_part_of

        h = z3.Array(f"h_{semantics.counter}", z3.BitVecSort(N), z3.BitVecSort(N))
        semantics.counter += 1
        # print(semantics.counter)

        x, y, z, u, v = z3.BitVecs("x y z u v", N)

        return z3.And(
            ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), Exists(y, z3.And(is_part_of(y, x), excludes(h[x], y))))), # cond 1
            ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(h[x], state))), # UB
            ForAll(z, z3.Implies(ForAll(x, z3.Implies(extended_verify(x, argument, eval_point), is_part_of(h[x], z))), is_part_of(state, z))) # LUB
            )


QA = ExclusionOperatorQuantifyArrays
QI = ExclusionOperatorQuantifyIndices
BQI = ExclusionOperatorBoundedQuantifyIndices
NF = ExclusionOperatorNameFunctions
NA = ExclusionOperatorNameArrays

ExclusionOperator = QA

exclusion_operators = syntactic.OperatorCollection(
    UniAndOperator, UniOrOperator, ExclusionOperator, # extensional
    UniIdentityOperator, # constitutive
)
