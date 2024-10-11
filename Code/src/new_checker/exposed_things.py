# M: Thought: might it not be a bad idea to do import z3 instead?
# if this file is going to be the example file for user-made semantics etc
# then it'd be nice if it were easily idenfiable what things are user defined
# (meaning they need to define) and what things come from Z3. 
# if we do import z3 instead of from z3 import (...), then everything imported
# from z3 will have z3. before it in the code, making it very clear that it
# comes from z3.
# B: that's a great idea!

import z3

# NOTE: go in API
from hidden_things import (
    Operator,
    DerivedOperator,
    Proposition,
)

# NOTE: go in API
from hidden_helpers import (
    AtomSort,
    ForAll,
    Exists,
)


class Semantics:
    """Includes the semantic primitives, semantic definitions, frame
    constraints, truth and falsity theories, and premise/conclusion behavior."""

    def __init__(self, N):
        self.N = N
        self.verify = z3.Function("verify", z3.BitVecSort(N), AtomSort, z3.BoolSort())
        self.falsify = z3.Function("falsify", z3.BitVecSort(N), AtomSort, z3.BoolSort())
        self.possible = z3.Function("possible", z3.BitVecSort(N), z3.BoolSort())
        self.main_world = z3.BitVec("w", N)
        x, y = z3.BitVecs("frame_x frame_y", N)
        self.frame_constraints = [
            ForAll(
                [x, y],
                z3.Implies(z3.And(self.possible(y), self.is_part_of(x, y)), self.possible(x)),
            ),
            # NOTE: not needed give that bitvector spaces are complete because finite
            # worth keeping around for now to do some benchmark testing on later
            # ForAll([x, y], Exists(z, self.fusion(x, y) == z)), # M: is this necessary?
            self.is_world(self.main_world),
        ]
        self.premise_behavior = self.true_at
        self.conclusion_behavior = self.false_at

    def fusion(self, bit_s, bit_t):
        """the result of taking the maximum for each index in bit_s and bit_t
        returns a Z3 constraint"""
        return bit_s | bit_t

    def is_part_of(self, bit_s, bit_t):
        """the fusion of bit_s and bit_t is identical to bit_t
        returns a Z3 constraint"""
        return self.fusion(bit_s, bit_t) == bit_t

    def non_null_part_of(self, bit_s, bit_t):
        """bit_s verifies atom and is not the null state
        returns a Z3 constraint"""
        return z3.And(z3.Not(bit_s == 0), self.is_part_of(bit_s, bit_t))

    def compatible(self, bit_x, bit_y):
        """the fusion of bit_x and bit_y is possible
        returns a Z3 constraint"""
        return self.possible(self.fusion(bit_x, bit_y))

    def maximal(self, bit_w):
        """bit_w includes all compatible states as parts.
        returns a Z3 constraint"""
        x = z3.BitVec("max_x", self.N)
        return ForAll(
            x,
            z3.Implies(
                self.compatible(x, bit_w),
                self.is_part_of(x, bit_w),
            ),
        )

    def is_world(self, bit_w):
        """bit_w is both possible and maximal.
        returns a Z3 constraint"""
        return z3.And(
            self.possible(bit_w),
            self.maximal(bit_w),
        )

    def max_compatible_part(self, bit_x, bit_w, bit_y):
        """bit_x is the biggest part of bit_w that is compatible with bit_y.
        returns a Z3 constraint"""
        z = z3.BitVec("max_part", self.N)
        return z3.And(
            self.is_part_of(bit_x, bit_w),
            self.compatible(bit_x, bit_y),
            ForAll(
                z,
                z3.Implies(
                    z3.And(
                        self.is_part_of(z, bit_w),
                        self.compatible(z, bit_y),
                        self.is_part_of(bit_x, z),
                    ),
                    bit_x == z,
                ),
            ),
        )

    def is_alternative(self, bit_u, bit_y, bit_w):
        """
        bit_u is a world that is the alternative that results from imposing state bit_y on
        world bit_w.
        returns a Z3 constraint
        """
        z = z3.BitVec("alt_z", self.N)
        return z3.And(
            self.is_world(bit_u),
            self.is_part_of(bit_y, bit_u),
            z3.And(self.is_part_of(z, bit_u), self.max_compatible_part(z, bit_w, bit_y)),
        )

    def true_at(self, prefix_sentence, eval_world):
        """
        prefix_sentence is always a list, eval world a BitVector
        """
        if len(prefix_sentence) == 1 and "\\" not in str(prefix_sentence[0]):
            sent = prefix_sentence[0]
            x = z3.BitVec("t_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.verify(x, sent)))
        operator = prefix_sentence[0]
        args = prefix_sentence[1:]
        return operator.true_at(*args, eval_world)

    def false_at(self, prefix_sentence, eval_world):
        if len(prefix_sentence) == 1 and "\\" not in str(prefix_sentence[0]):
            sent = prefix_sentence[0]
            x = z3.BitVec("f_atom_x", self.N)
            return Exists(x, z3.And(self.is_part_of(x, eval_world), self.falsify(x, sent)))
        operator = prefix_sentence[0]
        args = prefix_sentence[1:]
        return operator.false_at(*args, eval_world=eval_world)


class Defined(Proposition):
    """Defines the proposition assigned to the sentences of the language.
    all user has to keep for their own class is super().__init__ and super().__poster_init__
    in the __init__ method.
    """

    def __init__(self, prefix_sentence, model_structure):
        super().__init__(prefix_sentence, model_structure)
        self.verifiers, self.falsifiers = self.find_proposition()

    def __eq__(self, other):
        if (
            self.verifiers == other.verifiers
            and self.falsifiers == other.falsifiers
            and str(self.prefix_sentence) == str(other.prefix_sentence)
        ):
            return True
        return False

    # B: eliminated model_setup as an argument by initializing non_null
    def proposition_constraints(self, atom):
        """Currently does not have contingent proposition constraints."""
        semantics = self.semantics
        non_null = self.non_null
        x = z3.BitVec("prop_x", semantics.N)
        y = z3.BitVec("prop_y", semantics.N)
        non_null_constraints = [
            z3.Not(semantics.verify(0, atom)),
            z3.Not(semantics.falsify(0, atom)),
        ]
        classical_constraints = [
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.verify(x, atom), semantics.verify(y, atom)),
                    semantics.verify(semantics.fusion(x, y), atom),
                ),
            ),
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.falsify(x, atom), semantics.falsify(y, atom)),
                    semantics.falsify(semantics.fusion(x, y), atom),
                ),
            ),
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(semantics.verify(x, atom), semantics.falsify(y, atom)),
                    z3.Not(semantics.compatible(x, y)),
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    semantics.possible(x),
                    Exists(
                        y,
                        z3.And(
                            semantics.compatible(x, y),
                            z3.Or(semantics.verify(y, atom), semantics.falsify(y, atom)),
                        ),
                    ),
                ),
            ),
        ]
        constraints = classical_constraints
        if non_null:
            constraints += non_null_constraints
        return constraints

    def find_proposition(self):
        all_bits = self.model_structure.all_bits
        model = self.model_structure.z3_model
        sem = self.semantics
        if len(self.prefix_sentence) == 1:
            atom = self.prefix_sentence[0]
            V = {bit for bit in all_bits if model.evaluate(sem.verify(bit, atom))}
            # B: I managed to get an error here
            F = {bit for bit in all_bits if model.evaluate(sem.falsify(bit, atom))}
            return V, F
        operator, prefix_args = self.prefix_sentence[0], self.prefix_sentence[1:]
        children_subprops = [Defined(arg, self.model_structure) for arg in prefix_args]
        return operator.find_verifiers_and_falsifiers(*children_subprops)
        # # NOTE: this seems very close; just needs debugging and build prop dictionary here
        # # B: might as well add to proposition dictionary here
        # current_props = {str(p.prefix_sentence):p for p in self.model_structure.all_propositions}
        # children_subprops = []
        # for arg in prefix_args:
        #     if str(arg) in current_props:
        #         children_subprops.append(current_props[str(arg)])
        #     else:
        #         children_subprops.append(Proposition(arg, self.model_structure))


    def truth_value_at(self, world):
        semantics = self.model_structure.model_setup.semantics
        z3_model = self.model_structure.z3_model
        for ver_bit in self.verifiers:
            if z3_model.evaluate(semantics.is_part_of(ver_bit, world)):
                return True
        return False
        # DISCUSS: I tried to add this code but ran into trouble
        # # M: this for loop was in old def of truth_value_at. Is it still necessary?
        # # B: i was worried about it assuming a sentence is false just because
        # # it didn't find a verifier. now it raises an error if no ver or fal bits 
        # for fal_bit in self.verifiers:
        #     if z3_model.evaluate(semantics.is_part_of(fal_bit, world)):
        #         return False
        # # B: what should 'world' be to print as a state?
        # raise ValueError(f"The world {world} has no verifier or falsifier for {self.name}")


class AndOperator(Operator):
    """doc string place holder"""

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return z3.And(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return z3.Or(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))

    def find_verifiers_and_falsifiers(self, leftprop, rightprop):
        Y_V, Y_F = leftprop.find_proposition()
        Z_V, Z_F = rightprop.find_proposition()
        return (self.product(Y_V, Z_V), self.coproduct(Y_F, Z_F))


class OrOperator(Operator):
    """doc string place holder"""

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return z3.Or(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return z3.And(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))

    def find_verifiers_and_falsifiers(self, leftprop, rightprop):
        Y_V, Y_F = leftprop.find_proposition()
        Z_V, Z_F = rightprop.find_proposition()
        return (self.coproduct(Y_V, Z_V), self.product(Y_F, Z_F))


class NegOperator(Operator):
    """doc string place holder"""

    name = "\\neg"
    arity = 1

    def true_at(self, arg, eval_world):
        """doc string place holder"""
        return self.semantics.false_at(arg, eval_world)

    def false_at(self, arg, eval_world):
        """doc string place holder"""
        return self.semantics.true_at(arg, eval_world)

    def find_verifiers_and_falsifiers(self, argprop):
        Y_V, Y_F = argprop.find_proposition()
        return (Y_F, Y_V)


class ConditionalOperator(DerivedOperator):
    name = "\\rightarrow"
    arity = 2
    # @staticmethod # could also be defined with @classmethod, though slightly differently
    def derived_definition(self, leftarg, rightarg):
        return [OrOperator, [NegOperator, leftarg], rightarg]

        # M: hmm that's odd, this shouldn't be an instance method
        # M: attempted to fix that?
        # LINTER: Ok so now it says: Method "derived_definition" overrides class "DerivedOperator" in an incompatible manner 
        # Return type mismatch: base method returns "None", override returns type "list[Unknown]"
        # B: I returned an empty list in the definition of derived_definition in ConditionalOperator
        # and this seems to answer all the linter errors once I added 'self' which is nice to stay
        # consistent

    # M: seems that to avoid the linter issues there are a couple solns:
        # 1. put a decorator on top of the definition (liek @staticmethod or @classmethod). 
        # disadvantage: not something a beginner would understand, though certainly easy to execute
        # I've left it just to show what it would look like
            # 1b. @classmethod. disadvantage: kind of just kicking the problem of misleadingly
            # putting self in the definition to putting another confusing thing in there
            # 1a. @staticmethod. Advantage: no need to put self or cls in the function def
            # B: I feel like having 'self' as an argument is something that would be good to
            # maintain for consistency (and something users will have to learn to live with)

        # 2. define derived_definition as a class property
            # 2a. define it as a lambda function
            # 2b. assign it to a function defined outside the scope of the class. disadvantage: 
            # you have to define the thing elsewhere which is not practical

        # 3. define it as an instance method (with self). Advantage: familiar syntax. Disadvantage:
        # self will never be used in the derived definition, and what an operator instance is 
        # good for—the semantics—is not needed for the derived definitions
        # B: this seems like the best option, but definitely good to discuss (DISCUSS)

class BiconditionalOperator(DerivedOperator):
    name = "\\leftrightarrow"
    arity = 2
    def derived_definition(self, leftarg, rightarg):
        right_to_left = [ConditionalOperator, leftarg, rightarg]
        left_to_right = [ConditionalOperator, rightarg, leftarg]
        return [AndOperator, right_to_left, left_to_right]


class TopOperator(Operator):
    """doc string place holder"""

    name = "\\top"
    arity = 0

    def true_at(
        self, no_args, eval_world
    ):  # for consistency with recursive call in Semantics class
        """doc string place holder"""
        N = self.semantics.N
        x = z3.BitVec("top_x", N)
        return  # TODO (this and all below)
        # return Exists(x, self.semantics.is_part_of(x, eval_world))
        # B: the way this goes in the semantics is that \top is verified by the null state which
        # is a part of every world state, and so \top is true at every world. so perhaps what this
        # should do is say that there is a part of eval_world which makes \top true.

    def false_at(self, no_args, eval_world):  # see true_at comment
        """doc string place holder"""
        N = self.semantics.N
        return z3.BitVecVal(0, N) == z3.BitVecVal(1, N)
        # B: the way it goes in the semantics is that \top has no falsifiers and so there is no
        # part of any world which makes it false. so perhaps what this should do is say that there
        # is a part of eval_world which makes \top false.

    def find_verifiers_and_falsifiers(self, argprop):
        # B: V is the set containing just the null state and F is empty
        # B: I think it would be good to define this proposition and refer here
        # would be good to DISCUSS how best to do that
        pass


class BotOperator(Operator):
    """doc string place holder"""

    name = "\\bot"
    arity = 0

    def true_at(self, no_args, eval_world):  # see comment at true_at for TopOperator
        """doc string place holder"""
        N = self.semantics.N
        return z3.BitVecVal(0, N) == z3.BitVecVal(1, N)
        # B: similar comments apply as in \top

    def false_at(self, no_args, eval_world):  # see comment at true_at for TopOperator
        """doc string place holder"""
        N = self.semantics.N
        return z3.BitVecVal(1, N) == z3.BitVecVal(1, N)
        # B: similar comments apply as in \top

    def find_verifiers_and_falsifiers(self, argprop):
        # B: V is the set containing just the full state and F is the set of all states
        pass
