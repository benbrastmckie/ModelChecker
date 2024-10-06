from z3 import (
    And,
    BitVec,
    BitVecs,
    BitVecSort,
    BitVecVal,
    BoolSort,
    Function,
    Implies,
    Not,
    Or,
)

from syntax import AtomSort

from hidden_things import (
    Operator,
    Proposition,
)

from hidden_helpers import (
    ForAll,
    Exists,
)

class Semantics:
    """Includes the semantic primitives, semantic definitions, frame
    constraints, truth and falsity theories, and premise/conclusion behavior."""

    def __init__(self, N):
        self.N = N
        self.verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
        self.falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())
        self.possible = Function("possible", BitVecSort(N), BoolSort())
        self.main_world = BitVec("w", N)
        x, y = BitVecs("frame_x frame_y", N)
        self.frame_constraints = [
            ForAll(
                [x, y],
                Implies(And(self.possible(y), self.is_part_of(x, y)), self.possible(x)),
            ),
            # NOTE: not needed give that bitvector spaces are complete because finite
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
        return And(Not(bit_s == 0), self.is_part_of(bit_s, bit_t))

    def compatible(self, bit_x, bit_y):
        """the fusion of bit_x and bit_y is possible
        returns a Z3 constraint"""
        return self.possible(self.fusion(bit_x, bit_y))

    def maximal(self, bit_w):
        """bit_w includes all compatible states as parts.
        returns a Z3 constraint"""
        x = BitVec("max_x", self.N)
        return ForAll(
            x,
            Implies(
                self.compatible(x, bit_w),
                self.is_part_of(x, bit_w),
            ),
        )

    def is_world(self, bit_w):
        """bit_w is both possible and maximal.
        returns a Z3 constraint"""
        return And(
            self.possible(bit_w),
            self.maximal(bit_w),
        )

    def max_compatible_part(self, bit_x, bit_w, bit_y):
        """bit_x is the biggest part of bit_w that is compatible with bit_y.
        returns a Z3 constraint"""
        z = BitVec("max_part", self.N)
        return And(
            self.is_part_of(bit_x, bit_w),
            self.compatible(bit_x, bit_y),
            ForAll(
                z,
                Implies(
                    And(
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
        z = BitVec("alt_z", self.N)
        return And(
            self.is_world(bit_u),
            self.is_part_of(bit_y, bit_u),
            And(self.is_part_of(z, bit_u), self.max_compatible_part(z, bit_w, bit_y)),
        )

    def true_at(self, prefix_sentence, eval_world):
        if len(prefix_sentence) == 1 and "\\" not in str(prefix_sentence[0]):
            sent = prefix_sentence[0]
            x = BitVec("t_atom_x", self.N)
            return Exists(x, And(self.is_part_of(x, eval_world), self.verify(x, sent)))
        operator = prefix_sentence[0]
        args = prefix_sentence[1:]
        return operator.true_at(*args, eval_world)

    def false_at(self, prefix_sentence, eval_world):
        if len(prefix_sentence) == 1 and "\\" not in str(prefix_sentence[0]):
            sent = prefix_sentence[0]
            x = BitVec("f_atom_x", self.N)
            return Exists(x, And(self.is_part_of(x, eval_world), self.falsify(x, sent)))
        operator = prefix_sentence[0]
        args = prefix_sentence[1:]
        return operator.false_at(*args, eval_world)


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
        x = BitVec("prop_x", semantics.N)
        y = BitVec("prop_y", semantics.N)
        non_null_constraints = [
            Not(semantics.verify(0, atom)),
            Not(semantics.falsify(0, atom)),
        ]
        classical_constraints = [
            ForAll(
                [x, y],
                Implies(
                    And(semantics.verify(x, atom), semantics.verify(y, atom)),
                    semantics.verify(semantics.fusion(x, y), atom),
                ),
            ),
            ForAll(
                [x, y],
                Implies(
                    And(semantics.falsify(x, atom), semantics.falsify(y, atom)),
                    semantics.falsify(semantics.fusion(x, y), atom),
                ),
            ),
            ForAll(
                [x, y],
                Implies(
                    And(semantics.verify(x, atom), semantics.falsify(y, atom)),
                    Not(semantics.compatible(x, y)),
                ),
            ),
            ForAll(
                x,
                Implies(
                    semantics.possible(x),
                    Exists(
                        y,
                        And(
                            semantics.compatible(x, y),
                            Or(semantics.verify(y, atom), semantics.falsify(y, atom)),
                        ),
                    ),
                ),
            ),
        ]
        constraints = classical_constraints
        if non_null:
            constraints += non_null_constraints
        return constraints

    # B: I changed this name to avoid confusion with find_verifiers_and_falsifiers in operators
    def find_proposition(self):
        # if not(self.verifiers is None and self.falsifiers is None):
        #     return
        # M: not sure if the above helps
        # B: perhaps we could raise an error if there are no verifiers or falsifiers?
        # M: this is a remnant of the attempt explained in the long comment below
        all_bits = self.model_structure.all_bits
        model = self.model_structure.z3_model
        sem = self.semantics
        if len(self.prefix_sentence) == 1:
            atom = self.prefix_sentence[0]
            V = {bit for bit in all_bits if model.evaluate(sem.verify(bit, atom))}
            F = {bit for bit in all_bits if model.evaluate(sem.falsify(bit, atom))}
            return V, F
        operator, prefix_args = self.prefix_sentence[0], self.prefix_sentence[1:]

        # # NOTE: this seems very close; just needs debugging and build prop dictionary here
        # # B: might as well add to proposition dictionary here
        # current_props = {str(p.prefix_sentence):p for p in self.model_structure.all_propositions}
        # children_subprops = []
        # for arg in prefix_args:
        #     if str(arg) in current_props:
        #         children_subprops.append(current_props[str(arg)])
        #     else:
        #         children_subprops.append(Proposition(arg, self.model_structure))

        children_subprops = [Defined(arg, self.model_structure) for arg in prefix_args]
        return operator.find_verifiers_and_falsifiers(*children_subprops)

    def truth_or_falsity_at_world(self, world):
        semantics = self.model_structure.model_setup.semantics
        z3_model = self.model_structure.z3_model
        for bit in self.verifiers:
            if z3_model.evaluate(semantics.is_part_of(bit, world)):
                return True
        return False


class AndOperator(Operator):
    """doc string place holder"""

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return And(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return Or(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))

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
        return Or(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return And(
            sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world)
        )

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


class TopOperator(Operator):
    """doc string place holder"""

    name = "\\top"
    arity = 0

    def true_at(
        self, no_args, eval_world
    ):  # for consistency with recursive call in Semantics class
        """doc string place holder"""
        N = self.semantics.N
        x = BitVec("top_x", N)
        return  # TODO (this and all below)
        # return Exists(x, self.semantics.is_part_of(x, eval_world))
        # B: the way this goes in the semantics is that \top is verified by the null state which
        # is a part of every world state, and so \top is true at every world. so perhaps what this
        # should do is say that there is a part of eval_world which makes \top true.

    def false_at(self, no_args, eval_world):  # see true_at comment
        """doc string place holder"""
        N = self.semantics.N
        return BitVecVal(0, N) == BitVecVal(1, N)
        # B: the way it goes in the semantics is that \top has no falsifiers and so there is no
        # part of any world which makes it false. so perhaps what this should do is say that there
        # is a part of eval_world which makes \top false.

    def find_verifiers_and_falsifiers(self, argprop):
        # B: V is the set containing just the null state and F is empty
        pass


class BotOperator(Operator):
    """doc string place holder"""

    name = "\\bot"
    arity = 0

    def true_at(self, no_args, eval_world):  # see comment at true_at for TopOperator
        """doc string place holder"""
        N = self.semantics.N
        return BitVecVal(0, N) == BitVecVal(1, N)
        # B: similar comments apply as in \top

    def false_at(self, no_args, eval_world):  # see comment at true_at for TopOperator
        """doc string place holder"""
        N = self.semantics.N
        return BitVecVal(1, N) == BitVecVal(1, N)
        # B: similar comments apply as in \top

    def find_verifiers_and_falsifiers(self, argprop):
        # B: V is the set containing just the full state and F is the set of all states
        pass
