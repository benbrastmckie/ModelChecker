from z3 import (
    And,
    BitVec,
    BitVecSort,
    BitVecs,
    BoolSort,
    Exists,
    ForAll,
    Function,
    Implies,
    Not,
    Or,
)
from syntax import AtomSort

class Semantics:
    def __init__(self, N):
        self.N = N
        self.verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
        self.falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())
        self.possible = Function("possible", BitVecSort(N), BoolSort())
        self.operator_dict = {}
        self.w = BitVec("w", N) # what will be the main world. CALLED w, NOT main_world
        x, y, z = BitVecs("frame_x frame_y frame_z", N) # B: this makes sense!
        self.frame_constraints = [
            ForAll([x, y], Implies(And(self.possible(y), self.is_part_of(x, y)), self.possible(x))),
            ForAll([x, y], Exists(z, self.fusion(x, y) == z)),
            self.is_world(self.w),
        ]
        # B: could specify the 'true_at()' and 'false_at()' here so that other users might replace
        # 'false_at' with a function 'Not(true_at())' and wouldn't need to change the behavior
        # methods below. or was something else intended here?
        self.premise_behavior = None
        self.conclusion_behavior = None

    # B: maybe I'm not getting this, but I would have thought the methods here would take a list of
    # prefix_premises and return a conjunction of true_at(prem) for each prem in prefix_premises
    def set_premise_behavior(self, func):
        self.premise_behavior = func

    # B: the conclusion method would be similar but would return a disjunction of false_at(prem)
    # for each prem in prefix_conclusions, but others might change this to Not(true_at(prem))
    def set_conclusion_behavior(self, func):
        self.conclusion_behavior = func

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
    
    def true_at(self, prefix_sentence, eval_world): # NECESSARY
        if len(prefix_sentence) == 1:
            sent = prefix_sentence[0]
            if 'top' not in str(sent)[0]: # top const alr in model, see find_model_constraints
                # M: I'm not entirely sure where to deal with top, this is here only because it
                # was in the old code (hopefully it ends up working just as before too)
                # B: 'top' is really a zero-place operator and looks like sentence letter 
                # one downside to the current implementation is if a user wants to have a sentence
                # like '(andy_toppled \wedge sara_cried)' since 'top' occurs here. maybe best to
                # require operators to be written with a backslash and then make '\top' an operator
                x = BitVec("t_atom_x", self.N)
                return Exists(x, And(self.is_part_of(x, eval_world), self.verify(x, sent)))
        # TODO: change how operators work once that class is made
        operator = self.operator_dict[prefix_sentence[0]] # operator is a dict, the kw passed into add_operator
        args = prefix_sentence[1:]
        return operator['true_at'](*args, eval_world)

    def false_at(self, prefix_sentence, eval_world): # NECESSARY
        if len(prefix_sentence) == 1:
            sent = prefix_sentence[0]
            if 'bot' not in str(sent)[0]: # B: i've added this to match true_at
                x = BitVec("f_atom_x", self.N)
                return Exists(x, And(self.is_part_of(x, eval_world), self.falsify(x, sent))) # REMOVABLE
        # TODO: change how operators work once that class is made
        operator = self.operator_dict[prefix_sentence[0]] # operator is a dict, the kw passed into add_operator
        args = prefix_sentence[1:]
        return operator['false_at'](*args, eval_world)

    def find_model_constraints(self, atom):
        '''
        currently does not have contingent props. commented code (null_cons and skolem, latter of
        which was no longer needed) in addition to contingent props was deleted for space
        '''
        x = BitVec("prop_x", self.N)
        y = BitVec("prop_y", self.N)
        return [
            Not(self.verify(0, atom)), # TODO: M: B, are these necessary? Were not in class_semantics_playground but were in original file
            Not(self.falsify(0, atom)), # (continuing above) not sure if it was an accidental deletion on my part or an actual change
            ForAll(
                [x, y],
                Implies(
                    And(self.verify(x, atom), self.verify(y, atom)), self.verify(self.fusion(x, y), atom)
                ),
            ),
            ForAll(
                [x, y],
                Implies(
                    And(self.falsify(x, atom), self.falsify(y, atom)), self.falsify(self.fusion(x, y), atom)
                ),
            ),
            ForAll(
                [x, y],
                Implies(And(self.verify(x, atom), self.falsify(y, atom)), Not(self.compatible(x, y))),
            ),
            ForAll(
                x,
                Implies(
                    self.possible(x),
                    Exists(
                        y,
                        And(
                            self.compatible(x, y),
                            Or(self.verify(y, atom), self.falsify(y, atom)),
                        ),
                    ),
                ),
            ),
        ]

# TODO: this class could be hidden later
class Operator:
    def __str__(self):
        return self.name # B: Instance of 'Operator' has no 'name' member

    def __eq__(self, other): # currently unused but may be nice to have
        if self.name == other.name and self.arity == other.arity: # B: Attribute 'arity' is unknown
            return True
        return False

class Proposition:
    pass

class AndOperator(Operator):
    """doc string place holder"""

    def __init__(self, semantics):
        self.semantics = semantics
        self.arity = 2
        self.name = '\\wedge'

    # B: this looks great!
    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return And(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return Or(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))

class OrOperator(Operator):
    """doc string place holder"""

    def __init__(self, semantics):
        self.semantics = semantics
        self.arity = 2
        self.name = '\\vee'

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return Or(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def false_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return And(sem.false_at(leftarg, eval_world), sem.false_at(rightarg, eval_world))

class NegOperator(Operator):
    """doc string place holder"""

    def __init__(self, semantics):
        self.semantics = semantics
        self.arity = 1
        self.name = '\\neg'

    def true_at(self, arg, eval_world):
        """doc string place holder"""
        return self.semantics.false_at(arg, eval_world)

    def false_at(self, arg, eval_world):
        """doc string place holder"""
        return self.semantics.true_at(arg, eval_world)
