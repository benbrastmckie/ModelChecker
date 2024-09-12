from z3 import *
from syntax import AtomSort

class Semantics():
    def __init__(self, N):
        self.N = N
        self.verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
        self.falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())
        self.possible = Function("possible", BitVecSort(N), BoolSort())
        self.operator_dict = {}
        self.w = BitVec("w", N) # what will be the main world
    
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
    
    # TODO: should max_compatible_parts (and similar) also be in here?
    # B: this is particular to my semantics so perhaps belongs here
    # M: so all of above can be moved into the generic Frame class?
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

    # B: this is particular to my semantics so perhaps belongs here
    # B: why is the last line REMOVABLE?
    # B: should 'Exists' be added for 'z' now that we have defined the quantifiers?
    # M: those comments were relics of the old semantics, I just copy/pasted the code from
    # that so any comments also made their way in here. If they're outdated and just hadn't
    # been removed from the master branch then they're also fine to be removed here
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
            And(self.is_part_of(z, bit_u), self.max_compatible_part(z, bit_w, bit_y)), # REMOVABLE
        )

    # B: this looks good!
    def true_at(self, prefix_sentence, eval_world): # NECESSARY
        if len(prefix_sentence) == 1:
            sent = prefix_sentence[0]
            if 'top' not in str(sent)[0]: # top const alr in model, see find_model_constraints
                # M: I'm not entirely sure where to deal with top, this is here only because it
                # was in the old code (hopefully it ends up working just as before too)
                x = BitVec("t_atom_x", self.N)
                return Exists(x, And(self.is_part_of(x, eval_world), self.verify(x, sent))) # REMOVABLE
        operator = self.operator_dict[prefix_sentence[0]] # operator is a dict, the kw passed into add_operator
        args = prefix_sentence[1:]
        return operator['true_at'](*args, eval_world) # B: i assume this is what we want instead of the below
        # M: yes, good catch!

    def false_at(self, prefix_sentence, eval_world): # NECESSARY
        if len(prefix_sentence) == 1:
            sent = prefix_sentence[0]
            if 'bot' not in str(sent)[0]: # B: i've added this to match true_at
                x = BitVec("f_atom_x", self.N)
                return Exists(x, And(self.is_part_of(x, eval_world), self.falsify(x, sent))) # REMOVABLE
        operator = self.operator_dict[prefix_sentence[0]] # operator is a dict, the kw passed into add_operator
        args = prefix_sentence[1:]
        return operator['false_at'](*args, eval_world) # B: i assume this is what we want instead of the below

    def frame_constraints(self): # NECESSARY
        x = BitVec("frame_x", self.N)
        y = BitVec("frame_y", self.N)
        z = BitVec("frame_z", self.N)
        frame_constraints = [
            ForAll([x, y], Implies(And(self.possible(y), self.is_part_of(x, y)), self.possible(x))),
            ForAll([x, y], Exists(z, self.fusion(x, y) == z)),
            self.is_world(self.w),
        ]
        return frame_constraints

    # B: this seems like a good place to start!
    # I think this would be model contraints?
    def proposition_definition(self, atom): # NECESSARY
        '''
        currently does not have contingent props. commented code (null_cons and skolem, latter of
        which was no longer needed) in addition to contingent props was deleted for space
        '''
        x = BitVec("prop_x", self.N)
        y = BitVec("prop_y", self.N)
        return [
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

class Operator():
    pass