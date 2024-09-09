'''
example of what a user would do to create their own semantics following idea explained in
docstring of class_operator_playground.

First, they create a class that is a subclass of the Frame class with all special definitions
they need methods, and any other definitions as attributes (a couple are mandatory).

Then they create a Frame object of that type by defining N. Then they add operators to it with
whatever info they determine an operator needs (this is very loose, can be really whatever they
want at this point, so long as its consistent with their true_at definitions). 

Generally an upside of this approach is that it is very flexible. There are few minimal things
required by a Frame. However this flexibility is also a downside: this file is quite long, at
about 200 lines. Additionally some of the functions the user must currently define are not in Z3
but rather involve substantial python, which makes it not that friendly since if a user only had to
make methods that were pure Z3, they wouldn't need that much python experience. For example the true_at
and false_at functions both have recursion and accessing things from a dict. These are things that
presumably every semantics should have (at leaset bilateral semantics) so maybe those can be moved
to the Frame class as opposed to being required to be defined by the user in their new frame subclass.
(M: I am not sure what those things are, this is my guess at tha, but that would be a major design
choice in this approach)
'''

from class_semantics_playground import *


class BrastMcKieFrame(Frame): # M: couldn't think of a better name for your semantics lol
    def __init__(self, N):
        super().__init__(N)
        self.falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())
        self.assign = Function("assign", BitVecSort(N), AtomSort, BitVecSort(N))
        self.premise_constraint_behavior = self.true_at # NECESSARY
        self.conclusion_constraint_behavior = self.false_at # NECESSARY

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
        x = BitVec("max_x", N)
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
        z = BitVec("max_part", N)
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
        z = BitVec("alt_z", N)
        return And(
            self.is_world(bit_u),
            self.is_part_of(bit_y, bit_u),
            And(self.is_part_of(z, bit_u), self.max_compatible_part(z, bit_w, bit_y)), # REMOVABLE
        )

    def true_at(self, prefix_sentence, eval_world): # NECESSARY
        if len(prefix_sentence) == 1:
                sent = prefix_sentence[0]
                if 'top' not in str(sent)[0]: # top const alr in model, see find_model_constraints
                    x = BitVec("t_atom_x", N)
                    return Exists(x, And(self.is_part_of(x, eval_world), self.verify(x, sent))) # REMOVABLE
        operator = self.operator_dict[prefix_sentence[0]] # operator is a dict, the kw passed into add_operator
        args = prefix_sentence[1:]
        return operator['true_at'](args, eval_world)

    def false_at(self, prefix_sentence, eval_world): # NECESSARY
        if len(prefix_sentence) == 1:
            sent = prefix_sentence[0]
            x = BitVec("f_atom_x", N)
            return Exists(x, And(self.is_part_of(x, eval_world), self.falsify(x, sent))) # REMOVABLE
        operator = self.operator_dict[prefix_sentence[0]] # operator is a dict, the kw passed into add_operator
        args = prefix_sentence[1:]
        return operator['false_at'](*args, eval_world)
    
    def frame_constraints(self): # NECESSARY
        x = BitVec("frame_x", N)
        y = BitVec("frame_y", N)
        z = BitVec("frame_z", N)
        u = BitVec("frame_u", N)
        frame_constraints = [
            ForAll([x, y], Implies(And(self.possible(y), self.is_part_of(x, y)), self.possible(x))),
            ForAll([x, y], Exists(z, self.fusion(x, y) == z)),
            self.is_world(self.w),
        ]
        return frame_constraints
    
    def proposition_definition(self, atom): # NECESSARY
        '''
        currently does not have contingent props. commented code (null_cons and skolem, latter of
        which was no longer needed) in addition to contingent props was deleted for space
        '''
        x = BitVec("prop_x", N)
        y = BitVec("prop_y", N)
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


N = 3
frame = BrastMcKieFrame(N)
frame.add_operator('\\neg',
                   true_at=lambda arg, eval_world: frame.false_at(arg, eval_world),
                   false_at=lambda arg, eval_world: frame.true_at(arg, eval_world),
                   arity=1),
frame.add_operator('\\wedge',
                   true_at=lambda X, Y, eval_world: And(frame.true_at(X, eval_world), frame.true_at(Y, eval_world)),
                   false_at=lambda X, Y, eval_world: Or(frame.false_at(X, eval_world), frame.false_at(Y, eval_world)),
                   arity=2)
frame.add_operator('\\vee',
                   true_at=lambda X, Y, eval_world: Or(frame.true_at(X, eval_world), frame.true_at(Y, eval_world)),
                   false_at=lambda X, Y, eval_world: And(frame.false_at(X, eval_world), frame.false_at(Y, eval_world)),
                   arity=2)

infix_premises = []
infix_conclusions = []
model_setup = ModelSetup(frame, infix_premises, infix_conclusions)
# model_setup.solve() # ... and so on. The rest would ideally proceed as before.
