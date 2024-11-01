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


class BrastMcKieFrame(Frame):

    # B: I commented out assign since I don't think it is needed
    def __init__(self, N):
        super().__init__(N)
        self.verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
        self.falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())
        self.possible = Function("possible", BitVecSort(N), BoolSort())
        self.w = BitVec("w", N) # what will be the main world
        # self.assign = Function("assign", BitVecSort(N), AtomSort, BitVecSort(N))
        self.premise_constraint_behavior = self.true_at
        self.conclusion_constraint_behavior = self.false_at

    # B: some of the following definitions are very general; i wonder if they should be included in
    # the frame definition so as to be inherited by any instance? users wouldn't need to use them
    # necessarily, but would be there to be called on all the same. some of the definitions below
    # are more particular to my semantics, so perhaps it makes sense to include those here instead.
    # Yes, that is a very good point and I agree—I wasn't exactly sure what definitions should be
    # more general so I just put everything in here, but whatever you think should be more general
    # should be able to be moved into the Frame class with no effects

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

    # B: this is particular to my semantics so perhaps belongs here
    # M: so all of above can be moved into the generic Frame class?
    # B: yes I think so, and I think 'Semantics' would be the best name for that class
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
            And(self.is_part_of(z, bit_u), self.max_compatible_part(z, bit_w, bit_y)),
        )

    # B: this looks good!
    def true_at(self, prefix_object, eval_world):
        if len(prefix_object) == 1:
            sent = prefix_object[0]
            if 'top' not in str(sent)[0]: # top const alr in model, see find_model_constraints
                # M: I'm not entirely sure where to deal with top, this is here only because it
                # was in the old code (hopefully it ends up working just as before too)
                # B: it might make sense to remove this and make top and bot operators but can leave it for now
                x = BitVec("t_atom_x", N)
                return Exists(x, And(self.is_part_of(x, eval_world), self.verify(x, sent)))
        operator = self.operator_dict[prefix_object[0]] # operator is a dict, the kw passed into add_operator
        args = prefix_object[1:]
        return operator['true_at'](*args, eval_world) # B: i assume this is what we want instead of the below

    def false_at(self, prefix_object, eval_world):
        if len(prefix_object) == 1:
            sent = prefix_object[0]
            if 'bot' not in str(sent)[0]: # B: i've added this to match true_at
                x = BitVec("f_atom_x", N)
                return Exists(x, And(self.is_part_of(x, eval_world), self.falsify(x, sent)))
        operator = self.operator_dict[prefix_object[0]] # operator is a dict, the kw passed into add_operator
        args = prefix_object[1:]
        return operator['false_at'](*args, eval_world) # B: i assume this is what we want instead of the below

    def frame_constraints(self):
        x = BitVec("frame_x", N)
        y = BitVec("frame_y", N)
        z = BitVec("frame_z", N)
        frame_constraints = [
            ForAll([x, y], Implies(And(self.possible(y), self.is_part_of(x, y)), self.possible(x))),
            ForAll([x, y], Exists(z, self.fusion(x, y) == z)),
            self.is_world(self.w),
        ]
        return frame_constraints

    # B: this seems like a good place to start!
    def proposition_definition(self, atom):
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

# B: modularity would be helped if operator classes could be defined independent of a frame

    # M: (writing this after writing below comment) if the operators are classes, then the true_at and similar
    # methods would need a frame as input to access the Z3 possible, verify, falsify functions for that
    # frame (or it would need whatever bigger object that houses those things). I think that's possible

# B: if need be, we might consider defining something general which both the frame and operators could reference

    # M: I think that would end up being necessary, because operators need to reference things like possible,
    # verify, falsify etc, which are currently housed in the frame (that is really the only reason
    # for the current organization

# B: the reason for wanting the operators to be independent of the constraints on a proposition etc., is so
# that one could potentially compare frames using the same operators in just the same way that one could compare
# operators over the same frame in order to facilitate systematic comparisons between systems

# M: You could add operators more modularly doing the following:
negation = {'name': '\\neg',
            'true_at': lambda arg, ref_frame, eval_world: ref_frame.false_at(arg, eval_world),
                   'false_at': lambda arg, ref_frame, eval_world: ref_frame.true_at(arg, eval_world),
                   'arity': 1}
# now say you have two frames, frame1 and frame2 (pretend one of them is not a BrastMcKieFrame)
frame1 = BrastMcKieFrame(3)
frame2 = BrastMcKieFrame(3)
# now you can do (using the current syntax, though it could be changed to be prettier as follows
frame1.add_operator(negation['name'], negation) # add_operator could be changed to make the function call
                                                # be frame1.add_operator(negation)
frame2.add_operator(negation['name'], negation)

# M: Would need to change the def of true_at of the Frame class to include the frame being passed into
# the operator's true_at "method" (in quotations bc its a dict rn)

# M: I'm having trouble thinking of a way to turn this into a class because if you have an operator
# that needs methods additional to those of other operators, you'd need to define a new subclass (or
# change the definition of the Operator class). However if the methods operators need to have do not
# depend on the frame, then making the class would be easy since you'd never need to add any methods
# to the class.
# B: it would be great if we can define operators in a frame independent way

# see TODO at top of playground file


frame.add_operator('\\neg',
                   true_at = lambda arg, eval_world: frame.false_at(arg, eval_world),
                   false_at = lambda arg, eval_world: frame.true_at(arg, eval_world),
                   arity=1)

frame.add_operator('\\wedge',
                   true_at = lambda X, Y, eval_world: And(frame.true_at(X, eval_world), frame.true_at(Y, eval_world)),
                   false_at = lambda X, Y, eval_world: Or(frame.false_at(X, eval_world), frame.false_at(Y, eval_world)),
                   arity=2)

frame.add_operator('\\vee',
                   true_at = lambda X, Y, eval_world: Or(frame.true_at(X, eval_world), frame.true_at(Y, eval_world)),
                   false_at = lambda X, Y, eval_world: And(frame.false_at(X, eval_world), frame.false_at(Y, eval_world)),
                   arity=2)

# B: my linter thinks the lambdas may not be necessary. here is an alternative for neg:
# B: using functions as below might help readability for users
# M: Yeah, that's true—especially if we do operators as classes
def neg_true_at(arg, eval_world):
    return frame.false_at(arg, eval_world)

def neg_false_at(arg, eval_world):
    return frame.true_at(arg, eval_world)

frame.add_operator(
    '\\neg',
    true_at=neg_true_at,
    false_at=neg_false_at,
    arity=1
)

infix_premises = ['A vee B', 'neg A']
infix_conclusions = ['B']
model_setup = ModelSetup(frame, infix_premises, infix_conclusions)
# model_setup.solve() # ... and so on. The rest would ideally proceed as before.
