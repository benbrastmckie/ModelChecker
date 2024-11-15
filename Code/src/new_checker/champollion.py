import z3

from hidden_helpers import (
    ForAll,
    Exists,
    bitvec_to_substates,
    index_to_substate,
    pretty_set_print,
    z3_set,
    z3_set_to_python_set,
    # product, # B: this is another method of semantics that would be good
    # to include in the parent class; I might try to work on this tonight...
)

from model_builder import (
    PropositionDefaults,
    SemanticDefaults,
)

import syntactic


class ChampollionSemantics(SemanticDefaults):

    def __init__(self, N):

        # Initialize the superclass to set defaults
        super().__init__(N)

        self.verify = z3.Function(
            "verify", # name
            z3.BitVecSort(N), # first argument type: bitvector
            syntactic.AtomSort, # second argument type: sentence letter
            z3.BoolSort() # return type: boolean
        )
        self.excludes = z3.Function(
            "excludes", # name
            z3.BitVecSort(N), # first argument type: bitvector
            z3.BitVecSort(N), # second argument type: bitvector
            z3.BoolSort() # return type: boolean
        )
        self.main_world = z3.BitVec("w", N)

        # Define frame constraints
        x, y = z3.BitVecs("frame_x frame_y", self.N)
        actuality = self.is_world(self.main_world)
        exclusion_symmetry = ForAll(
            [x, y],
            z3.Implies(self.excludes(x, y), self.excludes(y, x))
        )
        cosmopolitanism = z3.ForAll(
            x,
            z3.Implies(
                self.possible(x),
                z3.Exists(
                    y,
                    z3.And(self.is_world(y), self.is_part_of(x,y))
                )
            )
        )
        harmony = z3.ForAll( # not biconditional form (just a note)
            [x,y],
            z3.Implies(
                z3.And(self.is_world(x), self.coheres(x,y)),
                self.possible(y)
            )
        )
        rashomon = z3.ForAll(
            [x,y],
            z3.Implies(
                z3.And(self.possible(x), self.possible(y), self.coheres(x,y)),
                self.possible(self.fusion(x,y))
            )
        )

        # Set frame constraints
        self.frame_constraints = [
            actuality,
            exclusion_symmetry,
            cosmopolitanism,
            harmony,
            rashomon, # guards against emergent impossibility (pg 538)
        ]

        # TODO: Define invalidity conditions
        # self.premise_behavior = self.true_at
        # self.conclusion_behavior = self.false_at

    # B: since definitions like this will almost always occur, can we pull them
    # from the API once that is set up? I'm getting it would be best to move all
    # such general methods from their classes into a helpers file. alternatively,
    # I was wondering if they could stay methods of their respective classes and
    # then be listed in __init__.py so that one can call them from the API. not
    # sure this makes much of a difference but could help keep things organized.
    # alternatively, we can divide the helpers into sections.
    # M: I think it may be most helpful to divide the helpers into sections. Maybe
    # we have multiple files so that all e.g. states-related functions could be
    # called as e.g. states.fusion. 
    # B: that sounds good. when it comes to setting up the API, will the modules
    # be preserved? I would have figured that it would go:
    # 'import X from model-checker' not 'import states.X from model-checker'
    # happy to cross this bridge when we come to it

    def conflicts(self, bit_e1, bit_e2):
        f1, f2 = z3.BitVecs("f1 f2", self.N)
        return Exists(
            [f1, f2],
            z3.And(
                self.is_part_of(f1, bit_e1),
                self.is_part_of(f2, bit_e2),
                self.excludes(f1, f2),
            ),
        )

    def coheres(self, bit_e1, bit_e2):
        return z3.Not(self.conflicts(bit_e1, bit_e2))

    def possible(self, bit_e):
        return self.coheres(bit_e, bit_e)

    def compossible(self, bit_e1, bit_e2):
        return self.possible(self.fusion(bit_e1, bit_e2))

    # M: TODO: missing necessary proposition def on 528. don't think it goes here
    def necessary(self, bit_e1):
        x = z3.BitVec("nec_x", self.N)
        return z3.ForAll(x, z3.Implies(self.possible(x), self.compossible(bit_e1, x)))

    def collectively_excludes(self, bit_s, set_P):
        return self.excludes(bit_s, self.total_fusion(set_P))
    
    def individually_excludes(self, bit_s, set_P):
        # M: I think this works. Had to come up with alt def for condition b
        # condition a
        sub_s, p = z3.BitVecs("sub_s p", self.N)
        P = z3_set(set_P, self.N)
        cond_a = Exists(
            [sub_s, p],
            z3.And(self.is_part_of(sub_s, bit_s), P[p], self.excludes(sub_s, p)),
        )
        # condition b
        # Sigma is upper bound on excluders of set P
        Sigma = z3.BitVec(
            str(set_P), self.N
        )  # M: I think needs a unique name, hence str(set_P). though this soln is very untenable for debugging
        x, y, z, p = z3.BitVecs("x y z p", self.N)
        Sigma_UB = z3.ForAll(
            x,
            z3.Implies(
                Exists(p, z3.And(P[p], self.excludes(x, p))),
                self.is_part_of(x, Sigma)
            ),
        )
        # Sigma is the least upper bound on excluders of set P
        Sigma_LUB = z3.Not(
            z3.Exists(
                z,
                z3.And(
                    z3.ForAll(
                        y,
                        z3.Implies(
                            Exists(p, z3.And(P[p], self.excludes(y, p))),
                            self.is_part_of(y, Sigma),
                        ),
                    ),
                    self.is_proper_part_of(z, Sigma),
                ),
            )
        )
        return z3.And(cond_a, Sigma_UB, Sigma_LUB, self.is_part_of(bit_s, Sigma))

    def emergently_excludes(self, bit_s, set_P):
        return z3.And(
            self.collectively_excludes(bit_s, set_P),
            z3.Not(self.individually_excludes(bit_s, set_P)),
        )

    def is_world(self, bit_s):
        m = z3.BitVec("m", self.N)
        return z3.And(
            self.possible(bit_s), 
            z3.Not(
                z3.Exists(
                    m,
                    z3.And(
                        self.is_proper_part_of(bit_s, m),
                        self.possible(m)
                    )
                )
            )
        )
    
    def occurs(self, bit_s):
        return self.is_part_of(bit_s, self.main_world)


# B: this seems close!
class NegationOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\neg"
    arity = 1

    def true_at(self, arg, eval_world):
        """doc string place holder"""
        # M: TODO I'm not sure this is right
        # B: I think this is it (see def 30 in his paper)
        return z3.Not(self.semantics.true_at(arg))

    # B: this is on the right track
    def extended_verify(self, state, arg, eval_world):
        pass # TODO: state precludes |arg|
        # return z3.Not(self.semantics.extended_verify(state, arg, eval_world))

    def find_verifiers(self, arg_sent_obj, eval_world):
        pass # TODO
        # Y_V, Y_F = arg_sent_obj.proposition.find_proposition()
        # return Y_F, Y_V

    def print_method(self, sentence_obj, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints the argument."""
        sentence_obj.proposition.print_proposition(eval_world, indent_num)
        model_structure = sentence_obj.proposition.model_structure
        argument = sentence_obj.arguments[0]
        indent_num += 1
        model_structure.recursive_print(argument, eval_world, indent_num)


# B: this looks great!
class AndOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder
        args are prefix_objects (ie things of the third kind) I think, def 2nd or 3rd kind
        """
        sem = self.semantics
        return z3.And(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def extended_verify(self, state, leftarg, rightarg, eval_world):
        x = z3.BitVec("ex_ver_x", self.semantics.N)
        y = z3.BitVec("ex_ver_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                self.semantics.fusion(x, y) == state,
                self.semantics.extended_verify(x, leftarg, eval_world),
                self.semantics.extended_verify(y, rightarg, eval_world),
            )
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_world):
        """Takes sentences objects as arguments, finds their verifiers and
        falsifiers, and returns the verifiers and falsifiers for the operator"""
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return self.semantics.product(Y_V, Z_V) 
        # M: moved copies of product and coproduct to hidden_helpers
        # (discussion above fusion (lines ~ 80-100) applies here too)
        # B: I moved these into the SemanticDefaults parent class
    
    def print_method(self, sentence_obj, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        sentence_obj.proposition.print_proposition(eval_world, indent_num)
        model_structure = sentence_obj.proposition.model_structure
        left_sent_obj, right_sent_obj = sentence_obj.arguments
        indent_num += 1
        model_structure.recursive_print(left_sent_obj, eval_world, indent_num)
        model_structure.recursive_print(right_sent_obj, eval_world, indent_num)


# B: this looks great!
class OrOperator(syntactic.Operator):
    """doc string place holder"""

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """doc string place holder"""
        sem = self.semantics
        return z3.Or(sem.true_at(leftarg, eval_world), sem.true_at(rightarg, eval_world))

    def extended_verify(self, state, leftarg, rightarg, eval_world):
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_world),
            self.semantics.extended_verify(state, rightarg, eval_world),
            # same as bilateral except no And in def
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_world):
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return Y_V.union(Z_V)
    
    def print_method(self, sentence_obj, eval_world, indent_num):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        sentence_obj.proposition.print_proposition(eval_world, indent_num)
        model_structure = sentence_obj.proposition.model_structure
        left_sent_obj, right_sent_obj = sentence_obj.arguments
        indent_num += 1
        model_structure.recursive_print(left_sent_obj, eval_world, indent_num)
        model_structure.recursive_print(right_sent_obj, eval_world, indent_num)
