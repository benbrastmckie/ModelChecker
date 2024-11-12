import z3

from hidden_helpers import (
    ForAll,
    Exists,
    bitvec_to_substates,
    index_to_substate,
    pretty_set_print,
    z3_set,
)

from model_builder import PropositionDefaults

import syntactic


class ChampollionSemantics:
    def __init__(self, N):
        self.N = N
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

        # Define top and bottom states
        max_value = (1 << self.N) - 1  # NOTE: faster than 2**self.N - 1
        self.full_bit = z3.BitVecVal(max_value, self.N)
        self.null_bit = z3.BitVecVal(0, self.N)
        self.all_bits = [z3.BitVecVal(i, self.N) for i in range(1 << self.N)]

        # TODO: Define the frame constraints
        x, y = z3.BitVecs("frame_x frame_y", self.N)
        exclusion_symmetry = ForAll(
            [x, y], z3.Implies(self.excludes(x, y), self.excludes(y, x))
        )
        possibility_downard_closure = ForAll(
            [x, y],
            z3.Implies(
                z3.And(self.possible(y), self.is_part_of(x, y)), self.possible(x)
            ),
        )
        cosmopolitanism = z3.ForAll(x, z3.Implies(self.possible(x), z3.Exists(y, z3.And(self.is_world(y), self.is_part_of(x,y)))))
        # M: below is not biconditional. I think that's ok (see comment on pg 538), just thought I'd note
        harmony = z3.ForAll([x,y], z3.Implies(z3.And(self.is_world(x), self.coheres(x,y)), self.possible(y)))
        rashomon = z3.ForAll([x,y], z3.Implies(z3.And(self.possible(x), self.possible(y), self.coheres(x,y)), self.possible(self.fusion(x,y))))
        # B: this is really nice and readable
        self.frame_constraints = [
            exclusion_symmetry,
            possibility_downard_closure,
            cosmopolitanism,
            harmony,
            rashomon, # guards against emergent impossibility (pg 538)
            self.is_world(self.main_world) # actuality?


        ]

        # TODO: Define invalidity conditions

    # B: since definitions like this will almost always occur, can we pull them
    # from the API once that is set up? I'm getting it would be best to move all
    # such general methods from their classes into a helpers file. alternatively,
    # I was wondering if they could stay methods of their respective classes and
    # then be listed in __init__.py so that one can call them from the API. not
    # sure this makes much of a difference but could help keep things organized.
    # alternatively, we can divide the helpers into sections.
    def fusion(self, bit_s, bit_t):
        """the result of taking the maximum for each index in bit_s and bit_t
        returns a Z3 constraint"""
        return bit_s | bit_t

    # def total_fusion(self, set_P):
    #     if isinstance(set_P, z3.ArrayRef):
    #         set_P = z3_set_to_python_set(z3_set, self.all_bits)
    #     set_P = list(set_P)
    #     if len(set_P) == 2:
    #         return self.fusion(set_P[0], set_P[1])
    #     return self.fusion(set_P[0], self.total_fusion(set_P[1:]))

    def is_part_of(self, bit_s, bit_t):
        """the fusion of bit_s and bit_t is identical to bit_t
        returns a Z3 constraint"""
        return self.fusion(bit_s, bit_t) == bit_t

    def is_proper_part_of(self, bit_s, bit_t):
        """the fusion of bit_s and bit_t is identical to bit_t
        returns a Z3 constraint"""
        return z3.And(self.fusion(bit_s, bit_t) == bit_t, bit_s != bit_t)

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

    def compossible(self, bit_e1, bit_e2):  # TODO: unsure. is fusion = sum?
        # def on page 528 of Champollion
        return self.possible(self.fusion(bit_e1, bit_e2))

    # M: TODO: missing necessary proposition def on 528. don't think it goes here
    def necessary(self, bit_e1):
        x = z3.BitVec("nec_x", self.N)
        return z3.ForAll(x, z3.Implies(self.possible(x), self.compossible(bit_e1, x)))

    def collectively_excludes(self, bit_s, set_P):
        return self.excludes(bit_s, self.total_fusion(set_P))
    
    def individually_excludes(self, bit_s, set_P):
        # M: I think this works. Had to come up with alt def for condition b
        # I have a proof, not completely confident on it though
        # condition a
        sub_s, p = z3.BitVecs("sub_s p", self.N)
        P = z3_set(set_P)
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
            self.individually_excludes(bit_s, set_P),
        )

    def is_world(self, bit_s):
        m = z3.BitVec("m", self.N)
        return z3.And(self.possible(bit_s), 
                      z3.Not(z3.Exists(m, z3.And(self.is_proper_part_of(bit_s, m),
                                                 self.possible(m)))))
    
    def occurs(self, bit_s):
        return self.is_part_of(bit_s, self.main_world)
    

