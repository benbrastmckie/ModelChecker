import z3

from hidden_helpers import (
    ForAll,
    Exists,
    bitvec_to_substates,
    index_to_substate,
    pretty_set_print,
    z3_simplify,

)

from model_builder import PropositionDefaults

import syntactic

class ChampollionSemantics:

    def __init__(self, N):
        self.N = N
        self.excludes = z3.Function("excludes", z3.BitVecSort(N), z3.BitVecSort(N), z3.BoolSort())
        # NOTE: anything else?
        self.main_world = z3.BitVec("w", N)

        # Define top and bottom states
        max_value = (1 << self.N) - 1 # NOTE: faster than 2**self.N - 1
        self.full_bit = z3.BitVecVal(max_value, self.N)
        self.null_bit = z3.BitVecVal(0, self.N)
        self.all_bits = [z3.BitVecVal(i, self.N) for i in range(1 << self.N)]

        # TODO: Define the frame constraints
        x, y, z = z3.BitVecs("frame_x frame_y frame_z", self.N)
        exclusion_symmetry = ForAll([x,y], z3.Implies(self.excludes(x,y), self.excludes(y,x)))
        possibility_downard_closure = ForAll(
                [x, y],
                z3.Implies(z3.And(self.possible(y), self.is_part_of(x, y)), self.possible(x)),
            )
        self.frame_constraints = [exclusion_symmetry,
                                  possibility_downard_closure,
                                  ]

        # TODO: Define invalidity conditions

    def fusion(self, bit_s, bit_t):
        """the result of taking the maximum for each index in bit_s and bit_t
        returns a Z3 constraint"""
        return bit_s | bit_t
    
    def total_fusion(self, set_P):
        set_P = list(set_P)
        if len(set_P) == 2:
            return self.fusion(set_P[0], set_P[1])
        return self.fusion(set_P[0], self.total_fusion(set_P[1:]))

    def is_part_of(self, bit_s, bit_t):
        """the fusion of bit_s and bit_t is identical to bit_t
        returns a Z3 constraint"""
        return self.fusion(bit_s, bit_t) == bit_t
    
    def conflicts(self, bit_e1, bit_e2):
        f1, f2 = z3.BitVecs("f1 f2", self.N)
        return Exists([f1, f2], z3.And(
            self.is_part_of(f1, bit_e1),
            self.is_part_of(f2, bit_e2),
            self.excludes(f1, f2)
        ))
    
    def coheres(self, bit_e1, bit_e2):
        return z3.Not(self.conflicts(bit_e1, bit_e2))
    
    def possible(self, bit_e):
        return self.coheres(bit_e, bit_e)
    
    def compossible(self, bit_e1, bit_e2): # TODO: unsure. is fusion = sum?
        # def on page 528 of Champollion
        return self.possible(self.fusion(bit_e1, bit_e2))
    
    def necessary(self, bit_e1): # M: TODO: missing necessary proposition def on 528. don't think it goes here
        x = z3.BitVec("nec_x", self.N)
        return z3.ForAll(x, z3.Implies(self.possible(x), self.compossible(bit_e1, x)))
    
    # def regular_closure(self, set_S):
    #     set_S = list(set_S)
    #     total_fusion_S = self.total_fusion(set_S)
    #     regular_closure_set = set()
    #     r = z3.BitVec("regular_closure_r", self.N)
    #     for bit in set_S:
    #         if z3_simplify(Exists(r, self.And(self.is_part_of(r, bit), self.is_part_of(bit, total_fusion_S)))):
    #             regular_closure_set.add(bit)
    #     return regular_closure_set

    def collectively_excludes(self, bit_s, set_P):
        return self.excludes(bit_s, self.total_fusion(set_P))
    
    # def individually_excludes(self, bit_s, set_P):
    #     # condition a
    #     cons_list = []
    #     for p in set_P:
    #         cons_list.append(self.excludes(bit_s, p))
    #     cons_list = z3.Or(cons_list)
    #     # condition b
    #     self.is_part_of(bit_s)

        
    #     return z3.And(
    #             Exists(x, self.is_part_of(x, bit_s))

    #     )
    
    def emergently_excludes(self, bit_s, set_P):
        return z3.And(self.collectively_excludes(bit_s, set_P),
                      self.individually_excludes(bit_s, set_P))
