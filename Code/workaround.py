from z3 import (Function, BitVecSort, BoolSort, BitVec)
from model_structure import ModelStructure
from syntax import AtomSort

def make_model_for(N):
    def make_relations_and_solve(premises, conclusions):
        possible = Function("possible", BitVecSort(N), BoolSort())
        verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
        falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())
        w = BitVec("w", N)
        mod = ModelStructure(premises, conclusions, verify, falsify, possible, N, w)
        mod.solve() # make these optional? technically, if they're saved within the model, they're not
                        # needed. And, actually anything else would make this go wrong. 
        return mod
    return make_relations_and_solve