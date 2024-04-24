from z3 import (Function, BitVecSort, BoolSort, BitVec)
from model_structure import ModelStructure
from definitions import AtomSort

def make_model_for(N):
    def make_relations_and_solve(premises, conclusions):
        possible = Function("possible", BitVecSort(N), BoolSort())
        verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
        falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())
        w = BitVec("w", N)
        mod = ModelStructure(premises, conclusions, possible, verify, falsify, N, w)
        mod.solve(N, w)
        return mod
    return make_relations_and_solve
