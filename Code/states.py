from z3 import *

N=7

#this file will have all functions related to states
def is_atomic(bit_vector):
    return simplify(
        And(bit_vector != 0, 0 == (bit_vector & (bit_vector - 1)))
    )  # this is taken from a Z3 documentation place thing

def fusion(bit_s, bit_t):
    fused = bit_s | bit_t  # | is the or operator
    return simplify(
        fused
    )  # this turns it from bvor to #b. The or operator | seems to return an "or" object of sorts, so simplify turns it into a bitvector object.

def is_part_of(bit_s, bit_t):
    return (
        fusion(bit_s, bit_t).sexpr() == bit_t.sexpr()
    )  # testing if fusion equals bit_t, as definition does
    # adding the sexpr()s above seemed to do the trick, not sure why.

def total_fusion(list_of_states):
    '''returns the fusion of a list of states'''
    fusion_of_first_two = fusion(list_of_states[0], list_of_states[1])
    if len(list_of_states) == 2: # base case: fuse 2
        return fusion_of_first_two
    # recursive step: fuse first two and run the func on the next
    new_list_of_states = [fusion_of_first_two]
    new_list_of_states.extend(list_of_states[2:])
    return total_fusion(new_list_of_states)

possible = Function("possible", BitVecSort(N), BoolSort())
is_world = Function("is_world", BitVecSort(N), BoolSort())
# def is_world(state):
#     '''func that defines if smth is a world'''
#     pass