from z3 import (
    # Solver,
    # BitVec,
    # Not,
    # Exists,
    # sat,
    ForAll,
    Implies,
    BoolSort,
    BitVecSort,
    Function,
    simplify,
    And,
)
# this file will have all functions related to states

N = 7


def is_atomic(bit_vector):
    return And(bit_vector != 0, 0 == (bit_vector & (bit_vector - 1)))  
    # this is taken from section 3.4 of https://z3prover.github.io/papers/programmingz3.html#sec-sorts


def fusion(bit_s, bit_t):
    return bit_s | bit_t
    # fused = bit_s | bit_t  # | is the or operator
    # return simplify(fused)
    # this turns it from bvor to #b. The or operator | seems to return an "or" object of sorts, so simplify turns it into a bitvector object.


def is_part_of(bit_s, bit_t):
    return fusion(bit_s, bit_t) == bit_t
    # return fusion(bit_s, bit_t).sexpr() == bit_t.sexpr()
    # testing if fusion equals bit_t, as definition does
    # adding the sexpr()s above seemed to do the trick, not sure why.


    # compatible def

    # maximality def

def is_new_world(bit_x,bit_w): # B: needs to quantify over all bit_x
    return And(
        possible(bit_w),
        ForAll(
            bit_x,
            Implies(
                And(possible(bit_x), possible(fusion(bit_x, bit_w))),
                is_part_of(bit_x, bit_w),
            ),
        ),
    )
    # testing if fusion equals bit_t, as definition does
    # adding the sexpr()s above seemed to do the trick, not sure why.


def total_fusion(list_of_states):
    """returns the fusion of a list of states"""
    fusion_of_first_two = fusion(list_of_states[0], list_of_states[1])
    if len(list_of_states) == 2:  # base case: fuse 2
        return fusion_of_first_two
    # recursive step: fuse first two and run the func on the next
    return total_fusion([fusion_of_first_two] + list_of_states[2:]) # + is list concatenation


def is_part_of(bit_s, bit_t):
    return fusion(bit_s, bit_t) == bit_t


possible = Function("possible", BitVecSort(N), BoolSort())
is_world = Function("is_world", BitVecSort(N), BoolSort())
# def is_world(state):
#     '''func that defines if smth is a world'''
#     pass
