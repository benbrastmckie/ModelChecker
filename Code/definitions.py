'''
file contains all definitions needed for finding Z3 models.
'''
from z3 import (
    Not,
    Exists,
    ForAll,
    Implies,
    BoolSort,
    BitVecSort,
    DeclareSort,
    BitVec,
    Consts,
    Function,
    And,
    # BitVecVal,
    # Var,
    # Const,
    # simplify,
)


### INFO ###

# this file will have all declarations and definitions needed to build models


### DECLARATIONS ###

# number of atomic states
N = 3

# sentence letters: sort definition, constants, and variables
# B: do we need a constant for each sentence letter in sentence_letters?
AtomSort = DeclareSort("AtomSort")
A, B, X = Consts("A B X", AtomSort)

# declare bitvector variables used for states
a = BitVec("a", N)
b = BitVec("b", N)
c = BitVec("c", N)

r = BitVec("r", N)
s = BitVec("s", N)
t = BitVec("t", N)

x = BitVec("x", N)
y = BitVec("y", N)
z = BitVec("z", N)

# declare bitvector variables used for world states
u = BitVec("u", N)
v = BitVec("v", N)
w = BitVec("w", N)

# primitive properties and relations
possible = Function("possible", BitVecSort(N), BoolSort())
world = Function("world", BitVecSort(N), BoolSort())
verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())


### DEFINITIONS ###


def is_atomic(bit_s):
    '''bit_s has exactly one index with value 1'''
    return And(bit_s != 0, 0 == (bit_s & (bit_s - 1)))


def fusion(bit_s, bit_t):
    '''the result of taking the maximum for each index in bit_s and bit_t'''
    return bit_s | bit_t


def is_part_of(bit_s, bit_t):
    '''the fusion of bit_s and bit_t is identical to bit_t'''
    return fusion(bit_s, bit_t) == bit_t


def compatible(bit_x, bit_y):
    '''the fusion of bit_x and bit_y is possible'''
    return possible(fusion(bit_x, bit_y))


def maximal(bit_w):
    '''bit_w includes all compatible states as parts.'''
    return ForAll(
        x,
        Implies(
            And(possible(x), possible(fusion(x, bit_w))),
            is_part_of(x, bit_w),
        ),
    )


def is_world(bit_w):
    '''bit_w is both possible and maximal.'''
    return And(
        possible(bit_w),
        maximal(bit_w),
    )


def compatible_part(bit_x, bit_w, bit_y):
    '''bit_x is the biggest part of bit_w that is compatible with bit_y.'''
    return And(
        is_part_of(bit_x, bit_w),
        compatible(bit_x, bit_y),
        ForAll(
            z,
            Implies(
                And(is_part_of(z, bit_w), compatible(z, bit_y), is_part_of(bit_x, z)),
                x == z,
            ),
        ),
    )


def alternative(bit_u, bit_y, bit_w):
    """
    bit_u is a world that is the alternative that results from imposing state bit_y on world bit_w.
    """
    return And(
        is_world(bit_u),
        is_part_of(bit_y, bit_u),
        Exists(z, And(is_part_of(z, bit_u), compatible_part(z, bit_w, bit_y))),
    )


def proposition(atom):
    """
    atom is a proposition since its verifiers and falsifiers are closed under
    fusion respectively, and the verifiers and falsifiers for atom are
    incompatible (exhaustivity). NOTE: exclusivity crashes Z3 so left off.
    """
    return And(
        ForAll(
            [x, y],
            Implies(And(verify(x, atom), verify(y, atom)), verify(fusion(x, y), atom)),
        ),
        ForAll(
            [x, y],
            Implies(And(falsify(x, atom), falsify(y, atom)), falsify(fusion(x, y), atom)),
        ),
        ForAll(
            [x, y],
            Implies(And(verify(x, atom), falsify(y, atom)), Not(possible(fusion(x, y)))),
        ),
        # ForAll(
        #     x,
        #     Implies(
        #         possible(x),
        #         Exists(y, And(compatible(x, y), Or(verify(y, atom), falsify(y, atom)))),
        #     ),
        # ),
        # NOTE: adding the constraint above makes Z3 crash
        # without this constraint the logic is not classical (there could be truth-value gaps)
    )

    # TODO: extended_verify and extended_falsify functions (see Strategies)

    # TODO: true def (see Strategies)


def total_fusion(list_of_states):
    """returns the fusion of a list of states."""
    fusion_of_first_two = fusion(list_of_states[0], list_of_states[1])
    if len(list_of_states) == 2:  # base case: fuse 2
        return fusion_of_first_two
    # recursive step: fuse first two and run the func on the next
    return total_fusion(
        [fusion_of_first_two] + list_of_states[2:]
    )  # + is list concatenation


def bitvec_to_substates(bit_vec):
    '''converts bitvectors to fusions of atomic states.'''
    bit_vec_as_string = bit_vec.sexpr()
    # print(type(bit_vec_as_string))
    bit_vec_backwards = bit_vec_as_string[::-1]
    # print(bit_vec_backwards)
    state_repr = ""
    alphabet = "abcdefghijklmnopqrstuvwxyz"
    # NOTE: this will only work for 26 states
    # could make a general function with a list, taking the quotient and remainder
    # then make the number of letters depends on how many sets of 26 you are in deep
    # TODO: this is ok for now, but we will want to be able to handle more than 26
    for i, char in enumerate(bit_vec_backwards):
        if char == "b":
            if not state_repr:
                return "□"  #  null state
            return state_repr[0 : len(state_repr) - 1]
        if char == "1":
            state_repr += alphabet[i]
            state_repr += "."

