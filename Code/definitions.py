### IMPORTS ###

from z3 import (
    # simplify,
    # Not,
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
    # Var,
    # Const,
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

# X = AtomSort("X", AtomSort)

# PropSort = DeclareSort("PropSort")
# X, Y = Consts("X Y", PropSort)

# A = Const("A", AtomSort)
# B = Const("B", AtomSort)
# B: Seems like the following could be useful to quantify over propositions
# B: Couldn't get this to work
# X = Var("X", AtomSort)
# Y = Var("Y", AtomSort)

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
verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())


### DEFINITIONS ###


def is_atomic(bit_vector):
    return And(bit_vector != 0, 0 == (bit_vector & (bit_vector - 1)))


def fusion(bit_s, bit_t):
    return bit_s | bit_t


def is_part_of(bit_s, bit_t):
    return fusion(bit_s, bit_t) == bit_t


def compatible(bit_x, bit_y):
    return possible(fusion(bit_x, bit_y))
    # TODO: compatible def


def maximal(bit_w):
    return ForAll(
        x,
        Implies(
            And(possible(x), possible(fusion(x, bit_w))),
            is_part_of(x, bit_w),
        ),
    )


def is_world(bit_w):
    return And(
        possible(bit_w),
        maximal(bit_w),
    )


def compatible_part(bit_x, bit_w, bit_y):
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
    return And(
        is_world(bit_u),
        is_part_of(bit_y, bit_u),
        Exists(z, And(is_part_of(z, bit_u), compatible_part(z, bit_w, bit_y))),
    )

    # TODO: proposition (see Strategies)

    # TODO: extended_verify and extended_falsify functions (see Strategies)

    # TODO: true def (see Strategies)


def total_fusion(list_of_states):
    """returns the fusion of a list of states"""
    fusion_of_first_two = fusion(list_of_states[0], list_of_states[1])
    if len(list_of_states) == 2:  # base case: fuse 2
        return fusion_of_first_two
    # recursive step: fuse first two and run the func on the next
    return total_fusion(
        [fusion_of_first_two] + list_of_states[2:]
    )  # + is list concatenation
