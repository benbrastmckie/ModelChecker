### IMPORTS ###

from z3 import (
    # simplify,
    # Not,
    # Exists,
    ForAll,
    Implies,
    BoolSort,
    BitVecSort,
    DeclareSort,
    BitVec,
    Consts,
    Function,
    And,
    Var,
)

### INFO ###

# this file will have all declarations and definitions needed to build models

### DECLARATIONS ###

# number of atomic states
N = 7

# sentence letters: sort definition, constants, and variables
# B: do we need a constant for each sentence letter in sentence_letters?
AtomSort = DeclareSort("AtomSort")
A, B = Consts("A B", AtomSort)

# B: I'm not sure these will do what we want but included them to experiment
X = Var("X", AtomSort)
Y = Var("Y", AtomSort)

# declare bitvector variables used for states
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
    # this is taken from section 3.4 of https://z3prover.github.io/papers/programmingz3.html#sec-sorts
    # TODO: move relevant notes here to gossary


def fusion(bit_s, bit_t):
    return bit_s | bit_t
    # fused = bit_s | bit_t  # | is the or operator
    # return simplify(fused)
    # this turns it from bvor to #b. The or operator | seems to return an "or" object of sorts, so simplify turns it into a bitvector object.
    # TODO: move relevant notes here to gossary


def is_part_of(bit_s, bit_t):
    return fusion(bit_s, bit_t) == bit_t
    # return fusion(bit_s, bit_t).sexpr() == bit_t.sexpr()
    # testing if fusion equals bit_t, as definition does
    # adding the sexpr()s above seemed to do the trick, not sure why.
    # TODO: move relevant notes here to gossary

    # TODO: compatible def

    # TODO: maximality def
    # NOTE: it might be OK to define the sort for a variable x here
    # that variable could then be used in the def of maximal

    # TODO: world def in terms of compatible and maximal defs

    # TODO: compatible_part def

    # TODO: alternative def

    # TODO: extended_verify and extended_falsify functions

    # TODO: true def


# B: check that quantification over x is working as intended
# TODO: rewrite in terms of possible and maximal defs
def is_world(bit_w):
    return And(
        possible(bit_w),
        ForAll(
            x,
            Implies(
                And(possible(x), possible(fusion(x, bit_w))),
                is_part_of(x, bit_w),
            ),
        ),
    )


def total_fusion(list_of_states):
    """returns the fusion of a list of states"""
    fusion_of_first_two = fusion(list_of_states[0], list_of_states[1])
    if len(list_of_states) == 2:  # base case: fuse 2
        return fusion_of_first_two
    # recursive step: fuse first two and run the func on the next
    return total_fusion(
        [fusion_of_first_two] + list_of_states[2:]
    )  # + is list concatenation
