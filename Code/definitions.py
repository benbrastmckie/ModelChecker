'''
file contains all basic definitions
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
    Function,
    And,
    BitVecNumRef,
    simplify,
)

# TODO: move to test_complete without causing circular import
N = 3

# from user_input import N
# from test_complete import N

# def bit_vec_length():
#     from test_complete import N
#     return N

# N = bit_vec_length()

################################
######## DECLARATIONS ##########
################################

# NOTE: tried moving N to test_complete but created circular import error
# from test_complete import N


# sentence letters sort definition
AtomSort = DeclareSort("AtomSort")

# primitive properties and relations
possible = Function("possible", BitVecSort(N), BoolSort())
verify = Function("verify", BitVecSort(N), AtomSort, BoolSort())
falsify = Function("falsify", BitVecSort(N), AtomSort, BoolSort())

# NOTE: I tried to include a more meaningful name for w but it didn't work
# w = BitVec("eval_world_w", N)
# TODO: make eval_world_w global variable
w = BitVec("w", N)




################################
######### DEFINITIONS ##########
################################


def is_bitvector(bit_s):
    '''bit_s is a bitvector'''
    if isinstance(bit_s, BitVecNumRef):
        return True
    return False


def non_null_verify(bit_s, atom):
    '''bit_s verifies atom and is not the null state'''
    return And(Not(bit_s == 0), verify(bit_s, atom))


def non_null_falsify(bit_s,atom):
    '''bit_s verifies atom and is not the null state'''
    return And(Not(bit_s == 0), falsify(bit_s,atom))


def is_atomic(bit_s):
    '''bit_s has exactly one index with value 1'''
    return And(bit_s != 0, 0 == (bit_s & (bit_s - 1)))


def fusion(bit_s, bit_t):
    '''the result of taking the maximum for each index in bit_s and bit_t'''
    return bit_s | bit_t


def bit_fusion(bit_s, bit_t):
    """the result of taking the maximum for each index in _s and _t"""
    return simplify(bit_s | bit_t)
    # NOTE: this does seem to make a difference, otherwise no comp_parts


def is_part_of(bit_s, bit_t):
    '''the fusion of bit_s and bit_t is identical to bit_t'''
    return fusion(bit_s, bit_t) == bit_t


def is_proper_part_of(bit_s, bit_t):
    '''the fusion of bit_s and bit_t is identical to bit_t'''
    return And(is_part_of(bit_s, bit_t), Not(bit_t == bit_s))


def bit_part(bit_s, bit_t):
    """the fusion of _s and _t is identical to bit_t"""
    return bool(simplify(bit_fusion(bit_s, bit_t) == bit_t))
    # NOTE: this does seem to make a difference, otherwise no comp_parts


def bit_proper_part(bit_s, bit_t):
    """bit_s is a part of bit_t and bit_t is not a part of bit_s"""
    return bool(bit_part(bit_s, bit_t)) and not bit_s == bit_t
    # NOTE: this does not seem to make a difference and so has been turned off
    # in the interest of discovering if it is required or not
    # return bool(bit_part(bit_s, bit_t)) and not bit_s == bit_t


def compatible(bit_x, bit_y):
    '''the fusion of bit_x and bit_y is possible'''
    return possible(fusion(bit_x, bit_y))


def maximal(bit_w):
    """bit_w includes all compatible states as parts."""
    x = BitVec('max_dummy', N)
    return ForAll(
        x,
        Implies(
            compatible(x, bit_w),
            is_part_of(x, bit_w),
        ),
    )


def is_world(bit_w):
    '''bit_w is both possible and maximal.'''
    return And(
        possible(bit_w),
        maximal(bit_w),
    )


def max_compatible_part(bit_x, bit_w, bit_y):
    '''bit_x is the biggest part of bit_w that is compatible with bit_y.'''
    z = BitVec('max_part_dummy', N)
    return And(
        is_part_of(bit_x, bit_w),
        compatible(bit_x, bit_y),
        ForAll(
            z,
            Implies(
                And(is_part_of(z, bit_w), compatible(z, bit_y), is_part_of(bit_x, z)),
                bit_x == z,
            ),
        ),
    )


def is_alternative(bit_u, bit_y, bit_w):
    """
    bit_u is a world that is the alternative that results from imposing state bit_y on world bit_w.
    """
    z = BitVec("alt_dummy", N)
    return And(
        is_world(bit_u),
        is_part_of(bit_y, bit_u),
        Exists(z, And(is_part_of(z, bit_u), max_compatible_part(z, bit_w, bit_y))),
    )


def proposition(atom):
    """
    atom is a proposition since its verifiers and falsifiers are closed under
    fusion respectively, and the verifiers and falsifiers for atom are
    incompatible (exhaustivity). NOTE: exclusivity crashes Z3 so left off.
    """
    x = BitVec("prop_dummy_x", N)
    y = BitVec("prop_dummy_y", N)
    return And(
        ForAll(
            [x, y],
            Implies(And(verify(x, atom), verify(y, atom)), verify(fusion(x, y), atom)),
        ), # verifiers for atom are closed under fusion
        ForAll(
            [x, y],
            Implies(And(falsify(x, atom), falsify(y, atom)), falsify(fusion(x, y), atom)),
        ), # falsifiers for atom are closed under fusion
        ForAll(
            [x, y],
            Implies(And(verify(x, atom), falsify(y, atom)), Not(compatible(x, y))),
        ), # verifiers and falsifiers for atom are incompatible
        # ForAll(
        #     x,
        #     Implies(
        #         possible(x),
        #         Exists(y, And(compatible(x, y), Or(verify(y, atom), falsify(y, atom)))),
        #     ),
        # ), # every possible state is compatible with either a verifier or falsifier for atom
        # NOTE: adding the constraint above makes Z3 crash
        # without this constraint the logic is not classical (there could be truth-value gaps)
    )


def total_fusion(list_of_states):
    """returns the fusion of a list of states."""
    fusion_of_first_two = fusion(list_of_states[0], list_of_states[1])
    if len(list_of_states) == 2:  # base case: fuse 2
        return fusion_of_first_two
    # recursive step: fuse first two and run the func on the next
    return total_fusion(
        [fusion_of_first_two] + list_of_states[2:]
    )  # + is list concatenation

def index_to_substate(index):
    '''
    >>> index_to_substate(0)
    'a'
    >>> index_to_substate(26)
    'aa'
    >>> index_to_substate(27)
    'bb'
    >>> index_to_substate(194)
    'mmmmmmmm'
    '''
    number = index + 1 # because python indices start at 0
    letter_dict = {1:'a', 2:'b', 3:'c', 4:'d', 5:'e', 6:'f', 7:'g', 8:'h', 9:'i', 10:'j',
                   11:'k', 12:'l', 13:'m', 14:'n', 15:'o', 16:'p', 17:'q', 18:'r', 19:'s', 20:'t',
                   21:'u', 22:'v', 23:'w', 24:'x', 25:'y', 26:'z'} # could be make less hard-code-y
                            # but this makes it clearer and more intuitive what we want to happen
    letter = letter_dict[number%26]
    return ((number//26) + 1) * letter

def int_to_binary(integer, number, backwards_binary_str = ''):
    '''converts a #x string to a #b string. follows the first algorithm that shows up on google
    when you google how to do this'''
    rem = integer%2
    new_backwards_str = backwards_binary_str + str(rem)
    if integer//2 == 0: # base case: we've reached the end
        remaining_0s_to_tack_on = number - len(new_backwards_str) # to fill in the zeroes
        return '#b' + remaining_0s_to_tack_on * '0' + new_backwards_str[::-1]
    new_int = integer//2
    return int_to_binary(new_int, number, new_backwards_str)


# TODO: linter says all or none of the returns should be an expression
def bitvec_to_substates(bit_vec):
    '''converts bitvectors to fusions of atomic states.'''
    bit_vec_as_string = bit_vec.sexpr()
    if 'x' in bit_vec_as_string: # if we have a hexadecimal, ie N=4m
        integer = int(bit_vec_as_string[2:],16)
        bit_vec_as_string = int_to_binary(integer, N)
    bit_vec_backwards = bit_vec_as_string[::-1]
    state_repr = ""
    for i, char in enumerate(bit_vec_backwards):
        if char == "b":
            if not state_repr:
                return "□"  #  null state
            return state_repr[0 : len(state_repr) - 1]
        if char == "1":
            state_repr += index_to_substate(i)
            state_repr += "."


def Equivalent(cond_a,cond_b):
    '''define the biconditional to make Z3 constraints intuitive to read'''
    return cond_a == cond_b


def summation(n, func, start = 0):
    '''used in print to find max bitvector'''
    if start == n:
        return func(start)
    return func(start) + summation(n,func,start+1)
