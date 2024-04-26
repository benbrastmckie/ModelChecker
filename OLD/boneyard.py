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

# would go to semantics
def is_bitvector(bit_s):
    '''bit_s is a bitvector'''
    if isinstance(bit_s, BitVecNumRef):
        return True
    return False

#would go to semantics
def is_atomic(bit_s):
    '''bit_s has exactly one index with value 1'''
    return And(bit_s != 0, 0 == (bit_s & (bit_s - 1)))



#would go to semantics
def is_proper_part_of(bit_s, bit_t):
    '''the fusion of bit_s and bit_t is identical to bit_t'''
    return And(is_part_of(bit_s, bit_t), Not(bit_t == bit_s))


# would go to sematnics, though I think prop_const supplants this
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


# would go to semantics
def total_fusion(list_of_states):
    """returns the fusion of a list of states."""
    fusion_of_first_two = fusion(list_of_states[0], list_of_states[1])
    if len(list_of_states) == 2:  # base case: fuse 2
        return fusion_of_first_two
    # recursive step: fuse first two and run the func on the next
    return total_fusion(
        [fusion_of_first_two] + list_of_states[2:]
    )  # + is list concatenation


# would go to semantics
def Equivalent(cond_a,cond_b):
    '''define the biconditional to make Z3 constraints intuitive to read'''
    return cond_a == cond_b

# came from syntax, would go to either syntax, semantics, or model_definitions
def prefix_combine(prem,con):
    '''combines the premises with the negation of the conclusion(s).
    premises are prefix sentences, and so are the conclusions'''
    # if prem is None:
    #     prem = []
    input_sent = prem
    neg_conclusion_sents = [['\\neg ', sent] for sent in con]
    input_sent.extend(neg_conclusion_sents)
    return input_sent