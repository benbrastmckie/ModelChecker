'''
just a place to put helper fucntions that are in semantics.py that are not in the Semantics class
'''

# from z3 import ForAll as z3ForAll
from z3 import (
    sat,
    Lambda, # used in FiniteForAll and FiniteExists definitions
    Implies,
    Or,
    Not,
    Solver,
    And,
    BitVec,
    BitVecVal,
    substitute, # used in FiniteForAll definition
    simplify,
)
from z3 import Exists as Z3Exists
from z3 import ForAll as Z3ForAll

use_z3_quantifiers = False # currently Z3Exists is being used despite this setting

unid_set = set()
def find_unused_id():
    num = 0
    while num in unid_set:
        num += 1
    unid_set.add(num)
    return str(num)


def SubForAll(bvs, formula):
    """
    This is a modified version of the original which uses substitution
    This works, but gives bad results: false premise models for strengthening the antecedent
    """
    cons_list = []
    if not isinstance(bvs, list):
        bvs = [bvs]
    bv_test = bvs[0]
    temp_N = bv_test.size()
    num_bvs = 2 ** temp_N
    if len(bvs) == 1:
        for i in range(num_bvs):
            substituted_formula = substitute(formula, (bvs[0], BitVecVal(i, temp_N)))
            cons_list.append(substituted_formula)
    if len(bvs) == 2:
        for i in range(num_bvs):
            for j in range(num_bvs):
                substituted_formula = substitute(formula, (bvs[0], BitVecVal(i, temp_N)), (bvs[1], BitVecVal(j, temp_N)))
                cons_list.append(substituted_formula)
    if len(bvs) == 3:
        for i in range(num_bvs):
            for j in range(num_bvs):
                for k in range(num_bvs):
                    substituted_formula = substitute(formula, (bvs[0], BitVecVal(i, temp_N)), (bvs[1], BitVecVal(j, temp_N)), (bvs[2], BitVecVal(k, temp_N)))
                    cons_list.append(substituted_formula)
    return And(cons_list)


def FiniteForAll(bvs, formula):
    """
    This is a modified version of the original which uses Lambdas
    Couldn't get this to work
    """
    cons_list = []
    if not isinstance(bvs, list):
        bvs = [bvs]
    bv_test = bvs[0]
    temp_N = bv_test.size()
    num_bvs = 2 ** temp_N
    lambda_formula = Lambda(bvs, formula)
    if len(bvs) == 1:
        for i in range(num_bvs):
            cons_list.append(lambda_formula[BitVecVal(i,temp_N)])
    if len(bvs) == 2:
        for i in range(num_bvs):
            for j in range(num_bvs):
                saturated_formula = lambda_formula[BitVecVal(i,temp_N),BitVecVal(j,temp_N)]
                cons_list.append(saturated_formula)
    if len(bvs) == 3:
        for i in range(num_bvs):
            for j in range(num_bvs):
                for k in range(num_bvs):
                    cons_list.append(lambda_formula[BitVecVal(i,temp_N),BitVecVal(j,temp_N),BitVecVal(k,temp_N)])
    return And(cons_list)

def FiniteExists(bvs, formula):
    if isinstance(bvs, list):
        new_bvs = ()
        for bv in bvs:
            new_bv = BitVec(str(bv) + find_unused_id(), bv.size())
            new_bvs += (new_bv,)
    else:
        new_bvs = BitVec(str(bvs) + find_unused_id(), bvs.size())
    return Lambda(bvs, formula)[new_bvs]

# Exists = Z3Exists
# Exists = Z3Exists if use_z3_quantifiers else ExistsFinite
# Exists = Z3Exists if use_z3_quantifiers else FiniteExists

# ForAll = Z3ForAll
# ForAll = Z3ForAll if use_z3_quantifiers else ForAllFinite
# ForAll = Z3ForAll if use_z3_quantifiers else FiniteForAll

def sentence_letters_in_compound(prefix_input_sentence): # can go in model_definitions
    """finds all the sentence letters in ONE input sentence. returns a list. WILL HAVE REPEATS
    returns a list of AtomSorts. CRUCIAL: IN THAT SENSE DOES NOT FOLLOW SYNTAX OF PREFIX SENTS.
    But that's ok, just relevant to know
    used in all_sentence_letters
    """
    if len(prefix_input_sentence) == 1:  # base case: atomic sentence
        return [prefix_input_sentence[0]] # redundant but conceptually clear
    return_list = []
    for part in prefix_input_sentence[1:]:
        return_list.extend(sentence_letters_in_compound(part))
    return return_list

def all_sentence_letters(prefix_sentences): # can go in model_definitions
    """finds all the sentence letters in a list of input sentences, in prefix form.
    returns as a list with no repeats (sorted for consistency) of AtomSorts
    used in find_all_constraints (to feed into find_prop_constraints) and StateSpace __init__"""
    sentence_letters = set()
    for prefix_input in prefix_sentences:
        sentence_letters_in_input = sentence_letters_in_compound(prefix_input)
        for sentence_letter in sentence_letters_in_input:
            sentence_letters.add(sentence_letter)
    return list(sentence_letters)
    # sort just to make every output the same, given sets aren't hashable

def solve_constraints(all_constraints): # will go in ModelSetup
    """ all_constraints is a list of constraints
    find model for the input constraints if there is any
    returns a tuple with a boolean representing if the constraints were solved or not
    and, if True, the model, if False the unsatisfiable core of the constraints"""
    solver = Solver()
    solver.add(all_constraints)
    result = solver.check(*[all_constraints])
    if result == sat:
        return (True, solver.model())
    return (False, solver.unsat_core())

### originally model_definitions—this and find_all_bits
def summation(n, func, start = 0):
    '''summation of i ranging from start to n of func(i)
    used in find_all_bits'''
    if start == n:
        return func(start)
    return func(start) + summation(n,func,start+1)

# unused
# def find_null_bit(size):
#     '''finds the null bit'''
#     return [BitVecVal(0, size)]

def find_all_bits(size):
    '''extract all bitvectors from the input model
    imported by model_structure'''
    all_bits = []
    max_bit_number = summation(size + 1, lambda x: 2**x)
    for val in range(max_bit_number):
        test_bit = BitVecVal(val, size)
        if test_bit in all_bits:
            continue
        all_bits.append(test_bit)
    return all_bits

def index_to_substate(index):
    '''
    test cases should make evident what's going on
    >>> index_to_substate(0)
    'a'
    >>> index_to_substate(26)
    'aa'
    >>> index_to_substate(27)
    'bb'
    >>> index_to_substate(194)
    'mmmmmmmm'
    used in bitvec_to_substates
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
    when you google how to do this
    used in bitvec_to_substates'''
    rem = integer%2
    new_backwards_str = backwards_binary_str + str(rem)
    if integer//2 == 0: # base case: we've reached the end
        remaining_0s_to_tack_on = number - len(new_backwards_str) # to fill in the zeroes
        return '#b' + remaining_0s_to_tack_on * '0' + new_backwards_str[::-1]
    new_int = integer//2
    return int_to_binary(new_int, number, new_backwards_str)


# has to do with printing
def bitvec_to_substates(bit_vec, N):
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
    raise ValueError("should have run into 'b' at the end but didn't")

def int_to_binary(integer, number, backwards_binary_str = ''):
    '''converts a #x string to a #b string. follows the first algorithm that shows up on google
    when you google how to do this
    used in bitvec_to_substates'''
    rem = integer%2
    new_backwards_str = backwards_binary_str + str(rem)
    if integer//2 == 0: # base case: we've reached the end
        remaining_0s_to_tack_on = number - len(new_backwards_str) # to fill in the zeroes
        return '#b' + remaining_0s_to_tack_on * '0' + new_backwards_str[::-1]
    new_int = integer//2
    return int_to_binary(new_int, number, new_backwards_str)



#### were in exposed_things

def ForAllFinite(bvs, formula):
    """
    generates constraints by substituting all possible bitvectors for the variables in the formula
    before taking the conjunction of those constraints
    """
    constraints = []
    if not isinstance(bvs, list):
        bvs = [bvs]
    bv_test = bvs[0]
    temp_N = bv_test.size()
    num_bvs = 2 ** temp_N
    if len(bvs) == 1:
        bv = bvs[0]
        for i in range(num_bvs):
            substituted_formula = substitute(formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_formula)
    else:
        bv = bvs[0]
        remaining_bvs = bvs[1:]
        reduced_formula = ForAllFinite(remaining_bvs, formula)
        for i in range(num_bvs):
            substituted_reduced_formula = substitute(reduced_formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_reduced_formula)
    return And(constraints)

def ExistsFinite(bvs, formula):
    """
    generates constraints by substituting all possible bitvectors for the variables in the formula
    before taking the disjunction of those constraints
    """
    constraints = []
    if not isinstance(bvs, list):
        bvs = [bvs]
    bv_test = bvs[0]
    temp_N = bv_test.size()
    num_bvs = 2 ** temp_N
    if len(bvs) == 1:
        bv = bvs[0]
        for i in range(num_bvs):
            substituted_formula = substitute(formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_formula)
    else:
        bv = bvs[0]
        remaining_bvs = bvs[1:]
        reduced_formula = ForAllFinite(remaining_bvs, formula)
        for i in range(num_bvs):
            substituted_reduced_formula = substitute(reduced_formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_reduced_formula)
    return Or(constraints)

ForAll = ForAllFinite
Exists = ExistsFinite

def product(set_A, set_B):
    """set of pairwise fusions of elements in set_A and set_B"""
    product_set = set()
    for bit_a in set_A:
        for bit_b in set_B:
            bit_ab = simplify(bit_a | bit_b)
            product_set.add(bit_ab)
    return product_set

def coproduct(set_A, set_B):
    """union closed under pairwise fusion"""
    A_U_B = set_A.union(set_B)
    return A_U_B.union(product(set_A, set_B))
