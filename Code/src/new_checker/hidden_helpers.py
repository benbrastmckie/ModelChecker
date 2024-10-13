"""
This file contains all helper functions used in `hidden_things.py`

NOTES:
Any latex commands must have double backslash.
Operators include `\\` and sentence letters do not.
The operators `\\top` and `\\bot` are reserved.
"""

### IMPORTS AND DEFINITIONS ###

import string
from z3 import(
    And,
    BitVecVal,
    Or,
    substitute,
) 

### GENERAL HELPERS ###


def remove_repeats(sentences):  # NOTE: sentences are unhashable so can't use set()
    """Takes a list and removes the repeats in it.
    Used in find_all_constraints."""
    seen = []
    for obj in sentences:
        if obj not in seen:
            seen.append(obj)
    return seen


### PRINT HELPERS ###


def pretty_set_print(set_with_strings):
    """input a set with strings print that same set but with no quotation marks around each
    individual string, and also with the set in order returns the set as a string
    Used in print_vers_and_fals() and print_alt_worlds()"""
    sorted_set = sorted(list(set_with_strings))  # actually type list, not set
    print_str = "{"
    for i, elem in enumerate(sorted_set):
        print_str += elem
        if i != len(sorted_set) - 1:
            print_str += ", "
    print_str += "}"
    return print_str if print_str != "{}" else '∅'


def summation(n, func, start = 0):
    '''summation of i ranging from start to n of func(i)
    used in find_all_bits'''
    if start == n:
        return func(start)
    return func(start) + summation(n,func,start+1)


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


def int_to_binary(integer, number):
    '''Converts a hexadecimal string to a binary string.'''
    binary_str = bin(integer)[2:]  # Convert to binary string and remove '0b' prefix
    padding = number - len(binary_str)  # Calculate padding
    return '#b' + '0' * padding + binary_str


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
    alphabet = string.ascii_lowercase  # 'abcdefghijklmnopqrstuvwxyz'
    letter = alphabet[number % 26 - 1]  # Get corresponding letter
    return ((number//26) + 1) * letter


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


### Z3 HELPERS ###


# # M: this is not used right now but may be later
# def z3_simplify(z3_expr):
#     """
#     This will get rid of need for all the bit_ functions.
#     However, it does not get rid of e.g. find_compatible_parts.
#     """
#     if isinstance(z3_expr, BoolRef):
#         return bool(simplify(z3_expr))
#     return simplify(z3_expr)

def ForAll(bvs, formula):
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
        reduced_formula = ForAll(remaining_bvs, formula)
        for i in range(num_bvs):
            substituted_reduced_formula = substitute(reduced_formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_reduced_formula)
    return And(constraints)

def Exists(bvs, formula):
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
        reduced_formula = ForAll(remaining_bvs, formula)
        for i in range(num_bvs):
            substituted_reduced_formula = substitute(reduced_formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_reduced_formula)
    return Or(constraints)


### ERROR REPORTING ###


def not_implemented_string(cl_name):
    """Return a message for NotImplemented Errors on Operator and Proposition classes.
    The error is raised when a user creates an Operator object or a Proposition object,
    and directs them to implement a subclass and create instances of the subclass."""
    return (
        f"User should implement subclass(es) of {cl_name} "
        f"for {cl_name.lower()}s. The {cl_name} "
        "class should never be instantiated."
    )


def flatten(L_of_Ls):
    flattened = []
    for elem in L_of_Ls:
        if not isinstance(elem, list):
            flattened.append(elem)
        if isinstance(elem, list):
            flattened.extend(flatten(elem))
    return flattened
