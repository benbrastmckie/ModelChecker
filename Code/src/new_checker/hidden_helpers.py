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
    BitVecSort,
    BitVecVal,
    BoolRef,
    EmptySet,
    IsMember,
    Or,
    SetAdd,
    simplify,
    substitute,
) 

### GENERAL HELPERS ###


# def remove_repeats(sentences):  # NOTE: sentences are unhashable so can't use set()
#     """Takes a list and removes the repeats in it.
#     Used in find_all_constraints."""
#     seen = []
#     for obj in sentences:
#         if obj not in seen:
#             seen.append(obj)
#     return seen


# def summation(n, func, start=0):
#     """summation of i ranging from start to n of func(i)
#     used in find_all_bits"""
#     if start == n:
#         return func(start)
#     return func(start) + summation(n, func, start + 1)

### SYNTACTIC HELPERS ###

def op_left_right(tokens):
    """Divides whatever is inside a pair of parentheses into the left argument,
    right argument, and the operator."""

    def balanced_parentheses(tokens):
        """Check if parentheses are balanced in the argument."""
        stack = []
        for token in tokens:
            if token == "(":
                stack.append(token)
            elif token == ")":
                if not stack:
                    return False
                stack.pop()
        return len(stack) == 0

    def check_right(tokens, operator):
        if not tokens:
            raise ValueError(f"Expected an argument after the operator {operator}")
        if not balanced_parentheses(tokens):
            raise ValueError("Unbalanced parentheses")
        return tokens  # Remaining tokens are the right argument

    def cut_parentheses(left, tokens):
        count = 1  # To track nested parentheses
        while tokens:
            token = tokens.pop(0)
            if token == "(":
                count += 1
                left.append(token)
            elif token == ")":
                count -= 1
                left.append(token)
            elif count > 0:
                left.append(token)
            elif not tokens:
                raise ValueError(f"Extra parentheses in {tokens}.")
            else:
                operator = token
                right = check_right(tokens, operator)
                return operator, left, right
        raise ValueError(f"The expression {tokens} is incomplete.")

    def process_operator(tokens):
        if tokens:
            return tokens.pop(0)
        raise ValueError("Operator missing after operand")

    def extract_arguments(tokens):
        """Extracts the left argument and right argument from tokens."""
        left = []
        while tokens:
            token = tokens.pop(0)
            if token == "(":
                left.append(token)
                return cut_parentheses(left, tokens)
            elif token.isalnum() or token in {"\\top", "\\bot"}:
                left.append(token)
                operator = process_operator(tokens)
                right = check_right(tokens, operator)
                return operator, left, right
            else:
                left.append(token)
        raise ValueError("Invalid expression or unmatched parentheses")

    result = extract_arguments(tokens)
    if result is None:
        raise ValueError("Failed to extract arguments")
    return result

def parse_expression(tokens):
    """Parses a list of tokens representing a propositional expression and returns
    the expression in prefix notation.
    At this point, prefix is with strings for everything, I think
    """
    if not tokens:  # Check if tokens are empty before processing
        raise ValueError("Empty token list")
    token = tokens.pop(0)  # Get the next token
    if token == "(":  # Handle binary operator case (indicated by parentheses)
        closing_parentheses = tokens.pop()  # Remove the closing parenthesis
        if closing_parentheses != ")":
            raise SyntaxError(
                f"The sentence {tokens} is missing a closing parenthesis."
            )
        operator, left, right = op_left_right(tokens)
        left_arg, left_comp = parse_expression(left)  # Parse the left argument
        right_arg, right_comp = parse_expression(right)  # Parse the right argument
        complexity = left_comp + right_comp + 1
        return [operator, left_arg, right_arg], complexity 
    if token.isalnum():  # Handle atomic sentences
        return [token], 0
    elif token in {"\\top", "\\bot"}:  # Handle extremal operators
        return [token], 0
    arg, comp = parse_expression(tokens)
    return [token, arg], comp + 1 



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

# def z3_set(python_set, N):
#     z3_set = z3.EmptySet(z3.BitVecSort(N))
#     for elem in python_set:
#         z3_set = z3.SetAdd(z3_set, elem)
#     return z3_set
#
# def z3_set_to_python_set(z3_set, domain):
#     python_set = set()
#     for elem in domain:
#         if z3.simplify(z3.IsMember(elem, z3_set)):
#             python_set.add(elem)
#     return python_set

def z3_set(python_set, N):
    """Convert a Python set to a Z3 set of bit-width N."""
    z3_set = EmptySet(BitVecSort(N))
    for elem in python_set:
        z3_set = SetAdd(z3_set, elem)
    return z3_set

def z3_set_to_python_set(z3_set, domain):
    """Convert a Z3 set to a Python set using domain for membership checks."""
    python_set = set()
    for elem in domain:
        if bool(simplify(IsMember(elem, z3_set))):
            python_set.add(elem)
    return python_set


# M: this is not used right now but may be later
def z3_simplify(z3_expr):
    """
    This will get rid of need for all the bit_ functions.
    However, it does not get rid of e.g. find_compatible_parts.
    """
    if isinstance(z3_expr, BoolRef):
        return bool(simplify(z3_expr))
    return simplify(z3_expr)

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
    sample_bv = bvs[0]
    N = sample_bv.size()
    num_bvs = 2 ** N
    if len(bvs) == 1:
        bv = bvs[0]
        for i in range(num_bvs):
            substituted_formula = substitute(formula, (bv, BitVecVal(i, N)))
            constraints.append(substituted_formula)
    else:
        bv = bvs[0]
        remaining_bvs = bvs[1:]
        reduced_formula = Exists(remaining_bvs, formula) # Exists or ForAll?
        for i in range(num_bvs):
            substituted_reduced_formula = substitute(reduced_formula, (bv, BitVecVal(i, N)))
            constraints.append(substituted_reduced_formula)
    return Or(constraints)

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


### ERROR REPORTING ###


def not_implemented_string(cl_name):
    """Return a message for NotImplemented Errors on Operator and Proposition classes.
    The error is raised when a user creates an Operator object or a Proposition object,
    and directs them to implement a subclass and create instances of the subclass."""
    if cl_name == "PropositionDefaults":
        return (f"User should implement subclass(es) of {cl_name} for propositions. The "
            f"{cl_name} class should never be instantiated.")
    return (f"User should implement subclass(es) of {cl_name} for {cl_name.lower()}s. The "
            f"{cl_name} class should never be instantiated.")

def flatten(L_of_Ls):
    """
    helper for making sure that derived operators are not defined in terms of each other.
    takes in a list of lists; returns that list of lists flattened. 
    can in principle flatten a list with any amount of embedding. 
    """
    flattened = []
    for elem in L_of_Ls:
        if not isinstance(elem, list):
            flattened.append(elem)
        if isinstance(elem, list):
            flattened.extend(flatten(elem))
    return flattened
