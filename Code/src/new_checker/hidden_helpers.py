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
    Const,
    DeclareSort,
    BoolRef,
    Or,
    simplify,
    substitute,
) 

AtomSort = DeclareSort("AtomSort")


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

# B: I replaced the below with above
# def int_to_binary(integer, number, backwards_binary_str = ''):
#     '''converts a #x string to a #b string. follows the first algorithm that shows up on google
#     when you google how to do this
#     used in bitvec_to_substates'''
#     rem = integer%2
#     new_backwards_str = backwards_binary_str + str(rem)
#     if integer//2 == 0: # base case: we've reached the end
#         remaining_0s_to_tack_on = number - len(new_backwards_str) # to fill in the zeroes
#         return '#b' + remaining_0s_to_tack_on * '0' + new_backwards_str[::-1]
#     new_int = integer//2
#     return int_to_binary(new_int, number, new_backwards_str)


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
    # letter_dict = {1:'a', 2:'b', 3:'c', 4:'d', 5:'e', 6:'f', 7:'g', 8:'h',
    #                9:'i', 10:'j', 11:'k', 12:'l', 13:'m', 14:'n', 15:'o',
    #                16:'p', 17:'q', 18:'r', 19:'s', 20:'t', 21:'u', 22:'v',
    #                23:'w', 24:'x', 25:'y', 26:'z'}
    # letter = letter_dict[number%26]
    # could be make less hard-code-y
    # but this makes it clearer and more intuitive what we want to happen
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


### SENTENCE HELPERS ###


def sentence_letters_in_compound(prefix_sentence):
    """Returns a list of AtomSorts for all sentence letters in prefix_sentence.
    May have repeats and does not follow the syntax of prefix sentences.
    Used in find_sentence_letters.
    """
    if len(prefix_sentence) == 1:  # base case: atomic sentence
        return [prefix_sentence[0]]  # redundant but conceptually clear
    return_list = []
    for part in prefix_sentence[1:]:
        return_list.extend(sentence_letters_in_compound(part))
    return return_list


def all_sentence_letters(prefix_sentences):
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


def repeats_removed(sentences):  # NOTE: sentences are unhashable so can't use set()
    """Takes a list and removes the repeats in it.
    Used in find_all_constraints."""
    seen = []
    for obj in sentences:
        if obj not in seen:
            seen.append(obj)
    return seen


def subsentences_of(prefix_sentence):
    """Returns all prefix subsentence of a prefix sentence
    Used in find_extensional_subsentences."""
    progress = []
    progress.append(prefix_sentence)
    if len(prefix_sentence) == 2:
        sub_sentsentences = subsentences_of(prefix_sentence[1])
        return progress + sub_sentsentences
    if len(prefix_sentence) == 3:
        left_subsentences = subsentences_of(prefix_sentence[1])
        right_subsentences = subsentences_of(prefix_sentence[2])
        all_subsentences = left_subsentences + right_subsentences + progress
        return repeats_removed(all_subsentences)
    return progress


### PREFIX HELPERS ###


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
            else:
                operator = token
                right = check_right(tokens, operator)
                return operator, left, right

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
    
    return extract_arguments(tokens)


def parse_expression(tokens, model_setup):
    """Parses a list of tokens representing a propositional expression and returns
    the expression in prefix notation."""
    if not tokens:  # Check if tokens are empty before processing
        raise ValueError("Empty token list")
    token = tokens.pop(0)  # Get the next token
    if token == "(":  # Handle binary operator case (indicated by parentheses)
        closing_parentheses = tokens.pop()  # Remove the closing parenthesis
        if closing_parentheses != ")":
            raise SyntaxError(
                f"The sentence {tokens} is missing a closing parenthesis."
            )
        operator, left, right = op_left_right(tokens)  # LINTER: "None" is not iterable
        left_arg = parse_expression(left, model_setup)  # Parse the left argument
        right_arg = parse_expression(right, model_setup)  # Parse the right argument
        return [model_setup.operators[operator], left_arg, right_arg]
    if token.isalnum():  # Handle atomic sentences
        return [Const(token, AtomSort)]
    elif token in {"\\top", "\\bot"}:  # Handle extremal operators
        return [model_setup.operators[token]]
    return [  # Unary operators
        model_setup.operators[token],
        parse_expression(tokens, model_setup),
    ]


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
