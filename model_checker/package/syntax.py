'''
file contains all syntactic definitions

NOTES:
All sentence letters are capital letters.
All commands must be strictly in lowercase; they can have double backslash, a forward slash, or nothing (nothing so long as the first letter is lowercase).
The unary operators are defined in a separate set for clarity in the code.
'''
import doctest
from z3 import (
    Const, DeclareSort
)


AtomSort = DeclareSort("AtomSort")
# sentence_stuff = {'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','Z','W','Y','Z'}
# operator_stuff = {'\\','/','a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z'}
unary_operators = {'\\neg', '/neg', 'neg'}
def tokenize(str_exp):
    """
    >>> tokenize("(A /wedge (B /vee C))")
    ['(', 'A', '/wedge', '(', 'B', '/vee', 'C', ')', ')']

    >>> tokenize("(/neg A /wedge (B /vee C))")
    ['(', '/neg', 'A', '/wedge', '(', 'B', '/vee', 'C', ')', ')']

    >>> tokenize('((A /operator ((C /operator D) /operator F)) /operator E)')
    ['(', '(', 'A', '/operator', '(', '(', 'C', '/operator', 'D', ')', '/operator', 'F', ')', ')', '/operator', 'E', ')']

    >>> tokenize('/neg A')
    ['/neg', 'A']
    """
    split_str = str_exp.split()  # small issue here with doctest cases and backslashes

    def tokenize_improved_input(split_str):
        if len(split_str) == 1:
            # split_str is a list with one elem (has been called recursively or is last elem)
            base_string = split_str[0]  # base_string is a string
            if "(" in base_string:  # left parentheses in base_string
                tokenized_l = ["("]
                tokenized_l.extend(tokenize_improved_input([base_string[1:]]))
                return tokenized_l
            if ")" in base_string:  # right parentheses in base_string
                tokenized_l = tokenize_improved_input([base_string[:-1]])
                tokenized_l.append(")")
                return tokenized_l
            return split_str # else case: covers sentence letter case and latex operator case
        tokenized_l = tokenize_improved_input([split_str[0]])
        tokenized_l.extend(tokenize_improved_input(split_str[1:]))
        return tokenized_l

    return tokenize_improved_input(split_str)


def binary_comp(tokenized_expression):
    """
    finds complexity, defined by number of operators, in a tokenized_expression.
    In reality, it counts left parentheses. But it can easily be shown by induction
    that this number and that of operators is equal.

    >>> binary_comp(tokenize('(A /wedge (B /vee C))'))
    2

    >>> binary_comp(tokenize('/neg (A /wedge (B /vee C))'))
    2
    """
    return len([char for char in tokenized_expression if char == "("])


# TODO: linter says all or none of the returns should be an expression
def main_op_index(tokenized_expression):
    """
    given an expression with complexity > 0, finds the index of the main operator.
    Starting after the expression's initial parenthesis, the point
    at which the number of left parentheses equals the number of right is the
    first expression (as it is closed there)
    ASSUMES FIRST CHAR IS LEFT PARENTH. IF NOT CASE, EQN PROLLY SHOULDN'T BE HERE
    >>> main_op_index(tokenize('(A /wedge (B /vee C))'))
    2

    >>> main_op_index(tokenize('((A /vee B) /wedge C)'))
    6

    >>> main_op_index(tokenize('((A /operator ((C /operator D) /operator F)) /operator E)'))
    14

    >>> main_op_index(tokenize('((/neg A /vee B) /wedge C)'))
    7

    >>> main_op_index(tokenize('((A \\op (B \\op C)) \\op (D \\op E))'))
    10
    """
    left_parentheses = 0
    right_parentheses = 0
    if tokenized_expression[0] != '(':
        raise ValueError(tokenized_expression, 'this case probably shouldnt be being raised by this function')
    for i, token in enumerate(tokenized_expression[1:]): # [1:] to exclude the left parenth (thus complexity) of the main operator
        if token == "(":
            left_parentheses += 1
        elif token == ")":
            right_parentheses += 1
        elif token in unary_operators: # ignore this case since we care about binary complexity
            continue
        if left_parentheses == right_parentheses:
            return i + 2 # +1 bc list is [1:] and we want original index, and +1 bc it's next elem where the main op is


def parse(tokens):
    """
    >>> parse(tokenize("(A /wedge (B /lor C))"))
    ['/wedge', ['A'], ['/lor', ['B'], ['C']]]

    >>> parse(tokenize("/neg A"))
    ['/neg', ['A']]
    
    >>> parse(tokenize("A")) # note: atomic sentence should return a single element list
    ['A']

    >>> parse(tokenize('((A /op (B /op C)) /op (D /op E))'))
    ['/op', ['/op', ['A'], ['/op', ['B'], ['C']]], ['/op', ['D'], ['E']]]
    """
    bin_comp_tokens = binary_comp(tokens)
    if tokens[0] in unary_operators:
        return [tokens[0], parse(tokens[1:])]
    if bin_comp_tokens == 0:
        token = tokens[0]
        return [Const(token, AtomSort)] # Const is a function to make a constant
    main_operator_index = main_op_index(tokens)
    op_str = tokens[main_operator_index]  # determines how far the operation is
    left_expression = tokens[1 : main_operator_index]  # start 1 (exclude first parenthesis), stop at same pos of above (exclusive)
    right_expression = tokens[main_operator_index + 1 : -1]  # from pos of op plus 1 to the penultimate, thus excluding the last parentheses, which belongs to the main expression
    return [op_str, parse(left_expression), parse(right_expression)]


def Prefix(A):
    """takes a sentence in Infix notation and translates it to Prefix notation"""
    return parse(tokenize(A))


def Infix(A):
    """takes a sentence in Prefix notation and translates it to infix notation"""
    if len(A) == 1:
        return str(A[0])
    if len(A) == 2:
        return f'\\neg {Infix(A[1])}'
    op = A[0]
    left_expr = A[1]
    right_expr = A[2]
    return f'({Infix(left_expr)} {op} {Infix(right_expr)})'

# doctest.testmod()
# print(tokenize("(A \\wedge (B \\vee C))")) # the doctests fail, but this works. Need to do double backslash for abfnrtv.
# print(Prefix("(A \\wedge (B \\vee \\neg C))")) # ['\\wedge', ['A'], ['\\vee', ['B'], ['\\neg', ['C']]]]
# print(Prefix("A")) 
# print(Prefix('((A \\op (B \\op C)) \\op (D \\op E))')) # ['\\op', ['\\op', ['A'], ['\\op', ['B'], ['C']]], ['\\op', ['D'], ['E']]]

# sentences = [Prefix("(A \\wedge (B \\vee \\neg C))"), Prefix("A"), Prefix('((A \\op (B \\op Z)) \\op (D \\op E))')]
# print(all_sentence_letters(sentences)) # correctly prints ['A', 'B', 'C', 'D', 'E', 'Z']
# print(Prefix("\\neg (A \\boxright B)"))
# print(all_sentence_letters([Prefix("\\neg (A \\boxright B)")]))

# moved unused prefix_combine to the boneyard