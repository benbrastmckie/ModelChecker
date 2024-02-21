import doctest
from z3 import *

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
    split_str = str_exp.split() # small issue here with doctest cases and backslashes

    def tokenize_improved_input(split_str):
        sentence_stuff = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        if len(split_str) == 1:
            # split_str is a list with one elem (has been called recursively or is last elem)
            base_string = split_str[0]  # base_string is a string
            if "(" in base_string:  # left parentheses in base_string
                tokenized_l = ["("]
                tokenized_l.extend(tokenize_improved_input([base_string[1:]]))
                return tokenized_l
            elif ")" in base_string:  # right parentheses in base_string
                tokenized_l = tokenize_improved_input([base_string[:-1]])
                tokenized_l.append(")")
                return tokenized_l
            elif "\\" or '/' in base_string: # latex operator case
                return split_str
            elif base_string in sentence_stuff: # sentence letter case
                return split_str
            raise ValueError(base_string) # these cases should be exhaustive
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
    return len([char for char in tokenized_expression if char == '('])


def main_op_index(tokenized_expression):
    """
    given an expression with complexity > 0, finds the index of the main operator.
    Starting after the expression's initial parenthesis, the point
    at which the number of left parentheses equals the number of right is the
    first expression (as it is closed there)
    # NOTE: what is the first expression?
    # consider: ((A \\op (B \\op C)) \\op (D \\op E))
    ASSUMES FIRST CHAR IS LEFT PARENTH. IF NOT CASE, EQN PROLLY SHOULDN'T BE HERE
    >>> main_op_index(tokenize('(A /wedge (B /vee C))'))
    2

    >>> main_op_index(tokenize('((A /vee B) /wedge C)'))
    6

    >>> main_op_index(tokenize('((A /operator ((C /operator D) /operator F)) /operator E)'))
    14

    >>> main_op_index(tokenize('((/neg A /vee B) /wedge C)'))
    7
    """
    left_parentheses = 0
    right_parentheses = 0
    if tokenized_expression[0] != '(':
        raise ValueError(tokenized_expression, 'this case probably shouldnt be being raised by this function')
    for i, token in enumerate(tokenized_expression[1:]): # [1:] to exclude the complexity of the matrix operator
        if token == "(":
            left_parentheses += 1
        # elif '\\' in seq and not left_parentheses:
        #     return left_parentheses
        elif token == ")":
            right_parentheses += 1
        elif 'neg' in token:
            continue
        if left_parentheses == right_parentheses:
            return i + 2 # +1 bc list is [1:], and +1 bc it's next elem where the matrix op is


def parse(tokens):
    """
    >>> parse(tokenize("(A /wedge (B /lor C))"))
    ['/wedge', 'A', ['/lor', 'B', 'C']]

    >>> parse(tokenize("/neg A"))
    ['/neg', 'A']
    
    >>> parse(tokenize("A")) # note: atomic sentence should return a string
    'A'
    """
    comp_tokens = binary_comp(tokens)
    if 'neg' in tokens[0]:
        return [tokens[0], parse(tokens[1:])]
    if comp_tokens == 0:
        token = tokens[0]
        return token
    matrix_index = main_op_index(tokens)
    op_str = tokens[matrix_index]  # determines how far the operation is
    left_expression = tokens[1 : matrix_index]  # from 1 (exclude first parenthesis) to the same
    # pos of above, bc its exclusive
    right_expression = tokens[matrix_index + 1 : -1]  # from pos of op plus 1 to the penultimate,
    # thus excluding the last parentheses, which belongs to the matrix expression
    return [op_str, parse(left_expression), parse(right_expression)]


def Prefix(A):
    """takes a sentence in Infix notation and translates it to prefix notation"""
    return parse(tokenize(A))


def Infix(A):
    """takes a sentence in Prefix notation and translates it to infix notation"""
    pass


doctest.testmod()
print(tokenize("(A \\wedge (B \\vee C))")) # the doctests fail, but this works. Need to do double backslash for abfnrtv.