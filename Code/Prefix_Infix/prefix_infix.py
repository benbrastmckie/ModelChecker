import doctest
from z3 import *


def tokenize(str_exp):
    """
    >>> tokenize("(A \\wedge (B \\vee C))")
    ['(', 'A', '\wedge', '(', 'B', '\vee', 'C', ')', ')']

    """
    split_str = str_exp.split()  # this is where the issue is! Fuck this shit.
    # print(split_str) # what this looks like: ['(-200.5', '**', 'x)']

    def tokenize_improved_input(split_str):
        sentence_stuff = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        if len(split_str) == 1:
            # split_str is a list with one elem (has been called recursively or is last elem)
            base_string = split_str[0]  # base_string is a string
            # 3 cases: either there is a parenthesis (2 cases, each treated differently), or there isn't
            # NOTES: 4 cases? another for latex operator?
            if "(" in base_string:  # left parentheses in base_string
                tokenized_l = ["("]
                tokenized_l.extend(tokenize_improved_input([base_string[1:]]))
                return tokenized_l
            elif ")" in base_string:  # right parentheses in base_string
                tokenized_l = tokenize_improved_input([base_string[:-1]])
                tokenized_l.append(")")
                return tokenized_l
            elif "\\" in base_string:  # latex operator case
                return split_str
            elif base_string in sentence_stuff:
                return split_str
            else:
                raise ValueError(base_string)
        tokenized_l = tokenize_improved_input([split_str[0]])
        tokenized_l.extend(tokenize_improved_input(split_str[1:]))
        return tokenized_l

    return tokenize_improved_input(split_str)


def comp(tokenized_expression):
    """
    finds complexity, defined by number of operators, in a tokenized_expression.
    In reality, it counts left parentheses. But it can easily be shown by induction
    that this number and that of operators is equal.
    # NOTES: what about negation? could it count `\\` instead?

    >>> comp(tokenize('(A /wedge (B /vee C))'))
    2
    """
    left_parentheses = 0
    for char in tokenized_expression:
        if char == "(":
            left_parentheses += 1
    return left_parentheses


def e1_comp(tokenized_expression):
    """
    given an expression with complexity > 0, finds the complexity of the
    first item. Starting after the expression's initial parenthesis, the point
    at which the number of left parentheses equals the number of right is the
    first expression (as it is closed there)
    # NOTE: what is the first expression?
    # consider: ((A \\op (B \\op C)) \\op (D \\op E))
    >>> e1_comp(tokenize('(A /wedge (B /vee C))'))
    0

    >>> e1_comp(tokenize('((A /vee B) /wedge C)'))
    1

    # >>> e1_comp(tokenize('((A /operator ((C /operator D) /operator F)) /operator E)'))
    # 3
    """
    left_parentheses = 0
    right_parentheses = 0
    for seq in tokenized_expression[1:]:  # why [1:]? # NOTE: curious about this
        if seq == "(":
            left_parentheses += 1
        elif "\\" in seq and not left_parentheses:
            return left_parentheses
        elif seq == ")":
            right_parentheses += 1
        if left_parentheses == right_parentheses:
            return left_parentheses


def parse(tokens):
    """
    >>> parse(tokenize("(A \wedge (B \lor C))"))
    ['\\wedge', ['A', ['\\lor', ['B', 'C']]]]

    # >>> parse(tokenize('((((x - y) + z) * 3) + 4)'))
    # Add(Mul(Add(Sub(Var('x'), Var('y')), Var('z')), Num(3.0)), Num(4.0))

    """
    comp_tokens = comp(tokens)
    if comp_tokens == 0:
        token = tokens[0]
        return token
    comp_e1 = e1_comp(tokens)
    op_str = tokens[comp_e1 * 4 + 2]  # determines how far the operation is
    e1 = tokens[1 : comp_e1 * 4 + 2]  # from 1 (exclude first parenthesis) to the same
    # pos of above, bc its exclusive
    e2 = tokens[comp_e1 * 4 + 3 : -1]  # from pos of op plus 1 to the penultimate,
    # thus excluding the last parentheses, which belongs to the matrix expression
    return [op_str, [parse(e1), parse(e2)]]


def Prefix(A):
    """takes a sentence in Infix notation and translates it to prefix notation"""
    return parse(tokenize(A))


def Infix(A):
    """takes a sentence in Prefix notation and translates it to infix notation"""
    pass


# doctest.testmod()
print(
    tokenize("(A \\wedge (B \\vee C))")
)  # the doctests fail, but this works. Need to do double backslash for abfnrtv.
