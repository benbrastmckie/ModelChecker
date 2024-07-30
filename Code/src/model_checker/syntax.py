"""
file contains all syntactic definitions

NOTES:
All commands must be strictly in lowercase. They must have nothing before or double backslash.
Sentence letters can be anything.
The unary operators are defined in a separate set for clarity in the code.
"""
from z3 import Const, DeclareSort


AtomSort = DeclareSort("AtomSort")
capital_alphabet = {"A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M",
                    "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z",}
unary_operators = {
    "\\neg", "neg",
    "\\not", "not",
    "Box", "\\Box",
    "Diamond", "\\Diamond",
}
binary_operators = {
    "\\wedge", "wedge",
    "\\vee", "vee",
    "\\rightarrow", "rightarrow",
    "\\leftrightarrow", "leftrightarrow",
    "\\boxright", "boxright",
    "\\circleright", "circleright",
    "\\imposition", "imposition",
    "\\leq", "leq",
    "\\sqsubseteq", "sqsubseteq",
    "\\equiv", "equiv",
    "\\preceq", "preceq",
}
all_operators = unary_operators.union(binary_operators)


def add_double_backslashes(tokens):
    """adds a double backslash to tokens in the output of tokenize that meet these 3 conditions:
    1. are not capital letters,
    2. do not already have a double backslash in them, AND
    3. are not parentheses
    returns the input tokens list with tokens having those qualities modified as described
    """
    new_tokens = []
    for token in tokens:
        if (token in all_operators and "\\" not in token):
            token = "\\" + token
        new_tokens.append(token)
    return new_tokens


def tokenize(str_exp):
    """
    >>> tokenize("(A /wedge (B /vee C))")
    ['(', 'A', '/wedge', '(', 'B', '/vee', 'C', ')', ')']

    >>> tokenize("(/neg A /wedge (B /vee C))")
    ['(', '/neg', 'A', '/wedge', '(', 'B', '/vee', 'C', ')', ')']

    >>> tokenize('((A /op ((C /op D) /op F)) /op E)')
    ['(', '(', 'A', '/op', '(', '(', 'C', '/op', 'D', ')', '/op', 'F', ')', ')', '/op', 'E', ')']

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
            return split_str  # else case: covers sentence letter case and latex operator case
        tokenized_l = tokenize_improved_input([split_str[0]])
        tokenized_l.extend(tokenize_improved_input(split_str[1:]))
        return tokenized_l

    raw_tokens = tokenize_improved_input(split_str)
    return add_double_backslashes(raw_tokens)

def rejoin_tokens(tokens):
    infix_expr = ''
    for token in tokens:
        if token in binary_operators:
            token = f' {token} '
        if token in unary_operators:
            token = f'{token} '
        infix_expr += token
    return infix_expr

def add_backslashes_to_infix(infix_expr):
    tokens_with_backslashes = tokenize(infix_expr)
    rejoined_with_backslashes = rejoin_tokens(tokens_with_backslashes)
    return rejoined_with_backslashes

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
    if tokenized_expression[0] != "(":
        raise ValueError(tokenized_expression, "Error: parentheses unmatched")
    # [1:] to exclude the left parens (thus complexity) of the main operator
    for i, token in enumerate(tokenized_expression[1:]):
        if token == "(":
            left_parentheses += 1
        elif token == ")":
            right_parentheses += 1
        elif (
            token in unary_operators
        ):  # ignore this case since this func is for binary complexity
            continue
        if left_parentheses == right_parentheses:
            # +1 bc list is [1:] and we want original index, and +1 bc it's next
            # elem where the main op is
            return i + 2
    raise ValueError(
        tokenized_expression,
        f"Looks like nothing was passed into main_op_index ({tokenized_expression})",
    )

# # M: most likely not necessary, but leaving here in case later it is
# def find_atom_strings(tokens):
#     """make list of all basic tokens to apply AtomSort to"""
#     pass


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
    if tokens[0] in unary_operators:  # must go before bin_comp_tokens == 0 case
        return [tokens[0], parse(tokens[1:])]
    if bin_comp_tokens == 0:
        token = tokens[0]
        return [Const(token, AtomSort)]  # Const is a function to make a constant
    main_operator_index = main_op_index(tokens)  # determines how far the operation is
    op_str = tokens[main_operator_index]
    # start 1 (exclude first parenthesis), stop at same pos of above (exclusive)
    left_expression = tokens[1:main_operator_index]
    if main_operator_index is None:
        raise SyntaxError("Error: 'main_operator_index' is not set.")
    # from pos of op plus 1 to the penultimate, thus excluding the last
    # parentheses, which belongs to the main expression
    right_expression = tokens[main_operator_index + 1 : -1]
    return [op_str, parse(left_expression), parse(right_expression)]


def prefix(infix_sentence):
    """takes a sentence in infix notation and translates it to prefix notation"""
    return parse(tokenize(infix_sentence))


def infix(prefix_sent):
    """takes a sentence in prefix notation and translates it to infix notation"""
    if len(prefix_sent) == 1:
        return str(prefix_sent[0])
    op = prefix_sent[0]
    if len(prefix_sent) == 2:
        return f"{op} {infix(prefix_sent[1])}"
    left_expr = prefix_sent[1]
    right_expr = prefix_sent[2]
    return f"({infix(left_expr)} {op} {infix(right_expr)})"

# moved unused prefix_combine to the boneyard
