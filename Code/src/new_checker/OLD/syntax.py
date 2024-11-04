"""
file contains all syntactic definitions

NOTES:
Any latex commands must have double backslash.
Sentence letters can be anything.
"""
from z3 import Const, DeclareSort

AtomSort = DeclareSort("AtomSort")

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
    # small issue here with doctest cases and backslashes
    split_str = str_exp.split() # splits string into list of words

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
    return raw_tokens

def binary_comp(tokenized_expression):
    """
    finds complexity, defined by number of binary operators, in a tokenized_expression.
    In reality, it counts left parentheses, but that ends up being basically the same.

    >>> binary_comp(tokenize('(A /wedge (B /vee C))'))
    2

    >>> binary_comp(tokenize('/neg (A /wedge (B /vee C))'))
    2
    """
    return len([char for char in tokenized_expression if char == "("])

def main_op_index(tokenized_expression, unary_operators_names):
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
        elif ( # this elif is necessary—e.g. token input to parse is 
                # ['(', '\\neg', 'B', '\\wedge', '\\neg', 'D', ')']
                # (it thinks B is an operator)
            token in unary_operators_names
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

def parse(tokens, model_setup):
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
    unary_operators_names = set(op_name for (op_name, op) in model_setup.operators.items() if op.arity == 1)
    bin_comp_tokens = binary_comp(tokens)
    if tokens[0] in unary_operators_names:  # must go before bin_comp_tokens == 0 case
        return [model_setup.operators[tokens[0]], parse(tokens[1:], model_setup)] # B: should 
    if bin_comp_tokens == 0:
        token = tokens[0]
        return [Const(token, AtomSort)]  # Const is a function to make a constant
    main_operator_index = main_op_index(tokens, unary_operators_names)  # determines how far the operation is
    op_str = tokens[main_operator_index]
    # start 1 (exclude first parenthesis), stop at same pos of above (exclusive)
    left_expression = tokens[1:main_operator_index]
    if main_operator_index is None:
        raise SyntaxError("Error: 'main_operator_index' is not set.")
    # from pos of op plus 1 to the penultimate, thus excluding the last
    # parentheses, which belongs to the main expression
    right_expression = tokens[main_operator_index + 1 : -1]
    return [
        model_setup.operators[op_str],
        parse(left_expression, model_setup),
        parse(right_expression, model_setup)
    ]

# M: could actually in principle be moved to ModelSetup
# B: yes, I think that makes good sense!
def prefix(infix_sentence, model_setup): 
    """takes a sentence in infix notation and translates it to prefix notation"""
    return parse(tokenize(infix_sentence), model_setup)

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

# NEW ATTEMPT

def repeats_removed(sentences):
    '''takes a list and removes the repeats in it.
    used in find_all_constraints'''
    seen = []
    for obj in sentences:
        if obj not in seen:
            seen.append(obj)
    return seen

def subsentences_of(prefix_sentence):
    '''finds all the subsentence of a prefix sentence
    returns these as a set
    used in find_extensional_subsentences'''
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

def find_subsentences(prefix_sentences):
    """take a set of prefix sentences and returns a set of all subsentences"""
    all_subsentences = []
    for prefix_sent in prefix_sentences:
        all_prefix_subs = subsentences_of(prefix_sent)
        all_subsentences.extend(all_prefix_subs)
    return repeats_removed(all_subsentences)

def left_op_right(tokens):
    """Divides whatever is inside a pair of parentheses into the left argument,
    right argument, and the operator."""
    
    count = 0  # To track nested parentheses
    left = []
    
    # Use a copy of tokens to avoid modifying the original list
    tokens = tokens[:]
    
    while tokens:
        token = tokens.pop(0)
        
        if token == '(':
            count += 1
            left.append(token)
            continue
        if token == ')':
            count -= 1
            left.append(token)
            if count < 0:
                raise ValueError("Unbalanced parentheses")
            continue
        if count > 0:  # Inside parentheses, add to the left argument
            left.append(token)
            continue
        
        # Handle alphanumeric tokens or special logical operators
        if token.isalnum() or token in {'\\top', '\\bot'}:
            left.append(token)
            if not tokens:
                raise ValueError(f"Expected an operator following {token}")
            operator = tokens.pop(0)
            if not tokens:
                raise ValueError(f"Expected an argument after the operator {operator}")
            right = tokens  # The remaining tokens are the right argument
            return operator, left, right
        
        # Otherwise, assume token is an operator and handle binary expression
        operator = token
        right = tokens
        return operator, left, right

    raise ValueError("Invalid expression or unmatched parentheses")

def parse_expression(tokens):
    """Parses a list of tokens representing a propositional logic expression and returns
    the expression in prefix notation (Polish notation)."""
    
    if not isinstance(tokens, list):
        return tokens

    def pop_token():
        """Helper function to get the next token."""
        if tokens:
            return tokens.pop(0)
        else:
            raise SyntaxError("Unexpected end of input.")

    token = pop_token()  # Get the next token
    
    # Handle binary operator case (indicated by parentheses)
    if token == '(':  
        # Ensure that the closing parenthesis is present
        final = tokens.pop()  # Remove the closing parenthesis
        if final != ')':
            raise SyntaxError(f"The sentence {tokens} is missing closing parenthesis.")

        # Extract operator and arguments
        operator, left, right = left_op_right(tokens)
        left_arg = parse_expression(left)  # Parse the left argument
        right_arg = parse_expression(right)  # Parse the right argument
        return [operator, left_arg, right_arg]

    # Handle atomic sentences and extremal elements (zero-place operators)
    if token.isalnum() or token in {'\\top', '\\bot'}:
        return [Const(token, AtomSort)]  # Return atomic sentence

    # Handle unary operator case (unary operators don't need parentheses)
    return [token, parse_expression(tokens)]  # Recursively parse the argument for unary operators

def pure_prefix(infix_sentence):
    """For converting from infix to prefix notation without knowing which
    which operators the language includes."""
    tokens = infix_sentence.replace('(', ' ( ').replace(')', ' ) ').split()
    return parse_expression(tokens)

# TESTS

# unary = '\\neg A'
# # unary_result = parse_expression(unary)
# unary_result = pure_prefix(unary)
# print(unary_result)  # Output: ['¬', 'A']

# binary = '(A \\vee B)'
# binary_result = pure_prefix(binary)
# print(binary_result)  # Output: ['∧', 'A', 'B']

# binary = '\\neg (A \\vee B)'
# binary_result = pure_prefix(binary)
# print(binary_result)  # Output: ['∧', 'A', 'B']

# comp = '((A \\random \\top) \\vee (\\bot \\operator B))'
# complex_result = pure_prefix(comp)
# print(complex_result)  # Output: ['∧', 'A', 'B']