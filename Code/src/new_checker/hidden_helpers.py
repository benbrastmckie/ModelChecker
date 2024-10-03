"""
file contains all helper functions used in `hidden_things.py`

NOTES:
Any latex commands must have double backslash.
Operators include `\\` and sentence letters do not.
The operators `\\top` and `\\bot` are reserved.
"""

from z3 import Const, DeclareSort

AtomSort = DeclareSort("AtomSort")

### PREFIX HELPERS ###

def balanced_parentheses(tokens):
    stack = []
    for token in tokens:
        if token == '(':
            stack.append(token)
        elif token == ')':
            if not stack:
                return False
            stack.pop()
    return len(stack) == 0

def left_op_right(tokens):
    """Divides whatever is inside a pair of parentheses into the left argument,
    right argument, and the operator."""
    count = 0  # To track nested parentheses
    left = []
    operator = None
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
        elif token.isalnum() or token in {"\\top", "\\bot"}:
            left.append(token)
            if not tokens:
                raise ValueError(f"Expected an operator following {token}")
            operator = tokens.pop(0)
            if not tokens:
                raise ValueError(
                    f"Expected an argument after the operator {operator}"
                )
            if not balanced_parentheses(tokens):
                raise ValueError("Unbalanced parentheses")
            right = tokens  # Remaining tokens are the right argument
            return operator, left, right
        else:
            left.append(token)
    raise ValueError("Invalid expression or unmatched parentheses")

def parse_expression(tokens, model_setup):
    """Parses a list of tokens representing a propositional expression and returns
    the expression in prefix notation."""
    if not tokens:  # Check if tokens are empty before processing
        raise ValueError("Empty token list")
    token = tokens.pop(0)  # Get the next token
    if token == "(":  # Handle binary operator case (indicated by parentheses)
        if tokens[-1] != ")":
            raise SyntaxError(f"The sentence {tokens} is missing a closing parenthesis.")
        tokens.pop()  # Remove the closing parenthesis
        operator, left, right = left_op_right(tokens)  # Extract operator and arguments
        left_arg = parse_expression(left, model_setup)  # Parse the left argument
        right_arg = parse_expression(right, model_setup)  # Parse the right argument
        return [model_setup.operators[operator], left_arg, right_arg]
    if token.isalnum():  # Handle atomic sentences
        # B: are sentence letters lists of length 1?
        return [Const(token, AtomSort)]
    elif token in {"\\top", "\\bot"}:
        return [model_setup.operators[token]]
    return [model_setup.operators[token], parse_expression(tokens, model_setup)]  # Unary operators

