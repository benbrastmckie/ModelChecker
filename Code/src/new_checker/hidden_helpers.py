"""
This file contains all helper functions used in `hidden_things.py`

NOTES:
Any latex commands must have double backslash.
Operators include `\\` and sentence letters do not.
The operators `\\top` and `\\bot` are reserved.
"""

### IMPORTS AND DEFINITIONS ###

from z3 import(
    Const,
    DeclareSort,
    BoolRef,
    simplify,
) 

AtomSort = DeclareSort("AtomSort")


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
                raise ValueError(f"Expected an argument after the operator {operator}")
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
            raise SyntaxError(
                f"The sentence {tokens} is missing a closing parenthesis."
            )
        tokens.pop()  # Remove the closing parenthesis
        operator, left, right = left_op_right(tokens)  # Extract operator and arguments
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