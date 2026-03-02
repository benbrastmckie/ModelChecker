"""
Expression parsing utilities.

This module provides functions for parsing logical expressions from infix
notation to the prefix notation used internally by the framework.

Extended with first-order syntax support:
- Variables: v_x, v_1, v_foo_bar
- Constants: a<>, zero<>
- Functions: f<t1, t2, ...>
- Predicates: F[t1, t2, ...]
- Lambda abstraction: \\lambda v.phi
- Lambda application: (\\lambda v.phi)(t)
- Quantifiers: \\forall v.phi, \\exists v.phi
"""

from typing import List, Tuple, Any, Union, TYPE_CHECKING

if TYPE_CHECKING:
    from model_checker.syntactic.terms import Term, Variable


# =============================================================================
# First-order Tokenizer
# =============================================================================

def tokenize_first_order(expression: str) -> List[str]:
    """Tokenize a first-order logical expression.

    This tokenizer handles both propositional and first-order syntax:
    - Parentheses: ( )
    - Angle brackets for function application: < >
    - Square brackets for predicates: [ ]
    - Comma for argument separation: ,
    - Dot for binding scope: .
    - LaTeX operators: \\neg, \\wedge, \\lambda, \\forall, etc.
    - Identifiers: variables (v_x), constants (a), predicates (F)

    Args:
        expression: A logical expression string

    Returns:
        List of tokens preserving delimiters as separate tokens

    Examples:
        >>> tokenize_first_order("f<v_x, v_y>")
        ['f', '<', 'v_x', ',', 'v_y', '>']
        >>> tokenize_first_order("\\forall v_x. F[v_x]")
        ['\\forall', 'v_x', '.', 'F', '[', 'v_x', ']']
    """
    tokens = []
    i = 0
    n = len(expression)

    # Special single-character delimiters
    delimiters = {'(', ')', '<', '>', '[', ']', ',', '.'}

    while i < n:
        char = expression[i]

        # Skip whitespace
        if char.isspace():
            i += 1
            continue

        # Handle single-character delimiters
        if char in delimiters:
            tokens.append(char)
            i += 1
            continue

        # Handle LaTeX commands (start with \)
        if char == '\\':
            j = i + 1
            # Consume alphanumeric characters after backslash
            while j < n and (expression[j].isalnum() or expression[j] == '_'):
                j += 1
            tokens.append(expression[i:j])
            i = j
            continue

        # Handle identifiers (alphanumeric, including underscore for v_x style)
        if char.isalnum() or char == '_':
            j = i
            while j < n and (expression[j].isalnum() or expression[j] == '_'):
                j += 1
            tokens.append(expression[i:j])
            i = j
            continue

        # Unknown character - skip with warning (or could raise error)
        i += 1

    return tokens


# =============================================================================
# Term Parsing
# =============================================================================

def parse_term(tokens: List[str]) -> Tuple['Term', List[str]]:
    """Parse a first-order term from a token list.

    Handles:
    - Variables: tokens starting with v_ prefix
    - Constants: name<> (empty angle brackets)
    - Function applications: name<t1, t2, ...>

    Args:
        tokens: List of tokens to parse (modified in place)

    Returns:
        Tuple of (parsed Term, remaining tokens)

    Raises:
        ValueError: If token list is empty or malformed
    """
    from model_checker.syntactic.terms import Variable, Constant, FunctionApplication

    if not tokens:
        raise ValueError("Empty token list in parse_term")

    token = tokens[0]

    # Check for variable (v_ prefix)
    if token.startswith("v_"):
        tokens.pop(0)
        return Variable(token), tokens

    # Check for function/constant (followed by <)
    if len(tokens) > 1 and tokens[1] == "<":
        name = tokens.pop(0)  # function/constant name
        tokens.pop(0)  # consume '<'

        # Check for empty args -> Constant
        if tokens and tokens[0] == ">":
            tokens.pop(0)  # consume '>'
            return Constant(name), tokens

        # Parse argument list
        args, tokens = parse_term_list(tokens, ">")

        # Consume closing '>'
        if not tokens or tokens[0] != ">":
            raise ValueError(f"Expected '>' after function arguments for {name}")
        tokens.pop(0)

        return FunctionApplication(name, tuple(args)), tokens

    # Fallback: treat as variable if starts with v_
    # (already handled above, but kept for safety)
    if token.startswith("v_"):
        tokens.pop(0)
        return Variable(token), tokens

    raise ValueError(f"Cannot parse term starting with: {token}")


def parse_term_list(tokens: List[str], terminator: str = ")") -> Tuple[List['Term'], List[str]]:
    """Parse a comma-separated list of terms.

    Args:
        tokens: Token list to parse
        terminator: Character that ends the list (not consumed)

    Returns:
        Tuple of (list of Terms, remaining tokens)
    """
    terms = []

    while tokens and tokens[0] != terminator:
        term, tokens = parse_term(tokens)
        terms.append(term)

        # Check for comma separator
        if tokens and tokens[0] == ",":
            tokens.pop(0)  # consume comma
        elif tokens and tokens[0] != terminator:
            raise ValueError(f"Expected ',' or '{terminator}' in term list, got: {tokens[0]}")

    return terms, tokens


# =============================================================================
# First-Order Expression Parsing
# =============================================================================

def parse_first_order_expression(tokens: List[str]) -> Tuple[List[Any], int]:
    """Parse a first-order logical expression.

    This extends parse_expression() to handle:
    - Variables and terms in atomic positions
    - Predicates with term arguments: F[t1, t2, ...]
    - Lambda abstractions: \\lambda v.phi
    - Lambda applications: (\\lambda v.phi)(t)
    - Quantifiers: \\forall v.phi, \\exists v.phi

    Args:
        tokens: List of tokens (modified in place)

    Returns:
        Tuple of (prefix expression, complexity)
    """
    from model_checker.syntactic.terms import Variable, Constant, FunctionApplication, Term

    if not tokens:
        raise ValueError("Empty token list")

    token = tokens[0]

    # Handle opening parenthesis - could be grouping or lambda application
    if token == "(":
        return _parse_parenthesized_expression(tokens)

    # Handle variables (v_ prefix)
    if token.startswith("v_"):
        tokens.pop(0)
        return [Variable(token)], 0

    # Handle lambda abstraction: \lambda v.body
    if token == "\\lambda":
        return _parse_lambda_abstraction(tokens)

    # Handle quantifiers: \forall v.body, \exists v.body
    if token in {"\\forall", "\\exists"}:
        return _parse_quantifier(tokens)

    # Handle LaTeX operators
    if token.startswith("\\"):
        tokens.pop(0)

        # Nullary operators
        if token in {"\\top", "\\bot"}:
            return [token], 0

        # Unary operators
        if not tokens:
            raise ValueError(f"Empty token list after operator {token}")
        arg, comp = parse_first_order_expression(tokens)
        return [token, arg], comp + 1

    # Handle identifier (could be predicate, function, or atom)
    if token.isalnum() or token.startswith("_"):
        return _parse_identifier_expression(tokens)

    # Fallback to original parse_expression behavior
    arg, comp = parse_first_order_expression(tokens)
    return [token, arg], comp + 1


def _parse_parenthesized_expression(tokens: List[str]) -> Tuple[List[Any], int]:
    """Parse an expression starting with '('.

    Could be:
    - Grouping: (expr)
    - Lambda application: (\\lambda v.body)(arg)
    - Binary operator: (left op right)
    """
    from model_checker.syntactic.terms import Variable, Constant, Term

    tokens.pop(0)  # consume '('

    if not tokens:
        raise ValueError("Empty token list after opening parenthesis")

    # Check if it's a lambda (for lambda application)
    if tokens[0] == "\\lambda":
        # Parse the lambda
        lambda_expr, lambda_comp = _parse_lambda_abstraction(tokens)

        # Consume closing ')'
        if not tokens or tokens[0] != ")":
            raise ValueError("Expected ')' after lambda in application")
        tokens.pop(0)

        # Check for application: )(
        if tokens and tokens[0] == "(":
            tokens.pop(0)  # consume '('

            # Parse the argument term
            arg_term, tokens_after = parse_term(tokens)

            # Consume closing ')'
            if not tokens_after or tokens_after[0] != ")":
                # Might be a more complex expression, not just a term
                # Fall back to parsing as expression
                tokens.insert(0, "(")
                arg_expr, arg_comp = parse_first_order_expression(tokens)
                if tokens and tokens[0] == ")":
                    tokens.pop(0)

                # Create lambda application
                return [
                    "\\lambdaApp",
                    lambda_expr[1],  # Variable
                    lambda_expr[2],  # Body
                    arg_expr
                ], lambda_comp + 1

            tokens_after.pop(0)
            tokens.clear()
            tokens.extend(tokens_after)

            # Create lambda application
            return [
                "\\lambdaApp",
                lambda_expr[1],  # Variable
                lambda_expr[2],  # Body
                arg_term
            ], lambda_comp + 1

        # Just a parenthesized lambda, no application
        return lambda_expr, lambda_comp

    # Otherwise, it's a grouped binary expression
    # Find the matching closing paren
    depth = 1
    inner_tokens = []
    while tokens and depth > 0:
        t = tokens.pop(0)
        if t == "(":
            depth += 1
        elif t == ")":
            depth -= 1
            if depth == 0:
                break
        inner_tokens.append(t)

    if depth != 0:
        raise ValueError("Unmatched parentheses")

    # Now check for lambda application pattern: )(
    if tokens and tokens[0] == "(":
        # This is tricky - we need to see if inner_tokens was a lambda
        # Re-parse inner_tokens
        inner_copy = inner_tokens.copy()
        if inner_copy and inner_copy[0] == "\\lambda":
            lambda_expr, _ = _parse_lambda_abstraction(inner_copy)

            tokens.pop(0)  # consume '('
            arg_term, tokens_after = parse_term(tokens)

            if tokens_after and tokens_after[0] == ")":
                tokens_after.pop(0)
                tokens.clear()
                tokens.extend(tokens_after)

                return [
                    "\\lambdaApp",
                    lambda_expr[1],
                    lambda_expr[2],
                    arg_term
                ], 1

    # Parse as binary expression
    return _parse_binary_expression(inner_tokens)


def _parse_binary_expression(tokens: List[str]) -> Tuple[List[Any], int]:
    """Parse a binary expression from tokens inside parentheses."""
    from model_checker.syntactic.terms import Term

    if not tokens:
        raise ValueError("Empty binary expression")

    # Find the main operator (not inside brackets)
    depth_paren = 0
    depth_bracket = 0
    depth_angle = 0

    operator_idx = None

    for i, t in enumerate(tokens):
        if t == "(":
            depth_paren += 1
        elif t == ")":
            depth_paren -= 1
        elif t == "[":
            depth_bracket += 1
        elif t == "]":
            depth_bracket -= 1
        elif t == "<":
            depth_angle += 1
        elif t == ">":
            depth_angle -= 1
        elif depth_paren == 0 and depth_bracket == 0 and depth_angle == 0:
            # Check if this is a binary operator
            if t.startswith("\\") and t not in {"\\top", "\\bot", "\\neg", "\\lambda", "\\forall", "\\exists"}:
                operator_idx = i
                break

    if operator_idx is None:
        # No binary operator found, parse as unary or atomic
        return parse_first_order_expression(tokens)

    operator = tokens[operator_idx]
    left_tokens = tokens[:operator_idx]
    right_tokens = tokens[operator_idx + 1:]

    left_expr, left_comp = parse_first_order_expression(left_tokens)
    right_expr, right_comp = parse_first_order_expression(right_tokens)

    return [operator, left_expr, right_expr], left_comp + right_comp + 1


def _parse_identifier_expression(tokens: List[str]) -> Tuple[List[Any], int]:
    """Parse an identifier expression (predicate, constant, or function).

    Convention (Task 14):
    - Bare identifier (e.g., 'P', 'sam') -> Constant (equivalent to P<>)
    - Brackets required for predicates: P[] for zero-arity, F[x] for unary
    - Angle brackets for functions: f<x> for application, a<> explicit constant
    """
    from model_checker.syntactic.terms import Variable, Constant, FunctionApplication, Term

    name = tokens.pop(0)

    # Check for predicate: F[args]
    if tokens and tokens[0] == "[":
        tokens.pop(0)  # consume '['

        # Check for empty predicate (nullary - equivalent to atom/sentence letter)
        if tokens and tokens[0] == "]":
            tokens.pop(0)  # consume ']'
            return [name], 0

        # Parse term arguments
        args = []
        while tokens and tokens[0] != "]":
            arg_term, tokens[:] = parse_term(tokens)
            args.append(arg_term)

            if tokens and tokens[0] == ",":
                tokens.pop(0)  # consume comma
            elif tokens and tokens[0] != "]":
                raise ValueError(f"Expected ',' or ']' in predicate args, got: {tokens[0]}")

        if not tokens or tokens[0] != "]":
            raise ValueError(f"Expected ']' after predicate arguments for {name}")
        tokens.pop(0)  # consume ']'

        # Return predicate as [name, arg1, arg2, ...]
        result = [name] + args
        return result, 0

    # Check for function application or explicit constant: f<args> or a<>
    if tokens and tokens[0] == "<":
        tokens.insert(0, name)  # put name back
        term, tokens[:] = parse_term(tokens)
        return [term], 0

    # Bare identifier -> Constant (Task 14 convention)
    # Previously returned [name] as atom; now returns Constant object
    return [Constant(name)], 0


def _parse_lambda_abstraction(tokens: List[str]) -> Tuple[List[Any], int]:
    """Parse lambda abstraction: \\lambda v.body"""
    from model_checker.syntactic.terms import Variable

    tokens.pop(0)  # consume '\lambda'

    if not tokens:
        raise ValueError("Expected variable after \\lambda")

    # Parse the bound variable
    var_token = tokens.pop(0)
    if not var_token.startswith("v_"):
        raise ValueError(f"Lambda variable must start with v_, got: {var_token}")
    bound_var = Variable(var_token)

    # Expect '.'
    if not tokens or tokens[0] != ".":
        raise ValueError("Expected '.' after lambda variable")
    tokens.pop(0)  # consume '.'

    # Parse the body
    body, body_comp = parse_first_order_expression(tokens)

    return ["\\lambda", bound_var, body], body_comp + 1


def _parse_quantifier(tokens: List[str]) -> Tuple[List[Any], int]:
    """Parse quantifier: \\forall v.body or \\exists v.body"""
    from model_checker.syntactic.terms import Variable

    quantifier = tokens.pop(0)  # '\forall' or '\exists'

    if not tokens:
        raise ValueError(f"Expected variable after {quantifier}")

    # Parse the bound variable
    var_token = tokens.pop(0)
    if not var_token.startswith("v_"):
        raise ValueError(f"Quantifier variable must start with v_, got: {var_token}")
    bound_var = Variable(var_token)

    # Expect '.'
    if not tokens or tokens[0] != ".":
        raise ValueError(f"Expected '.' after {quantifier} variable")
    tokens.pop(0)  # consume '.'

    # Parse the body
    body, body_comp = parse_first_order_expression(tokens)

    # Return surface representation (evaluator handles lambda equivalence)
    return [quantifier, bound_var, body], body_comp + 1


# =============================================================================
# Original Propositional Parsing (unchanged for backward compatibility)
# =============================================================================


def parse_expression(tokens: List[str]) -> Tuple[List[Any], int]:
    """Parses a list of tokens representing a propositional expression and returns
    the expression in prefix notation.
    """
    if not tokens:  # Check if tokens are empty before processing
        raise ValueError("Empty token list")
    token = tokens.pop(0)  # Get the next token
    if token == "(":  # Handle binary operator case (indicated by parentheses)
        if not tokens:  # Check if tokens are empty after removing first token
            raise ValueError(f"Empty token list after opening parenthesis")
        closing_parentheses = tokens.pop()  # Remove the closing parenthesis
        if closing_parentheses != ")":
            raise SyntaxError(
                f"The sentence {tokens} is missing a closing parenthesis."
            )
        if not tokens:  # Check if tokens are empty after removing parentheses
            raise ValueError(f"Empty token list after removing parentheses")
        operator, left, right = op_left_right(tokens)
        left_arg, left_comp = parse_expression(left)  # Parse the left argument
        right_arg, right_comp = parse_expression(right)  # Parse the right argument
        complexity = left_comp + right_comp + 1
        return [operator, left_arg, right_arg], complexity 
    if token.isalnum():  # Handle atomic sentences
        return [token], 0
    elif token.startswith("\\"):  # Handle all LaTeX operators 
        # This includes: \top, \bot, \Future, \Past, \future, \past, etc.
        # Special case for nullary operators like \top and \bot
        if token in {"\\top", "\\bot"}:
            return [token], 0
        if not tokens:  # Check if tokens are empty after operator
            raise ValueError(f"Empty token list after operator {token}")
        arg, comp = parse_expression(tokens)
        return [token, arg], comp + 1
    arg, comp = parse_expression(tokens)
    return [token, arg], comp + 1 


def op_left_right(tokens: List[str]) -> Tuple[str, List[str], List[str]]:
    """Divides whatever is inside a pair of parentheses into the left argument,
    right argument, and the operator."""

    def balanced_parentheses(tokens: List[str]) -> bool:
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

    def check_right(tokens: List[str], operator: str) -> List[str]:
        if not tokens:
            raise ValueError(f"Expected an argument after the operator {operator}")
        if not balanced_parentheses(tokens):
            raise ValueError(
                f"Unbalanced parentheses for the tokens {tokens} " + 
                f"with the operator {operator}."
            )
        return tokens  # Remaining tokens are the right argument

    def cut_parentheses(left: List[str], tokens: List[str]) -> Tuple[str, List[str], List[str]]:
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

    def process_operator(tokens: List[str]) -> str:
        if tokens:
            return tokens.pop(0)
        raise ValueError("Operator missing after operand")

    def extract_arguments(tokens: List[str]) -> Tuple[str, List[str], List[str]]:
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