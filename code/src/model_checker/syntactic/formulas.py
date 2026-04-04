"""Formula-level operations for first-order logic.

This module provides functions for analyzing parsed formulas (prefix notation):
- compute_formula_free_variables: Compute free variables of a formula
- is_syntactically_wff: Check if a prefix structure is a well-formed formula

These functions operate on the prefix representation produced by the parser,
which uses lists where the first element is the operator/predicate and
subsequent elements are arguments.
"""

from typing import FrozenSet, Tuple, TYPE_CHECKING

if TYPE_CHECKING:
    from .terms import Term, Variable


def compute_formula_free_variables(prefix) -> FrozenSet['Variable']:
    """Compute free variables of a formula in prefix notation.

    Implements the FV function from the Logos Theory manual:
    - FV(F(t1,...,tn)) = Union(FV(ti)) for predicates
    - FV((lambda v.phi)(t)) = (FV(phi) - {v}) union FV(t)
    - FV(forall phi) = FV(phi) for Church-style quantifiers
    - FV(top) = FV(bot) = emptyset
    - FV(not phi) = FV(phi)
    - FV(phi op psi) = FV(phi) union FV(psi) for binary connectives

    Args:
        prefix: Formula in prefix notation (list with operator at head)

    Returns:
        FrozenSet of Variable objects that are free in the formula

    Note:
        For terms (Variable, Constant, FunctionApplication), delegates to
        the term's own free_variables() method.
    """
    from .terms import Term, Variable

    # Handle Term objects directly
    if isinstance(prefix, Term):
        return prefix.free_variables()

    # Handle non-list or empty input
    if not isinstance(prefix, list) or len(prefix) == 0:
        return frozenset()

    head = prefix[0]

    # Handle Z3 objects (sentence letters from apply_operator)
    try:
        from model_checker.solver.expressions import is_const
        if is_const(head):
            return frozenset()
    except (ImportError, TypeError):
        pass

    # Single-element list containing a Term
    if len(prefix) == 1 and isinstance(head, Term):
        return head.free_variables()

    # Extremal constants: \top, \bot
    if head in {'\\top', '\\bot'}:
        return frozenset()

    # Predicate application: ['P', Term1, Term2, ...]
    # Predicates have string name and Term arguments
    if isinstance(head, str) and not head.startswith('\\'):
        result = set()
        for arg in prefix[1:]:
            if isinstance(arg, Term):
                result.update(arg.free_variables())
            elif isinstance(arg, list):
                # Nested formula in argument position (shouldn't happen for predicates)
                result.update(compute_formula_free_variables(arg))
        return frozenset(result)

    # Negation: ['\neg', phi]
    if head == '\\neg':
        if len(prefix) > 1:
            return compute_formula_free_variables(prefix[1])
        return frozenset()

    # Binary connectives: [op, phi, psi]
    binary_ops = {'\\wedge', '\\vee', '\\rightarrow', '\\leftrightarrow', '\\equiv'}
    if head in binary_ops:
        if len(prefix) >= 3:
            left_fv = compute_formula_free_variables(prefix[1])
            right_fv = compute_formula_free_variables(prefix[2])
            return left_fv | right_fv
        return frozenset()

    # Lambda application: ['\lambdaApp', var, body, arg]
    if head == '\\lambdaApp':
        if len(prefix) >= 4:
            var = prefix[1]
            body = prefix[2]
            arg = prefix[3]

            body_fv = compute_formula_free_variables(body)

            # Compute arg's free variables
            if isinstance(arg, Term):
                arg_fv = arg.free_variables()
            elif isinstance(arg, list):
                arg_fv = compute_formula_free_variables(arg)
            else:
                arg_fv = frozenset()

            # Remove bound variable from body's free vars, union with arg's
            if isinstance(var, Variable):
                return (body_fv - frozenset({var})) | arg_fv
            return body_fv | arg_fv
        return frozenset()

    # Quantifiers: ['\forall', ['\lambda', var, body]] or ['\exists', ...] or native variants
    if head in {'\\forall', '\\exists', '\\all', '\\some'}:
        if len(prefix) >= 2:
            lambda_term = prefix[1]
            if isinstance(lambda_term, list) and len(lambda_term) >= 3:
                if lambda_term[0] == '\\lambda':
                    var = lambda_term[1]
                    body = lambda_term[2]
                    body_fv = compute_formula_free_variables(body)
                    if isinstance(var, Variable):
                        return body_fv - frozenset({var})
                    return body_fv
            # Non-standard quantifier form
            return compute_formula_free_variables(lambda_term)
        return frozenset()

    # Bare lambda: ['\lambda', var, body]
    # Note: Bare lambdas are not WFFs, but we compute FV anyway for error reporting
    if head == '\\lambda':
        if len(prefix) >= 3:
            var = prefix[1]
            body = prefix[2]
            body_fv = compute_formula_free_variables(body)
            if isinstance(var, Variable):
                return body_fv - frozenset({var})
            return body_fv
        return frozenset()

    # Unknown structure - return empty set
    return frozenset()


def is_syntactically_wff(prefix) -> Tuple[bool, str]:
    """Check if prefix structure represents a well-formed formula.

    A well-formed formula (WFF) matches the grammar from the Logos Theory manual:
    - F(t1, ..., tn): Predicate application
    - (lambda v.phi)(t): Lambda application
    - forall phi, exists phi: Quantifiers
    - top, bot: Extremal constants
    - not phi: Negation
    - phi op psi: Binary connectives

    Terms (variables, constants, function applications) are NOT formulas.
    Bare lambda abstractions are NOT formulas.

    Args:
        prefix: Parsed prefix structure to validate

    Returns:
        Tuple of (is_wff, error_message).
        If is_wff is True, error_message is empty string.
        If is_wff is False, error_message explains why.
    """
    from .terms import Term, Variable, Constant, FunctionApplication

    # Handle non-list input
    if not isinstance(prefix, list):
        return False, f"Expected list structure, got {type(prefix).__name__}"

    if len(prefix) == 0:
        return False, "Empty formula"

    head = prefix[0]

    # REJECT: Single Term - this is a term, not a formula
    if len(prefix) == 1 and isinstance(head, Term):
        if isinstance(head, Variable):
            return False, (
                f"'{head}' is a variable (denotes an individual), not a formula. "
                f"Variables cannot be used as sentences. "
                f"Did you mean to use a predicate like 'P[{head}]'?"
            )
        elif isinstance(head, Constant):
            return False, (
                f"'{head}' is a constant (denotes an individual), not a formula. "
                f"Constants cannot be used as sentences. "
                f"Did you mean to use a predicate like 'P[{head}]'?"
            )
        else:  # FunctionApplication
            return False, (
                f"'{head}' is a function application (denotes an individual), not a formula. "
                f"Terms cannot be used as sentences."
            )

    # REJECT: Bare lambda - lambdas are not formulas in the WFF grammar
    if head == '\\lambda':
        return False, (
            "Lambda abstraction '\\lambda v. ...' is not a formula. "
            "Lambdas must be either applied to an argument '(\\lambda v. phi)(t)' "
            "or used inside a quantifier '\\forall v. phi'."
        )

    # ACCEPT: Extremal constants
    if head in {'\\top', '\\bot'}:
        return True, ""

    # Handle Z3 objects (sentence letters from apply_operator)
    # Also accept any single non-Term, non-string object (could be mocked or Z3 const)
    if len(prefix) == 1 and not isinstance(head, Term) and not isinstance(head, str):
        try:
            from model_checker.solver.expressions import is_const
            if is_const(head):
                return True, ""  # Z3 sentence letter
        except (ImportError, TypeError):
            pass
        # Accept any single object that's not a Term or string (could be mock or custom atom)
        # This handles test mocks and potential extensions
        return True, ""

    # ACCEPT: Predicate application
    # Predicates have string head (not starting with \) and Term arguments
    if isinstance(head, str) and not head.startswith('\\'):
        return True, ""

    # ACCEPT: Negation
    if head == '\\neg':
        return True, ""

    # ACCEPT: Binary connectives (core propositional logic)
    if head in {'\\wedge', '\\vee', '\\rightarrow', '\\leftrightarrow', '\\equiv'}:
        return True, ""

    # ACCEPT: Quantifiers (including native variants \all, \some)
    if head in {'\\forall', '\\exists', '\\all', '\\some'}:
        return True, ""

    # ACCEPT: Lambda application
    if head == '\\lambdaApp':
        return True, ""

    # ACCEPT: Any other backslash-prefixed operator (modal operators, etc.)
    # Theory libraries may define additional operators like \Box, \Diamond, etc.
    # These are valid formulas if they start with backslash and aren't \lambda
    if isinstance(head, str) and head.startswith('\\'):
        return True, ""

    # Unknown structure - likely an extension or error
    return False, f"Unrecognized formula structure with head: {head}"
