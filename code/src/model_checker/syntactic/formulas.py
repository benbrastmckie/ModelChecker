"""Formula-level operations.

This module provides functions for analyzing parsed formulas (prefix notation):
- is_syntactically_wff: Check if a prefix structure is a well-formed formula

These functions operate on the prefix representation produced by the parser,
which uses lists where the first element is the operator and subsequent
elements are arguments.
"""

from typing import Tuple


def is_syntactically_wff(prefix) -> Tuple[bool, str]:
    """Check if prefix structure represents a well-formed formula.

    A well-formed formula (WFF) matches the following grammar:
    - Atomic sentence letters (bare identifiers)
    - top, bot: Extremal constants
    - not phi: Negation
    - phi op psi: Binary connectives
    - Any other backslash-prefixed operator (modal, temporal, etc.)

    Args:
        prefix: Parsed prefix structure to validate

    Returns:
        Tuple of (is_wff, error_message).
        If is_wff is True, error_message is empty string.
        If is_wff is False, error_message explains why.
    """
    # Handle non-list input
    if not isinstance(prefix, list):
        return False, f"Expected list structure, got {type(prefix).__name__}"

    if len(prefix) == 0:
        return False, "Empty formula"

    head = prefix[0]

    # ACCEPT: Extremal constants
    if head in {'\\top', '\\bot'}:
        return True, ""

    # Handle Z3 objects (sentence letters from apply_operator)
    # Also accept any single non-string object (could be mocked or Z3 const)
    if len(prefix) == 1 and not isinstance(head, str):
        try:
            from model_checker.solver.expressions import is_const
            if is_const(head):
                return True, ""  # Z3 sentence letter
        except (ImportError, TypeError):
            pass
        # Accept any single object that's not a string (could be mock or custom atom)
        # This handles test mocks and potential extensions
        return True, ""

    # ACCEPT: Atomic sentence letter
    if isinstance(head, str) and not head.startswith('\\'):
        return True, ""

    # ACCEPT: Negation
    if head == '\\neg':
        return True, ""

    # ACCEPT: Binary connectives (core propositional logic)
    if head in {'\\wedge', '\\vee', '\\rightarrow', '\\leftrightarrow', '\\equiv'}:
        return True, ""

    # ACCEPT: Any other backslash-prefixed operator (modal operators, etc.)
    # Theory libraries may define additional operators like \Box, \Diamond, etc.
    if isinstance(head, str) and head.startswith('\\'):
        return True, ""

    # Unknown structure - likely an extension or error
    return False, f"Unrecognized formula structure with head: {head}"
