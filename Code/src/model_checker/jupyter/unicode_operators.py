"""
Operator utilities for Jupyter notebooks.

This module provides tools for working with logical operators in 
different notations (Unicode, LaTeX) in Jupyter notebooks.
"""

from typing import Dict, List, Any, Optional, Union


def normalize_formula(formula: Union[str, Any], format_type: str = "latex") -> str:
    """
    Normalize a formula to a specific format.
    
    Args:
        formula: The formula to normalize
        format_type: The target format ('latex', 'unicode', 'ascii')
        
    Returns:
        str: Normalized formula
    """
    if not isinstance(formula, str):
        return str(formula)
    
    if format_type == "latex":
        return unicode_to_latex(formula)
    elif format_type == "unicode":
        return latex_to_unicode(formula)
    else:
        return formula


def unicode_to_latex(formula: str) -> str:
    """
    Convert Unicode operators to LaTeX notation.
    
    Args:
        formula: Formula string potentially containing Unicode operators
        
    Returns:
        str: Formula with Unicode operators converted to LaTeX commands
    """
    # Unicode to LaTeX mappings
    replacements = {
        '→': '\\rightarrow',
        '∧': '\\wedge',
        '∨': '\\vee',
        '¬': '\\neg ',
        '□': '\\Box ',
        '◇': '\\Diamond ',
        '↔': '\\leftrightarrow',
        '≡': '\\equiv',
        '⊥': '\\bot',
        '⊤': '\\top'
    }
    
    # Theory-specific mappings (exclusion theory)
    exclusion_mappings = {
        '⦻': '\\exclude',   # Exclusion symbol (if used)
        '⊓': '\\uniwedge',  # Unilateral conjunction (if used)
        '⊔': '\\univee',    # Unilateral disjunction (if used)
        '≔': '\\uniequiv'   # Unilateral equivalence (if used)
    }
    
    # Apply Unicode replacements
    for unicode_op, latex_op in replacements.items():
        formula = formula.replace(unicode_op, latex_op)
    
    # Apply exclusion theory mappings
    for unicode_op, latex_op in exclusion_mappings.items():
        formula = formula.replace(unicode_op, latex_op)
    
    # Handle backslash commands that might already be in the formula
    # If someone writes `\exclude`, we need to make sure it's properly handled
    # This is important for theories that don't have Unicode equivalents
    theory_commands = [
        # Exclusion theory
        '\\exclude', '\\uniwedge', '\\univee', '\\uniequiv',
        # Default theory additions
        '\\Box', '\\Diamond', '\\rightarrow', '\\wedge', '\\vee', 
        '\\neg', '\\leftrightarrow', '\\equiv', '\\bot', '\\top'
    ]
    
    # Check if formula is already in raw string format
    is_raw = formula.startswith('r"') or formula.startswith("r'")
    
    if not is_raw:
        # If it's not a raw string, make sure we replace any theory commands
        # with properly escaped versions for Python strings
        for cmd in theory_commands:
            if cmd in formula:
                # We need to add an extra backslash for Python string processing
                # \exclude becomes \\exclude in the string
                formula = formula.replace(cmd, f"\\{cmd}")
    
    # Ensure proper parenthesization
    formula = ensure_parentheses(formula)
    
    return formula


def latex_to_unicode(formula: str) -> str:
    """
    Convert LaTeX notation to Unicode operators.
    
    Args:
        formula: Formula string with LaTeX commands (with either single or double backslashes)
        
    Returns:
        str: Formula with LaTeX commands converted to Unicode
    """
    # LaTeX to Unicode mappings (single backslash version)
    replacements = {
        '\\rightarrow': '→',
        '\\wedge': '∧',
        '\\vee': '∨',
        '\\neg': '¬',
        '\\Box': '□',
        '\\Diamond': '◇',
        '\\leftrightarrow': '↔',
        '\\equiv': '≡',
        '\\bot': '⊥',
        '\\top': '⊤',
        # Exclusion theory
        '\\exclude': '⦻',
        '\\uniwedge': '⊓',
        '\\univee': '⊔',
        '\\uniequiv': '≔'
    }
    
    # First handle double backslash version (\\rightarrow, etc.)
    double_backslash_replacements = {f"\\{key}": value for key, value in replacements.items()}
    
    # Replace double backslash LaTeX commands first
    for latex_op, unicode_op in double_backslash_replacements.items():
        formula = formula.replace(latex_op, unicode_op)
    
    # Then replace single backslash commands (for any that weren't caught by the double replacement)
    for latex_op, unicode_op in replacements.items():
        formula = formula.replace(latex_op, unicode_op)
    
    return formula


def ensure_parentheses(formula: str) -> str:
    """
    Ensure binary operators are wrapped in parentheses.
    
    Args:
        formula: Formula string
        
    Returns:
        str: Formula with proper parenthesization
    """
    binary_operators = [
        '\\rightarrow', '\\wedge', '\\vee', '\\leftrightarrow', '\\equiv',
        '\\uniwedge', '\\univee', '\\uniequiv'
    ]
    
    # If formula contains a binary operator and isn't already parenthesized,
    # wrap it in parentheses
    contains_binary_op = any(op in formula for op in binary_operators)
    already_parenthesized = formula.startswith('(') and formula.endswith(')')
    
    if contains_binary_op and not already_parenthesized:
        return f"({formula})"
    
    return formula


def test_unicode_latex_conversion():
    """
    Test the conversion between Unicode and LaTeX notation.
    
    This function tests both directions of conversion:
    1. Unicode to LaTeX: Ensures proper double backslashes
    2. LaTeX to Unicode: Ensures proper handling of both single and double backslashes
    
    Returns:
        bool: True if all tests pass, raises AssertionError otherwise
    """
    # Test unicode to latex
    unicode_formula = "p → (q ∧ ¬r) ∨ □s"
    expected_latex = "p \\rightarrow (q \\wedge \\neg r) \\vee \\Box s"
    actual_latex = unicode_to_latex(unicode_formula)
    assert expected_latex in actual_latex, f"Unicode to LaTeX conversion failed.\nExpected: {expected_latex}\nGot: {actual_latex}"
    
    # Test latex to unicode with double backslashes
    double_backslash_formula = "(p \\\\rightarrow (q \\\\wedge \\\\neg r) \\\\vee \\\\Box s)"
    expected_unicode = "(p → (q ∧ ¬r) ∨ □s)"
    actual_unicode = latex_to_unicode(double_backslash_formula)
    assert actual_unicode == expected_unicode, f"Double backslash LaTeX to Unicode conversion failed.\nExpected: {expected_unicode}\nGot: {actual_unicode}"
    
    # Test latex to unicode with single backslashes
    single_backslash_formula = "(p \\rightarrow (q \\wedge \\neg r) \\vee \\Box s)"
    actual_unicode = latex_to_unicode(single_backslash_formula)
    assert actual_unicode == expected_unicode, f"Single backslash LaTeX to Unicode conversion failed.\nExpected: {expected_unicode}\nGot: {actual_unicode}"
    
    # Test round trip conversion
    round_trip = latex_to_unicode(unicode_to_latex(unicode_formula))
    assert round_trip == unicode_formula, f"Round trip conversion failed.\nExpected: {unicode_formula}\nGot: {round_trip}"
    
    return True


def get_theory_operators(theory_name: str) -> Dict[str, Dict[str, str]]:
    """
    Get operator mappings for a specific theory.
    
    Args:
        theory_name: Name of the theory
        
    Returns:
        dict: Mappings between different operator formats
    """
    # Default theory operators
    default_operators = {
        'latex_to_unicode': {
            '\\rightarrow': '→',
            '\\wedge': '∧',
            '\\vee': '∨',
            '\\neg': '¬',
            '\\Box': '□',
            '\\Diamond': '◇',
            '\\leftrightarrow': '↔',
            '\\equiv': '≡',
            '\\bot': '⊥',
            '\\top': '⊤'
        },
        'unicode_to_latex': {
            '→': '\\rightarrow',
            '∧': '\\wedge',
            '∨': '\\vee',
            '¬': '\\neg',
            '□': '\\Box',
            '◇': '\\Diamond',
            '↔': '\\leftrightarrow',
            '≡': '\\equiv',
            '⊥': '\\bot',
            '⊤': '\\top'
        }
    }
    
    # Theory-specific additional operators
    theory_specific = {
        'exclusion': {
            'latex_to_unicode': {
                '\\exclude': '⦻',
                '\\uniwedge': '⊓',
                '\\univee': '⊔',
                '\\uniequiv': '≔'
            },
            'unicode_to_latex': {
                '⦻': '\\exclude',
                '⊓': '\\uniwedge',
                '⊔': '\\univee',
                '≔': '\\uniequiv'
            }
        }
    }
    
    # Return combined operators for the specified theory
    if theory_name in theory_specific:
        result = {
            'latex_to_unicode': {**default_operators['latex_to_unicode'], 
                                 **theory_specific[theory_name]['latex_to_unicode']},
            'unicode_to_latex': {**default_operators['unicode_to_latex'], 
                                 **theory_specific[theory_name]['unicode_to_latex']}
        }
        return result
    
    return default_operators
