"""Custom assertion utilities for ModelChecker tests.

This module provides specialized assertion functions for validating
ModelChecker-specific structures and behaviors.
"""

from typing import Any, Dict, List, Optional
import re


def assert_valid_formula(formula: str) -> None:
    """Assert that a formula is syntactically valid.
    
    Args:
        formula: Formula string to validate
        
    Raises:
        AssertionError: If formula is invalid
    """
    # Check for Unicode characters (should use LaTeX)
    unicode_chars = ['∧', '∨', '¬', '→', '↔', '□', '◇', '⊨', '⊭']
    for char in unicode_chars:
        assert char not in formula, \
            f"Formula contains Unicode character '{char}' - should use LaTeX notation"
    
    # Check for balanced parentheses
    paren_count = 0
    for char in formula:
        if char == '(':
            paren_count += 1
        elif char == ')':
            paren_count -= 1
        if paren_count < 0:
            assert False, "Formula has unbalanced parentheses (too many closing)"
    
    assert paren_count == 0, "Formula has unbalanced parentheses (too many opening)"
    
    # Check for valid LaTeX operators
    valid_operators = [
        '\\wedge', '\\vee', '\\neg', '\\rightarrow', '\\leftrightarrow',
        '\\Box', '\\Diamond', '\\boxright', '\\forall', '\\exists'
    ]
    
    # Basic validation - at least one operator or proposition
    assert len(formula.strip()) > 0, "Formula is empty"


def assert_model_satisfiable(model_structure) -> None:
    """Assert that a model structure represents a satisfiable model.
    
    Args:
        model_structure: ModelDefaults instance to check
        
    Raises:
        AssertionError: If model is not satisfiable
    """
    assert hasattr(model_structure, 'satisfiable'), \
        "Model structure missing 'satisfiable' attribute"
    
    assert model_structure.satisfiable is True, \
        "Model is not satisfiable"
    
    assert hasattr(model_structure, 'z3_model'), \
        "Model structure missing 'z3_model' attribute"
    
    assert model_structure.z3_model is not None, \
        "Model has no Z3 model (unsatisfiable or timeout)"


def assert_model_unsatisfiable(model_structure) -> None:
    """Assert that a model structure represents an unsatisfiable model.
    
    Args:
        model_structure: ModelDefaults instance to check
        
    Raises:
        AssertionError: If model is satisfiable
    """
    assert hasattr(model_structure, 'satisfiable'), \
        "Model structure missing 'satisfiable' attribute"
    
    assert model_structure.satisfiable is False, \
        "Model is satisfiable when unsatisfiable was expected"
    
    assert hasattr(model_structure, 'unsat_core'), \
        "Model structure missing 'unsat_core' attribute"


def assert_theory_components(theory: Dict[str, Any]) -> None:
    """Assert that a theory has all required components.
    
    Args:
        theory: Theory dictionary to validate
        
    Raises:
        AssertionError: If theory is missing required components
    """
    required = ['semantics', 'model', 'proposition', 'operators']
    
    for component in required:
        assert component in theory, \
            f"Theory missing required component: {component}"
    
    # Check operators structure
    operators = theory['operators']
    assert isinstance(operators, dict), \
        "Theory operators must be a dictionary"
    
    # Check for basic operators
    basic_ops = ['wedge', 'vee', 'neg']
    for op in basic_ops:
        assert op in operators, \
            f"Theory missing basic operator: {op}"
        
        # Validate operator has required attributes
        operator = operators[op]
        assert hasattr(operator, 'symbol'), \
            f"Operator {op} missing 'symbol' attribute"
        assert hasattr(operator, 'arity'), \
            f"Operator {op} missing 'arity' attribute"


def assert_settings_valid(settings: Dict[str, Any]) -> None:
    """Assert that settings dictionary is valid.
    
    Args:
        settings: Settings dictionary to validate
        
    Raises:
        AssertionError: If settings are invalid
    """
    # Check N value
    if 'N' in settings:
        n_value = settings['N']
        assert isinstance(n_value, int), \
            f"Setting 'N' must be an integer, got {type(n_value)}"
        assert 1 <= n_value <= 64, \
            f"Setting 'N' must be between 1 and 64, got {n_value}"
    
    # Check max_time
    if 'max_time' in settings:
        max_time = settings['max_time']
        assert isinstance(max_time, (int, float)), \
            f"Setting 'max_time' must be numeric, got {type(max_time)}"
        assert max_time > 0, \
            f"Setting 'max_time' must be positive, got {max_time}"
    
    # Check boolean settings
    bool_settings = [
        'print_constraints', 'print_z3', 'save_output',
        'print_impossible', 'maximize', 'contingent',
        'disjoint', 'non_empty', 'non_null'
    ]
    
    for setting in bool_settings:
        if setting in settings:
            value = settings[setting]
            assert isinstance(value, bool), \
                f"Setting '{setting}' must be boolean, got {type(value)}"


def assert_output_contains(output: str, expected: str, 
                          case_sensitive: bool = False) -> None:
    """Assert that output contains expected substring.
    
    Args:
        output: Output string to check
        expected: Expected substring
        case_sensitive: Whether to use case-sensitive comparison
        
    Raises:
        AssertionError: If expected substring not found
    """
    if not case_sensitive:
        output = output.lower()
        expected = expected.lower()
    
    assert expected in output, \
        f"Expected substring '{expected}' not found in output"


def assert_no_errors(output: str, stderr: str = '') -> None:
    """Assert that output contains no error indicators.
    
    Args:
        output: Standard output
        stderr: Standard error output
        
    Raises:
        AssertionError: If error indicators are found
    """
    error_indicators = [
        'error:', 'exception:', 'traceback', 'failed',
        'Error:', 'Exception:', 'Traceback', 'Failed'
    ]
    
    combined_output = output + stderr
    
    for indicator in error_indicators:
        # Allow some exceptions
        if indicator.lower() == 'failed' and 'all tests passed' in combined_output.lower():
            continue
            
        assert indicator not in combined_output, \
            f"Output contains error indicator '{indicator}'"


def assert_example_structure(example: List) -> None:
    """Assert that an example has valid structure.
    
    Args:
        example: Example list [assumptions, conclusions, settings]
        
    Raises:
        AssertionError: If example structure is invalid
    """
    assert isinstance(example, list), \
        f"Example must be a list, got {type(example)}"
    
    assert len(example) == 3, \
        f"Example must have 3 elements [assumptions, conclusions, settings], got {len(example)}"
    
    assumptions, conclusions, settings = example
    
    assert isinstance(assumptions, list), \
        f"Assumptions must be a list, got {type(assumptions)}"
    
    assert isinstance(conclusions, list), \
        f"Conclusions must be a list, got {type(conclusions)}"
    
    assert isinstance(settings, dict), \
        f"Settings must be a dict, got {type(settings)}"
    
    # Validate formulas
    for formula in assumptions + conclusions:
        if formula:  # Skip empty formulas
            assert_valid_formula(formula)
    
    # Validate settings
    assert_settings_valid(settings)


def assert_files_exist(paths: List[str]) -> None:
    """Assert that all specified files exist.
    
    Args:
        paths: List of file paths to check
        
    Raises:
        AssertionError: If any file doesn't exist
    """
    import os
    
    for path in paths:
        assert os.path.exists(path), \
            f"File does not exist: {path}"


def assert_files_not_exist(paths: List[str]) -> None:
    """Assert that specified files do not exist.
    
    Args:
        paths: List of file paths to check
        
    Raises:
        AssertionError: If any file exists
    """
    import os
    
    for path in paths:
        assert not os.path.exists(path), \
            f"File should not exist: {path}"