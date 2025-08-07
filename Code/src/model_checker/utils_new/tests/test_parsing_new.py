"""Test parsing functions from new location."""

import pytest
from model_checker.utils_new import parse_expression, op_left_right


def test_parse_expression_from_new_location():
    """Test that parse_expression works from new location."""
    # Simple atomic
    result, complexity = parse_expression(['A'])
    assert result == ['A']
    assert complexity == 0
    
    # Binary operator
    result, complexity = parse_expression(['(', 'A', '\\wedge', 'B', ')'])
    assert result == ['\\wedge', ['A'], ['B']]
    assert complexity == 1
    
    # Unary operator
    result, complexity = parse_expression(['\\neg', 'A'])
    assert result == ['\\neg', ['A']]
    assert complexity == 1


def test_op_left_right_from_new_location():
    """Test that op_left_right works from new location."""
    tokens = ['A', '\\wedge', 'B']
    operator, left, right = op_left_right(tokens)
    assert operator == '\\wedge'
    assert left == ['A']
    assert right == ['B']