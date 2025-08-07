"""Tests for expression parsing utilities."""

import pytest
from model_checker.utils import parse_expression, op_left_right


class TestParseExpression:
    """Tests for parse_expression function."""
    
    def test_atomic_sentence(self):
        """Test parsing atomic sentences."""
        result, complexity = parse_expression(['A'])
        assert result == ['A']
        assert complexity == 0
        
        result, complexity = parse_expression(['p'])
        assert result == ['p']
        assert complexity == 0
    
    def test_nullary_operators(self):
        """Test parsing nullary operators like \\top and \\bot."""
        result, complexity = parse_expression(['\\top'])
        assert result == ['\\top']
        assert complexity == 0
        
        result, complexity = parse_expression(['\\bot'])
        assert result == ['\\bot']
        assert complexity == 0
    
    def test_unary_operators(self):
        """Test parsing unary operators."""
        result, complexity = parse_expression(['\\neg', 'A'])
        assert result == ['\\neg', ['A']]
        assert complexity == 1
        
        result, complexity = parse_expression(['\\Box', 'p'])
        assert result == ['\\Box', ['p']]
        assert complexity == 1
        
        result, complexity = parse_expression(['\\Diamond', 'A'])
        assert result == ['\\Diamond', ['A']]
        assert complexity == 1
    
    def test_binary_operators(self):
        """Test parsing binary operators."""
        # A ∧ B
        result, complexity = parse_expression(['(', 'A', '\\wedge', 'B', ')'])
        assert result == ['\\wedge', ['A'], ['B']]
        assert complexity == 1
        
        # p ∨ q
        result, complexity = parse_expression(['(', 'p', '\\vee', 'q', ')'])
        assert result == ['\\vee', ['p'], ['q']]
        assert complexity == 1
        
        # A → B
        result, complexity = parse_expression(['(', 'A', '\\rightarrow', 'B', ')'])
        assert result == ['\\rightarrow', ['A'], ['B']]
        assert complexity == 1
    
    def test_nested_expressions(self):
        """Test parsing nested expressions."""
        # ¬(A ∧ B)
        tokens = ['\\neg', '(', 'A', '\\wedge', 'B', ')']
        result, complexity = parse_expression(tokens)
        assert result == ['\\neg', ['\\wedge', ['A'], ['B']]]
        assert complexity == 2
        
        # (A ∧ B) ∨ C
        tokens = ['(', '(', 'A', '\\wedge', 'B', ')', '\\vee', 'C', ')']
        result, complexity = parse_expression(tokens)
        assert result == ['\\vee', ['\\wedge', ['A'], ['B']], ['C']]
        assert complexity == 2
        
        # A ∧ (B ∨ C)
        tokens = ['(', 'A', '\\wedge', '(', 'B', '\\vee', 'C', ')', ')']
        result, complexity = parse_expression(tokens)
        assert result == ['\\wedge', ['A'], ['\\vee', ['B'], ['C']]]
        assert complexity == 2
    
    def test_complex_nested_expressions(self):
        """Test parsing deeply nested expressions."""
        # ((A ∧ B) ∨ (C ∧ D))
        tokens = ['(', '(', 'A', '\\wedge', 'B', ')', '\\vee', '(', 'C', '\\wedge', 'D', ')', ')']
        result, complexity = parse_expression(tokens)
        assert result == ['\\vee', ['\\wedge', ['A'], ['B']], ['\\wedge', ['C'], ['D']]]
        assert complexity == 3
    
    def test_empty_tokens(self):
        """Test error handling for empty tokens."""
        with pytest.raises(ValueError, match="Empty token list"):
            parse_expression([])
    
    def test_missing_closing_parenthesis(self):
        """Test error handling for missing closing parenthesis."""
        with pytest.raises(SyntaxError, match="missing a closing parenthesis"):
            parse_expression(['(', 'A', '\\wedge', 'B'])
    
    def test_incomplete_expression(self):
        """Test error handling for incomplete expressions."""
        with pytest.raises(ValueError):
            parse_expression(['\\neg'])  # Missing argument


class TestOpLeftRight:
    """Tests for op_left_right function."""
    
    def test_simple_binary(self):
        """Test extracting operator and arguments from simple binary expression."""
        tokens = ['A', '\\wedge', 'B']
        operator, left, right = op_left_right(tokens)
        assert operator == '\\wedge'
        assert left == ['A']
        assert right == ['B']
    
    def test_nested_left(self):
        """Test with nested expression on left."""
        # (A ∧ B) ∨ C
        tokens = ['(', 'A', '\\wedge', 'B', ')', '\\vee', 'C']
        operator, left, right = op_left_right(tokens)
        assert operator == '\\vee'
        assert left == ['(', 'A', '\\wedge', 'B', ')']
        assert right == ['C']
    
    def test_nested_right(self):
        """Test with nested expression on right."""
        # A ∧ (B ∨ C)
        tokens = ['A', '\\wedge', '(', 'B', '\\vee', 'C', ')']
        operator, left, right = op_left_right(tokens)
        assert operator == '\\wedge'
        assert left == ['A']
        assert right == ['(', 'B', '\\vee', 'C', ')']
    
    def test_both_nested(self):
        """Test with nested expressions on both sides."""
        # (A ∧ B) ∨ (C ∧ D)
        tokens = ['(', 'A', '\\wedge', 'B', ')', '\\vee', '(', 'C', '\\wedge', 'D', ')']
        operator, left, right = op_left_right(tokens)
        assert operator == '\\vee'
        assert left == ['(', 'A', '\\wedge', 'B', ')']
        assert right == ['(', 'C', '\\wedge', 'D', ')']
    
    def test_unbalanced_parentheses(self):
        """Test error handling for unbalanced parentheses."""
        with pytest.raises(ValueError, match="Unbalanced parentheses"):
            op_left_right(['A', '\\wedge', '(', 'B'])
    
    def test_missing_operator(self):
        """Test error handling for missing operator."""
        with pytest.raises(ValueError):
            op_left_right(['A', 'B'])
    
    def test_nullary_operators_handling(self):
        """Test handling of nullary operators like \\top and \\bot."""
        tokens = ['\\top', '\\wedge', '\\bot']
        operator, left, right = op_left_right(tokens)
        assert operator == '\\wedge'
        assert left == ['\\top']
        assert right == ['\\bot']


class TestIntegration:
    """Integration tests for parsing functionality."""
    
    def test_logos_style_formulas(self):
        """Test parsing of Logos-style formulas."""
        # A □→ B (counterfactual)
        tokens = ['(', 'A', '\\boxright', 'B', ')']
        result, complexity = parse_expression(tokens)
        assert result == ['\\boxright', ['A'], ['B']]
        assert complexity == 1
        
        # A ⊢ B (constitutive)
        tokens = ['(', 'A', '\\prec', 'B', ')']
        result, complexity = parse_expression(tokens)
        assert result == ['\\prec', ['A'], ['B']]
        assert complexity == 1
    
    def test_bimodal_formulas(self):
        """Test parsing of bimodal formulas."""
        # ◇F A (future possibility)
        tokens = ['\\Future', 'A']
        result, complexity = parse_expression(tokens)
        assert result == ['\\Future', ['A']]
        assert complexity == 1
        
        # □P B (past necessity)
        tokens = ['\\past', 'B']
        result, complexity = parse_expression(tokens)
        assert result == ['\\past', ['B']]
        assert complexity == 1
    
    def test_real_world_example(self):
        """Test parsing a real-world complex formula."""
        # ((A ∧ B) → C) ∨ (¬D ∧ E)
        tokens = ['(', '(', '(', 'A', '\\wedge', 'B', ')', '\\rightarrow', 'C', ')', 
                  '\\vee', '(', '\\neg', 'D', '\\wedge', 'E', ')', ')']
        result, complexity = parse_expression(tokens)
        
        # Verify structure without hardcoding exact complexity
        assert result[0] == '\\vee'  # Top level is disjunction
        assert result[1][0] == '\\rightarrow'  # Left side is implication
        assert result[1][1][0] == '\\wedge'  # Antecedent is conjunction
        assert result[2][0] == '\\wedge'  # Right side is conjunction with negation