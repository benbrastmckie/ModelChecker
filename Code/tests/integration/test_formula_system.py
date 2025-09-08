"""Unit tests for formula validation with parameterization.

This module uses parameterized testing to efficiently validate
formula syntax across different input patterns.
"""

import pytest
from tests.utils.assertions import assert_valid_formula


class TestFormulaValidation:
    """Test formula validation with parameterized inputs."""
    
    @pytest.mark.parametrize("formula,should_pass", [
        # Valid LaTeX formulas
        ("(A \\wedge B)", True),
        ("\\Box (A \\rightarrow B)", True),
        ("\\neg (A \\vee B)", True),
        ("\\Diamond p", True),
        ("(p \\leftrightarrow q)", True),
        ("\\forall x (P(x))", True),
        ("\\exists x (Q(x))", True),
        
        # Invalid Unicode formulas
        ("A ∧ B", False),
        ("□ A", False),
        ("¬ p", False),
        ("A → B", False),
        ("◇ p", False),
        
        # Malformed formulas
        ("(A \\wedge", False),
        ("A \\wedge B)", False),
        ("((A \\wedge B)", False),
        ("", False),
    ])
    def test_formula_syntax(self, formula, should_pass):
        """Test formula syntax validation."""
        if should_pass:
            # Should not raise
            assert_valid_formula(formula)
        else:
            # Should raise AssertionError
            with pytest.raises(AssertionError):
                assert_valid_formula(formula)
    
    @pytest.mark.parametrize("operator,latex,unicode", [
        ('conjunction', '\\wedge', '∧'),
        ('disjunction', '\\vee', '∨'),
        ('negation', '\\neg', '¬'),
        ('implication', '\\rightarrow', '→'),
        ('biconditional', '\\leftrightarrow', '↔'),
        ('necessity', '\\Box', '□'),
        ('possibility', '\\Diamond', '◇'),
    ])
    def test_operator_formats(self, operator, latex, unicode):
        """Test that LaTeX is preferred over Unicode."""
        # LaTeX formula should be valid
        latex_formula = f"(A {latex} B)" if operator not in ['negation', 'necessity', 'possibility'] else f"{latex} A"
        assert_valid_formula(latex_formula)
        
        # Unicode formula should be invalid
        unicode_formula = f"(A {unicode} B)" if operator not in ['negation', 'necessity', 'possibility'] else f"{unicode} A"
        with pytest.raises(AssertionError) as exc_info:
            assert_valid_formula(unicode_formula)
        assert "Unicode character" in str(exc_info.value)
    
    @pytest.mark.parametrize("depth", [1, 2, 3, 5, 10])
    def test_nested_formulas(self, depth):
        """Test deeply nested formula validation."""
        # Build nested formula
        formula = "p"
        for i in range(depth):
            formula = f"(A \\wedge {formula})"
        
        # Should be valid regardless of depth
        assert_valid_formula(formula)
        
        # Verify parentheses are balanced
        assert formula.count('(') == formula.count(')')
    
    @pytest.mark.parametrize("props", [
        ['p'],
        ['p', 'q'],
        ['p', 'q', 'r'],
        ['A', 'B', 'C', 'D', 'E'],
    ])
    def test_multiple_propositions(self, props):
        """Test formulas with varying numbers of propositions."""
        # Build conjunction of all propositions
        if len(props) == 1:
            formula = props[0]
        elif len(props) == 2:
            formula = f"({props[0]} \\wedge {props[1]})"
        else:
            # Build nested conjunction properly
            formula = props[0]
            for prop in props[1:]:
                formula = f"({formula} \\wedge {prop})"
        
        assert_valid_formula(formula)