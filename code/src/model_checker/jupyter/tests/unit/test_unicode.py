"""Unit tests for Unicode conversion utilities."""

import pytest
from model_checker.jupyter.unicode import unicode_to_latex, latex_to_unicode, normalize_formula


class TestUnicodeConversions:
    """Test Unicode to LaTeX conversions."""
    
    def test_unicode_to_latex_logical_operators(self):
        """Test converting logical operators from Unicode to LaTeX."""
        assert unicode_to_latex("p ∧ q") == "p \\wedge q"
        assert unicode_to_latex("p ∨ q") == "p \\vee q"
        assert unicode_to_latex("¬p") == "\\neg p"
        assert unicode_to_latex("p → q") == "p \\rightarrow q"
        assert unicode_to_latex("p ↔ q") == "p \\leftrightarrow q"
    
    def test_unicode_to_latex_modal_operators(self):
        """Test converting modal operators from Unicode to LaTeX."""
        assert unicode_to_latex("□p") == "\\Box p"
        assert unicode_to_latex("◇p") == "\\Diamond p"
    
    def test_unicode_to_latex_quantifiers(self):
        """Test converting quantifiers from Unicode to LaTeX."""
        assert unicode_to_latex("∀x") == "\\forall x"
        assert unicode_to_latex("∃x") == "\\exists x"
    
    def test_unicode_to_latex_combined(self):
        """Test converting complex formulas."""
        formula = "□(p → q) ∧ ◇(p ∨ ¬r)"
        expected = "\\Box (p \\rightarrow q) \\wedge \\Diamond (p \\vee \\neg r)"
        assert unicode_to_latex(formula) == expected
    
    def test_unicode_to_latex_unchanged(self):
        """Test that regular text is unchanged."""
        assert unicode_to_latex("p and q") == "p and q"
        assert unicode_to_latex("(p + q) * r") == "(p + q) * r"
    
    def test_latex_to_unicode_logical_operators(self):
        """Test converting logical operators from LaTeX to Unicode."""
        assert latex_to_unicode("p \\wedge q") == "p ∧ q"
        assert latex_to_unicode("p \\vee q") == "p ∨ q"
        assert latex_to_unicode("\\neg p") == "¬p"
        assert latex_to_unicode("p \\rightarrow q") == "p → q"
        assert latex_to_unicode("p \\leftrightarrow q") == "p ↔ q"
    
    def test_latex_to_unicode_modal_operators(self):
        """Test converting modal operators from LaTeX to Unicode."""
        assert latex_to_unicode("\\Box p") == "□p"
        assert latex_to_unicode("\\Diamond p") == "◇p"
    
    def test_latex_to_unicode_quantifiers(self):
        """Test converting quantifiers from LaTeX to Unicode."""
        assert latex_to_unicode("\\forall x") == "∀x"
        assert latex_to_unicode("\\exists x") == "∃x"
    
    def test_latex_to_unicode_combined(self):
        """Test converting complex LaTeX formulas."""
        formula = "\\Box (p \\rightarrow q) \\wedge \\Diamond (p \\vee \\neg r)"
        expected = "□(p → q) ∧ ◇(p ∨ ¬r)"
        assert latex_to_unicode(formula) == expected
    
    def test_latex_to_unicode_unchanged(self):
        """Test that non-LaTeX text is unchanged."""
        assert latex_to_unicode("p and q") == "p and q"
        assert latex_to_unicode("(p + q) * r") == "(p + q) * r"
    
    def test_normalize_formula_to_latex(self):
        """Test normalizing formula to LaTeX format."""
        assert normalize_formula("p ∧ q", "latex") == "p \\wedge q"
        assert normalize_formula("□p", "latex") == "\\Box p"
    
    def test_normalize_formula_to_unicode(self):
        """Test normalizing formula to Unicode format."""
        assert normalize_formula("p \\wedge q", "unicode") == "p ∧ q"
        assert normalize_formula("\\Box p", "unicode") == "□p"
    
    def test_normalize_formula_default(self):
        """Test that default format is LaTeX."""
        assert normalize_formula("p ∧ q") == "p \\wedge q"
    
    def test_normalize_formula_non_string(self):
        """Test normalizing non-string formulas."""
        # Should convert to string first
        assert normalize_formula(123, "latex") == "123"
        assert normalize_formula(None, "unicode") == "None"
    
    def test_bidirectional_conversion(self):
        """Test that conversions are reversible."""
        formulas = [
            "p ∧ q ∨ ¬r",
            "□(p → q) ↔ ◇r",
            "∀x ∃y (x ∧ y)",
        ]
        
        for formula in formulas:
            # Unicode -> LaTeX -> Unicode
            latex = unicode_to_latex(formula)
            back_to_unicode = latex_to_unicode(latex)
            assert back_to_unicode == formula
            
            # LaTeX -> Unicode -> LaTeX
            latex_formula = "\\Box p \\wedge \\Diamond q"
            unicode_form = latex_to_unicode(latex_formula)
            back_to_latex = unicode_to_latex(unicode_form)
            assert back_to_latex == latex_formula