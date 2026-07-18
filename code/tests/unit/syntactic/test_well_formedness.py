"""Tests for well-formedness checking of propositional sentences.

Validates Sentence construction and parsing for propositional (non-first-order)
formulas.
"""

import pytest
from model_checker.syntactic import Sentence
from model_checker.syntactic.errors import ParseError, InvalidFormulaError


class TestSentenceAcceptanceOfPropositional:
    """Tests propositional syntax parsing and acceptance."""

    def test_simple_propositional_atom(self):
        """Simple atom 'p' is accepted."""
        s = Sentence("p")
        assert s.name == "p"
        assert s.prefix_sentence == ["p"]

    def test_propositional_conjunction(self):
        """(p \\wedge q) works."""
        s = Sentence("(p \\wedge q)")
        assert s.prefix_sentence[0] == "\\wedge"

    def test_propositional_disjunction(self):
        """(p \\vee q) works."""
        s = Sentence("(p \\vee q)")
        assert s.prefix_sentence[0] == "\\vee"

    def test_propositional_negation(self):
        """\\neg p works."""
        s = Sentence("\\neg p")
        assert s.prefix_sentence[0] == "\\neg"

    def test_complex_propositional_formula(self):
        """((p \\wedge q) \\rightarrow r) works."""
        s = Sentence("((p \\wedge q) \\rightarrow r)")
        assert s.prefix_sentence[0] == "\\rightarrow"

    def test_top_constant(self):
        """\\top is accepted."""
        s = Sentence("\\top")
        assert s.prefix_sentence == ["\\top"]

    def test_bot_constant(self):
        """\\bot is accepted."""
        s = Sentence("\\bot")
        assert s.prefix_sentence == ["\\bot"]


class TestSentenceEdgeCases:
    """Tests for edge cases and boundary conditions."""

    def test_empty_formula_rejected(self):
        """Empty string is rejected."""
        with pytest.raises(InvalidFormulaError):
            Sentence("")
