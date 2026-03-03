"""Comprehensive tests for well-formedness checking.

Tests the two-level validation approach from the Logos Theory manual:
1. Syntactic category check: Is the input a well-formed formula (WFF)?
2. Closedness check: Is the formula closed (no free variables)?

This test file validates the full integration of well-formedness checking
in the Sentence class constructor.
"""

import pytest
from model_checker.syntactic import Sentence
from model_checker.syntactic.errors import ParseError


class TestSentenceRejectionOfTerms:
    """Tests that bare terms (not formulas) are rejected."""

    def test_bare_variable_rejected(self):
        """Bare variable v_x is a term, not a formula."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("v_x")
        assert "variable" in str(exc_info.value).lower()
        assert "not a formula" in str(exc_info.value).lower()

    def test_bare_constant_rejected(self):
        """Bare constant a<> is a term, not a formula."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("a<>")
        assert "constant" in str(exc_info.value).lower()
        assert "not a formula" in str(exc_info.value).lower()

    def test_function_application_rejected(self):
        """Function application f<v_x> is a term, not a formula."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("f<v_x>")
        assert "function application" in str(exc_info.value).lower()
        assert "not a formula" in str(exc_info.value).lower()

    def test_nested_function_rejected(self):
        """Nested function f<g<a<>>> is still a term."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("f<g<a<>>>")
        assert "not a formula" in str(exc_info.value).lower()


class TestSentenceRejectionOfBareLambda:
    """Tests that bare lambda abstractions are rejected."""

    def test_bare_lambda_rejected(self):
        """Lambda abstraction \\lambda v_x. P[v_x] is not a formula."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("\\lambda v_x. P[v_x]")
        assert "lambda" in str(exc_info.value).lower()
        assert "not a formula" in str(exc_info.value).lower()

    def test_bare_lambda_with_connective_rejected(self):
        """Lambda with conjunction body is still not a formula."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("\\lambda v_x. (P[v_x] \\wedge Q[v_x])")
        assert "lambda" in str(exc_info.value).lower()


class TestSentenceRejectionOfOpenFormulas:
    """Tests that open formulas (with free variables) are rejected."""

    def test_predicate_with_free_variable_rejected(self):
        """P[v_x] is a WFF but not a sentence (has free variable)."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("P[v_x]")
        assert "free variable" in str(exc_info.value).lower()
        assert "v_x" in str(exc_info.value)

    def test_binary_predicate_with_free_variables_rejected(self):
        """R[v_x, v_y] has two free variables."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("R[v_x, v_y]")
        assert "free variable" in str(exc_info.value).lower()

    def test_conjunction_with_free_variable_rejected(self):
        """(P[v_x] \\wedge Q[]) is open due to v_x."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("(P[v_x] \\wedge Q[])")
        assert "free variable" in str(exc_info.value).lower()

    def test_negation_with_free_variable_rejected(self):
        """\\neg P[v_x] is open."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("\\neg P[v_x]")
        assert "free variable" in str(exc_info.value).lower()

    def test_predicate_with_function_containing_free_var_rejected(self):
        """P[f<v_x>] has free variable v_x inside function."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("P[f<v_x>]")
        assert "free variable" in str(exc_info.value).lower()


class TestSentenceAcceptanceOfClosedFormulas:
    """Tests that valid closed formulas are accepted."""

    def test_zero_arity_predicate_accepted(self):
        """P[] is a closed zero-arity predicate (sentence letter)."""
        s = Sentence("P[]")
        assert s.name == "P[]"
        assert s.prefix_sentence == ['P']

    def test_predicate_with_constant_accepted(self):
        """P[a<>] is closed (constant has no free vars)."""
        s = Sentence("P[a<>]")
        assert s.name == "P[a<>]"

    def test_binary_predicate_with_constants_accepted(self):
        """R[a<>, b<>] is closed."""
        s = Sentence("R[a<>, b<>]")
        assert "R" in str(s.prefix_sentence)

    def test_universal_quantifier_closes_variable(self):
        """\\forall v_x. P[v_x] is closed (v_x is bound)."""
        s = Sentence("\\forall v_x. P[v_x]")
        assert s.name == "\\forall v_x. P[v_x]"
        assert s.prefix_sentence[0] == "\\forall"

    def test_existential_quantifier_closes_variable(self):
        """\\exists v_x. P[v_x] is closed (v_x is bound)."""
        s = Sentence("\\exists v_x. P[v_x]")
        assert s.name == "\\exists v_x. P[v_x]"
        assert s.prefix_sentence[0] == "\\exists"

    def test_nested_quantifiers_close_all_variables(self):
        """\\forall v_x. \\forall v_y. R[v_x, v_y] is closed."""
        s = Sentence("\\forall v_x. \\forall v_y. R[v_x, v_y]")
        assert s.prefix_sentence[0] == "\\forall"

    def test_lambda_application_is_closed(self):
        """(\\lambda v_x. P[v_x])(a<>) is closed by application."""
        s = Sentence("(\\lambda v_x. P[v_x])(a<>)")
        assert s.prefix_sentence[0] == "\\lambdaApp"

    def test_conjunction_of_closed_formulas(self):
        """(P[] \\wedge Q[]) is closed."""
        s = Sentence("(P[] \\wedge Q[])")
        assert s.prefix_sentence[0] == "\\wedge"

    def test_disjunction_of_closed_formulas(self):
        """(P[] \\vee Q[]) is closed."""
        s = Sentence("(P[] \\vee Q[])")
        assert s.prefix_sentence[0] == "\\vee"

    def test_negation_of_closed_formula(self):
        """\\neg P[] is closed."""
        s = Sentence("\\neg P[]")
        assert s.prefix_sentence[0] == "\\neg"

    def test_top_constant(self):
        """\\top is closed."""
        s = Sentence("\\top")
        assert s.prefix_sentence == ["\\top"]

    def test_bot_constant(self):
        """\\bot is closed."""
        s = Sentence("\\bot")
        assert s.prefix_sentence == ["\\bot"]


class TestSentenceAcceptanceOfPropositional:
    """Tests backward compatibility with propositional syntax."""

    def test_simple_propositional_atom(self):
        """Simple atom 'p' is still accepted."""
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


class TestSentenceEdgeCases:
    """Tests for edge cases and boundary conditions."""

    def test_empty_formula_rejected(self):
        """Empty string is rejected."""
        from model_checker.syntactic.errors import InvalidFormulaError
        with pytest.raises(InvalidFormulaError):
            Sentence("")

    def test_nested_functions_with_constant_base_accepted(self):
        """P[f<f<a<>>>] is closed."""
        s = Sentence("P[f<f<a<>>>]")
        assert s.name == "P[f<f<a<>>>>]" or "f" in str(s.prefix_sentence)

    def test_quantifier_partially_closes_formula(self):
        """\\forall v_x. R[v_x, v_y] still has free variable v_y."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("\\forall v_x. R[v_x, v_y]")
        assert "free variable" in str(exc_info.value).lower()
        assert "v_y" in str(exc_info.value)

    def test_multiple_occurrences_of_bound_variable(self):
        """\\forall v_x. R[v_x, v_x] is closed."""
        s = Sentence("\\forall v_x. R[v_x, v_x]")
        assert s.prefix_sentence[0] == "\\forall"


class TestSentenceErrorMessages:
    """Tests that error messages are helpful."""

    def test_variable_error_suggests_predicate(self):
        """Error for variable should suggest using a predicate."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("v_x")
        msg = str(exc_info.value)
        assert "P[v_x]" in msg or "predicate" in msg.lower()

    def test_constant_error_suggests_predicate(self):
        """Error for constant should suggest using a predicate."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("a<>")
        msg = str(exc_info.value)
        assert "P[a<>]" in msg or "predicate" in msg.lower()

    def test_free_variable_error_suggests_quantification(self):
        """Error for open formula should suggest quantifying."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("P[v_x]")
        msg = str(exc_info.value)
        assert "forall" in msg.lower() or "quantif" in msg.lower()

    def test_lambda_error_suggests_usage(self):
        """Error for bare lambda should suggest proper usage."""
        with pytest.raises(ParseError) as exc_info:
            Sentence("\\lambda v_x. P[v_x]")
        msg = str(exc_info.value)
        assert "apply" in msg.lower() or "quantifier" in msg.lower()
