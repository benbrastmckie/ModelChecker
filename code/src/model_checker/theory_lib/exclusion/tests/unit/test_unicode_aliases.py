"""Unicode-alias / LaTeX equivalence tests for the exclusion theory's operators."""

import pytest

from model_checker import Syntax
from model_checker.theory_lib.exclusion.operators import (
    UniNegationOperator,
    UniConjunctionOperator,
    UniDisjunctionOperator,
    UniIdentityOperator,
    witness_operators,
)


@pytest.mark.parametrize(
    "latex_formula, unicode_formula, operator_class",
    [
        ("\\neg p", "¬ p", UniNegationOperator),
        ("(p \\wedge q)", "(p ∧ q)", UniConjunctionOperator),
        ("(p \\vee q)", "(p ∨ q)", UniDisjunctionOperator),
        ("(p \\equiv q)", "(p ≡ q)", UniIdentityOperator),
    ],
)
def test_unicode_alias_matches_latex_name(latex_formula, unicode_formula, operator_class):
    latex_syntax = Syntax([latex_formula], [], witness_operators)
    unicode_syntax = Syntax([unicode_formula], [], witness_operators)

    assert latex_syntax.premises[0].original_operator == operator_class
    assert unicode_syntax.premises[0].original_operator == operator_class
