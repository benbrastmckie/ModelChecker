"""Unicode-alias / LaTeX equivalence tests for the bimodal theory's operators."""

import pytest

from model_checker import Syntax
from model_checker.theory_lib.bimodal.operators import (
    NegationOperator,
    AndOperator,
    OrOperator,
    NecessityOperator,
    FutureOperator,
    PastOperator,
    ConditionalOperator,
    BiconditionalOperator,
    DefPossibilityOperator,
    bimodal_operators,
)


@pytest.mark.parametrize(
    "latex_formula, unicode_formula, operator_class",
    [
        ("\\neg p", "¬ p", NegationOperator),
        ("(p \\wedge q)", "(p ∧ q)", AndOperator),
        ("(p \\vee q)", "(p ∨ q)", OrOperator),
        ("\\Box p", "□ p", NecessityOperator),
        ("\\Future p", "⏵ p", FutureOperator),
        ("\\Past p", "⏴ p", PastOperator),
        ("(p \\rightarrow q)", "(p → q)", ConditionalOperator),
        ("(p \\leftrightarrow q)", "(p ↔ q)", BiconditionalOperator),
        ("\\Diamond p", "◇ p", DefPossibilityOperator),
    ],
)
def test_unicode_alias_matches_latex_name(latex_formula, unicode_formula, operator_class):
    latex_syntax = Syntax([latex_formula], [], bimodal_operators)
    unicode_syntax = Syntax([unicode_formula], [], bimodal_operators)

    assert latex_syntax.premises[0].original_operator == operator_class
    assert unicode_syntax.premises[0].original_operator == operator_class


def test_until_since_and_discrete_duals_have_no_alias():
    """\\Until / \\Since have no non-alphanumeric standard glyph (their obvious
    candidates "U"/"S" would tokenize as sentence letters), and the discrete
    \\future/\\past/\\next/\\prev duals have no standard glyph distinct from
    \\Future/\\Past -- all four are deliberately left alias-free."""
    from model_checker.theory_lib.bimodal.operators import (
        UntilOperator,
        SinceOperator,
        DefFutureOperator,
        DefPastOperator,
        DefNextOperator,
        DefPrevOperator,
    )

    for cls in (
        UntilOperator,
        SinceOperator,
        DefFutureOperator,
        DefPastOperator,
        DefNextOperator,
        DefPrevOperator,
    ):
        assert cls.aliases == [], f"{cls.__name__} must not declare aliases"
