"""Unicode-alias / LaTeX equivalence tests for the extensional subtheory.

Confirms that the `aliases` declared on each extensional operator in
`operators.py` parse to the same operator class as the operator's canonical
LaTeX `name` (the user-specifiable Unicode operator characters feature).
"""

import pytest

from model_checker import Syntax
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.theory_lib.logos.subtheories.extensional.operators import (
    NegationOperator,
    AndOperator,
    OrOperator,
    ConditionalOperator,
    BiconditionalOperator,
)


@pytest.fixture
def operator_collection():
    registry = LogosOperatorRegistry()
    registry.load_subtheories(["extensional"])
    return registry.operator_collection


@pytest.mark.parametrize(
    "latex_formula, unicode_formula, operator_class",
    [
        ("\\neg p", "¬ p", NegationOperator),
        ("(p \\wedge q)", "(p ∧ q)", AndOperator),
        ("(p \\vee q)", "(p ∨ q)", OrOperator),
        ("(p \\rightarrow q)", "(p → q)", ConditionalOperator),
        ("(p \\leftrightarrow q)", "(p ↔ q)", BiconditionalOperator),
    ],
)
def test_unicode_alias_matches_latex_name(
    operator_collection, latex_formula, unicode_formula, operator_class
):
    latex_syntax = Syntax([latex_formula], [], operator_collection)
    unicode_syntax = Syntax([unicode_formula], [], operator_collection)

    assert latex_syntax.premises[0].original_operator == operator_class
    assert unicode_syntax.premises[0].original_operator == operator_class
