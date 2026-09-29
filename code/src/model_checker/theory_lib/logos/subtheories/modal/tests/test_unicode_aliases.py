"""Unicode-alias / LaTeX equivalence tests for the modal subtheory."""

import pytest

from model_checker import Syntax
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.theory_lib.logos.subtheories.modal.operators import (
    NecessityOperator,
    PossibilityOperator,
)


@pytest.fixture
def operator_collection():
    registry = LogosOperatorRegistry()
    registry.load_subtheories(["modal"])
    return registry.operator_collection


@pytest.mark.parametrize(
    "latex_formula, unicode_formula, operator_class",
    [
        ("\\Box p", "□ p", NecessityOperator),
        ("\\Diamond p", "◇ p", PossibilityOperator),
    ],
)
def test_unicode_alias_matches_latex_name(
    operator_collection, latex_formula, unicode_formula, operator_class
):
    latex_syntax = Syntax([latex_formula], [], operator_collection)
    unicode_syntax = Syntax([unicode_formula], [], operator_collection)

    assert latex_syntax.premises[0].original_operator == operator_class
    assert unicode_syntax.premises[0].original_operator == operator_class


def test_no_alias_declared_for_counterfactual_modal_variants(operator_collection):
    """\\CFBox / \\CFDiamond deliberately have no Unicode alias -- aliasing them
    would collide with \\Box / \\Diamond's own "□" / "◇" aliases."""
    from model_checker.theory_lib.logos.subtheories.modal.operators import (
        CFNecessityOperator,
        CFPossibilityOperator,
    )

    assert CFNecessityOperator.aliases == []
    assert CFPossibilityOperator.aliases == []
