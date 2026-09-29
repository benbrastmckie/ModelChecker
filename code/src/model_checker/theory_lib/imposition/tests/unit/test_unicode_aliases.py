"""Unicode-alias / LaTeX equivalence tests for the imposition theory's operators."""

import pytest

from model_checker import Syntax
from model_checker.theory_lib.imposition.operators import (
    ImpositionOperator,
    MightImpositionOperator,
    LogosCounterfactual,
    LogosMightCounterfactual,
    imposition_operators,
)


@pytest.mark.parametrize(
    "latex_formula, unicode_formula, operator_class",
    [
        ("(p \\boxright q)", "(p □→ q)", ImpositionOperator),
        ("(p \\diamondright q)", "(p ◇→ q)", MightImpositionOperator),
    ],
)
def test_unicode_alias_matches_latex_name(latex_formula, unicode_formula, operator_class):
    latex_syntax = Syntax([latex_formula], [], imposition_operators)
    unicode_syntax = Syntax([unicode_formula], [], imposition_operators)

    assert latex_syntax.premises[0].original_operator == operator_class
    assert unicode_syntax.premises[0].original_operator == operator_class


def test_logos_variants_have_no_alias_to_avoid_colliding_with_imposition_operators():
    """\\boxrightlogos / \\diamondrightlogos deliberately carry no Unicode alias:
    they subclass the logos counterfactual operators (which alias "□→"/"◇→"),
    and this same collection also registers ImpositionOperator /
    MightImpositionOperator under those same glyphs -- aliasing the logos
    variants too would collide."""
    assert LogosCounterfactual.aliases == []
    assert LogosMightCounterfactual.aliases == []
