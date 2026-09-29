"""Unicode-alias / LaTeX equivalence tests for the counterfactual subtheory."""

import pytest

from model_checker import Syntax
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.theory_lib.logos.subtheories.counterfactual.operators import (
    CounterfactualOperator,
    MightCounterfactualOperator,
)


@pytest.fixture
def operator_collection():
    registry = LogosOperatorRegistry()
    registry.load_subtheories(["counterfactual"])
    return registry.operator_collection


@pytest.mark.parametrize(
    "latex_formula, unicode_formula, operator_class",
    [
        ("(p \\boxright q)", "(p □→ q)", CounterfactualOperator),
        ("(p \\diamondright q)", "(p ◇→ q)", MightCounterfactualOperator),
    ],
)
def test_unicode_alias_matches_latex_name(
    operator_collection, latex_formula, unicode_formula, operator_class
):
    latex_syntax = Syntax([latex_formula], [], operator_collection)
    unicode_syntax = Syntax([unicode_formula], [], operator_collection)

    assert latex_syntax.premises[0].original_operator == operator_class
    assert unicode_syntax.premises[0].original_operator == operator_class


def test_candidate_variants_do_not_inherit_the_boxright_alias():
    """The context-free candidate clauses in `candidates.py` (\\boxrightI,
    \\boxrightW, etc.) subclass `CounterfactualOperator` but must not inherit
    its "□→" alias -- they have distinct canonical names precisely so they can
    be individually selected, and several are registered together (e.g. by
    `frame_oracle.py`), which would collide if they shared one alias."""
    from model_checker.theory_lib.logos.subtheories.counterfactual.candidates import (
        CANDIDATE_OPERATORS,
    )

    for key, cls in CANDIDATE_OPERATORS.items():
        assert cls.aliases == [], f"candidate '{key}' ({cls.__name__}) must not declare aliases"
