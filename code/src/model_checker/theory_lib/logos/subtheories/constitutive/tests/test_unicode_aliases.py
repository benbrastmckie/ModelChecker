"""Unicode-alias / LaTeX equivalence tests for the constitutive subtheory."""

import pytest

from model_checker import Syntax
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.theory_lib.logos.subtheories.constitutive.operators import (
    IdentityOperator,
    GroundOperator,
    EssenceOperator,
    RelevanceOperator,
    ReductionOperator,
)


@pytest.fixture
def operator_collection():
    registry = LogosOperatorRegistry()
    # ReductionOperator's derived_definition expands through \wedge, so
    # 'extensional' must be loaded too (matches test_constitutive_examples.py's
    # own registry setup).
    registry.load_subtheories(["extensional", "modal", "constitutive"])
    return registry.operator_collection


@pytest.mark.parametrize(
    "latex_formula, unicode_formula, operator_class",
    [
        ("(p \\equiv q)", "(p ≡ q)", IdentityOperator),
        ("(p \\leq q)", "(p ≤ q)", GroundOperator),
        ("(p \\sqsubseteq q)", "(p ⊑ q)", EssenceOperator),
        ("(p \\preceq q)", "(p ⪯ q)", RelevanceOperator),
        ("(p \\Rightarrow q)", "(p ⇒ q)", ReductionOperator),
    ],
)
def test_unicode_alias_matches_latex_name(
    operator_collection, latex_formula, unicode_formula, operator_class
):
    latex_syntax = Syntax([latex_formula], [], operator_collection)
    unicode_syntax = Syntax([unicode_formula], [], operator_collection)

    assert latex_syntax.premises[0].original_operator == operator_class
    assert unicode_syntax.premises[0].original_operator == operator_class
