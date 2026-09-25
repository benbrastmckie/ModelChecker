"""Integration tests for Until and Since temporal operators against the certificate
encoding (Phase 18 rewrite).

The retired version of this file asserted `find_truth_condition` signature/mock-based Z3
plumbing that no longer exists at all (operators now have only `true_at`/`false_at`,
already covered directly against `translate`'s own rules by
`tests/unit/test_operators.py`'s `TestPrimitiveOperatorsMirrorTranslate`), so this rewrite
drops that layer entirely rather than patching it, and instead tests the semantic claims
the retired file's own docstring named as its "Key tests" -- run end-to-end through the
real `Syntax -> ModelConstraints -> BimodalStructure -> run_test()` pipeline, since that is
the only way to check a genuine semantic equivalence (a claim about every model, not about
one hand-built Z3 term):

- `U(p, top)` (i.e. `(p \\Until \\neg\\bot)`) is equivalent to `future p`
- `S(p, top)` (i.e. `(p \\Since \\neg\\bot)`) is equivalent to `past p`
- The open guard interval: a guard that fails strictly between now and the event time
  blocks Until/Since, even though the event itself holds later/earlier
- Boundary/immediate-witness behaviour: `(p \\Until \\bot)` (`\\next p`) is witnessed only by
  the immediately next position, since `bot` never holds to bridge a wider gap
"""

from __future__ import annotations

from model_checker import ModelConstraints, Syntax, run_test
from model_checker.theory_lib.bimodal import (
    BimodalProposition,
    BimodalSemantics,
    BimodalStructure,
    bimodal_operators,
)
from model_checker.theory_lib.bimodal.operators import bimodal_operators as _bimodal_operators
from model_checker.utils.context import isolated_z3_context


def _settings(**overrides):
    settings = dict(BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS)
    settings.update(overrides)
    return settings


def _run(premises, conclusions, **setting_overrides):
    example = [premises, conclusions, _settings(**setting_overrides)]
    with isolated_z3_context():
        return run_test(
            example,
            BimodalSemantics,
            BimodalProposition,
            bimodal_operators,
            Syntax,
            ModelConstraints,
            BimodalStructure,
        )


class TestOperatorsRegistered:
    def test_until_and_since_in_operator_collection(self):
        assert "\\Until" in _bimodal_operators.operator_dictionary
        assert "\\Since" in _bimodal_operators.operator_dictionary
        assert _bimodal_operators.operator_dictionary["\\Until"].arity == 2
        assert _bimodal_operators.operator_dictionary["\\Since"].arity == 2


class TestUntilSinceTopGuardEquivalence:
    """`(p \\Until top)` <-> `future p`, and the Since dual -- the retired file's own
    headline claim, checked as a real biconditional theorem."""

    def test_until_top_guard_equivalent_to_future(self):
        result = _run(
            [],
            ['((A \\Until \\neg \\bot) \\leftrightarrow \\future A)'],
            back=2, mid=1, fwd=2, expectation=False,
        )
        assert result, "(A \\Until top) <-> future A should be a theorem"

    def test_since_top_guard_equivalent_to_past(self):
        result = _run(
            [],
            ['((A \\Since \\neg \\bot) \\leftrightarrow \\past A)'],
            back=2, mid=1, fwd=2, expectation=False,
        )
        assert result, "(A \\Since top) <-> past A should be a theorem"


class TestBoundaryImmediateWitness:
    """`(p \\Until bot)` (i.e. `\\next p`) and its Since dual: witnessed only by the
    immediately next/previous position, since `bot` never holds to bridge a wider gap
    (already exercised structurally by `test_next_prev.py`'s
    `TestSemanticEquivalence.test_next_equivalent_to_until_bot`; this checks the
    *countermodel* direction -- that a merely-eventual `A` does NOT suffice)."""

    def test_until_bot_guard_is_not_equivalent_to_eventual(self):
        """`future A` does NOT imply `(A \\Until bot)`: A might hold two steps out, with a
        non-bot state at the intervening position, which `\\Until bot` (needing an *empty*
        guard interval) rejects. This is a genuine countermodel, not a theorem."""
        result = _run(
            ['\\future A'],
            ['(A \\Until \\bot)'],
            back=2, mid=2, fwd=2, expectation=True,
        )
        assert result, "future A should NOT imply (A \\Until bot): expected a countermodel"


class TestOpenGuardInterval:
    """A guard that fails strictly between now and the event time blocks Until/Since, even
    though the event itself genuinely holds later/earlier -- `(B \\Until A)` requires B at
    every intermediate position, not merely that A eventually holds."""

    def test_until_requires_guard_throughout_the_open_interval(self):
        """`future A` (A holds at *some* later time) does NOT imply `(B \\Until A)` for an
        unrelated B: nothing forces B to hold at every intermediate position. Expect a
        countermodel."""
        result = _run(
            ['\\future A'],
            ['(B \\Until A)'],
            back=2, mid=2, fwd=2, expectation=True,
        )
        assert result, "future A should NOT imply (B \\Until A): expected a countermodel"

    def test_since_requires_guard_throughout_the_open_interval(self):
        result = _run(
            ['\\past A'],
            ['(B \\Since A)'],
            back=2, mid=2, fwd=2, expectation=True,
        )
        assert result, "past A should NOT imply (B \\Since A): expected a countermodel"
