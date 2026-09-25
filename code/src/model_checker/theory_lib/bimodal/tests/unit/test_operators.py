"""Unit tests for the bimodal operators under the certificate redesign (Phase 14): each
primitive operator's `true_at` returns the label bit of its translated formula at the eval
point (D5), matching its own case in `semantic/formula.py`'s `translate` dispatch; `\\Box`
introduces the guess variable and, when guessed false, is backed by a witness lasso through
the registry; and the whole constraint set for a nested `\\Box\\Future` example contains no
quantifier node (the certificate encoding is quantifier-free by design, D6).
"""

from __future__ import annotations

import pytest

from model_checker import z3_shim as z3
from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal.operators import bimodal_operators
from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics
from model_checker.theory_lib.bimodal.semantic.formula import Bot, Box, Imp, Snce, Untl, translate


def _settings(**overrides):
    settings = dict(BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS)
    settings.update(overrides)
    return settings


def _sentence(infix: str):
    syntax = Syntax([infix], [], bimodal_operators)
    return syntax.premises[0]


def _same_expr(a, b) -> bool:
    """Two Z3 BoolRefs denote the identical term iff their string forms match -- WitnessRegistry
    memoizes by (lasso, slot, formula), so two lookups of the same formula/position are the
    literal same Z3 object, not merely equisatisfiable ones."""
    return a.eq(b)


class TestExtensionalOperatorsDelegateGenerically:
    """NegationOperator/AndOperator/OrOperator needed no change: they already delegate to
    semantics.true_at/false_at recursively (D5's contract already)."""

    def test_negation_true_at_is_semantics_false_at_of_argument(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("\\neg A")
        argument = sentence.arguments[0]
        eval_point = {"lasso": 0, "position": 0}
        expr = sentence.operator(semantics).true_at(argument, eval_point)
        expected = semantics.false_at(argument, eval_point)
        assert _same_expr(expr, expected)

    def test_and_true_at_is_conjunction_of_semantics_true_at(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("(A \\wedge B)")
        left, right = sentence.arguments
        eval_point = {"lasso": 0, "position": 0}
        expr = sentence.operator(semantics).true_at(left, right, eval_point)
        expected = z3.And(semantics.true_at(left, eval_point), semantics.true_at(right, eval_point))
        assert _same_expr(expr, expected)

    def test_or_false_at_is_conjunction_of_semantics_false_at(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("(A \\vee B)")
        left, right = sentence.arguments
        eval_point = {"lasso": 0, "position": 0}
        expr = sentence.operator(semantics).false_at(left, right, eval_point)
        expected = z3.And(semantics.false_at(left, eval_point), semantics.false_at(right, eval_point))
        assert _same_expr(expr, expected)


class TestPrimitiveOperatorsMirrorTranslate:
    """Each rewritten primitive operator's true_at is the label bit of exactly the Formula
    `semantic/formula.py`'s translate() produces for the same sentence."""

    def test_bot_true_at_is_the_bot_label_bit(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("\\bot")
        eval_point = {"lasso": 0, "position": 0}
        expr = sentence.operator(semantics).true_at(eval_point)
        expected = semantics.witness_registry.bit(0, 0, Bot())
        assert _same_expr(expr, expected)

    def test_box_true_at_is_the_translated_box_label_bit(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("\\Box A")
        argument = sentence.arguments[0]
        eval_point = {"lasso": 1, "position": -3}
        expr = sentence.operator(semantics).true_at(argument, eval_point)
        expected_formula = translate(sentence)
        assert isinstance(expected_formula, Box)
        expected = semantics.witness_registry.bit(1, -3, expected_formula)
        assert _same_expr(expr, expected)

    def test_future_true_at_matches_translates_future_rule(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("\\Future A")
        argument = sentence.arguments[0]
        eval_point = {"lasso": 0, "position": 2}
        expr = sentence.operator(semantics).true_at(argument, eval_point)
        expected = semantics.witness_registry.bit(0, 2, translate(sentence))
        assert _same_expr(expr, expected)

    def test_past_true_at_matches_translates_past_rule(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("\\Past A")
        argument = sentence.arguments[0]
        eval_point = {"lasso": 0, "position": -2}
        expr = sentence.operator(semantics).true_at(argument, eval_point)
        expected = semantics.witness_registry.bit(0, -2, translate(sentence))
        assert _same_expr(expr, expected)

    def test_until_true_at_matches_translates_event_first_swap(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("(A \\Until B)")
        event_arg, guard_arg = sentence.arguments
        eval_point = {"lasso": 0, "position": 0}
        expr = sentence.operator(semantics).true_at(event_arg, guard_arg, eval_point)
        expected_formula = translate(sentence)
        assert isinstance(expected_formula, Untl)
        assert expected_formula.event == translate(event_arg)
        assert expected_formula.guard == translate(guard_arg)
        expected = semantics.witness_registry.bit(0, 0, expected_formula)
        assert _same_expr(expr, expected)

    def test_since_true_at_matches_translates_event_first_swap(self):
        semantics = BimodalSemantics(_settings())
        sentence = _sentence("(A \\Since B)")
        event_arg, guard_arg = sentence.arguments
        eval_point = {"lasso": 0, "position": 0}
        expr = sentence.operator(semantics).true_at(event_arg, guard_arg, eval_point)
        expected_formula = translate(sentence)
        assert isinstance(expected_formula, Snce)
        expected = semantics.witness_registry.bit(0, 0, expected_formula)
        assert _same_expr(expr, expected)

    def test_false_at_is_negation_of_true_at_for_every_rewritten_primitive(self):
        semantics = BimodalSemantics(_settings())
        cases = ["\\bot", "\\Box A", "\\Future A", "\\Past A", "(A \\Until B)", "(A \\Since B)"]
        eval_point = {"lasso": 0, "position": 0}
        for infix in cases:
            sentence = _sentence(infix)
            operator = sentence.operator(semantics)
            arguments = sentence.arguments or ()
            true_expr = operator.true_at(*arguments, eval_point)
            false_expr = operator.false_at(*arguments, eval_point)
            assert _same_expr(false_expr, z3.Not(true_expr)), infix


class TestBoxIntroducesAWitnessLassoWhenGuessedFalse:
    def test_finalize_certificate_allocates_a_witness_lasso_for_a_boxed_argument(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        sentence = _sentence("\\Box A")
        semantics.premise_behavior(sentence)
        semantics.finalize_certificate()

        argument_formula = translate(sentence.arguments[0])
        assert argument_formula in semantics.witness_registry._witness_lassos
        assert semantics._active_lassos == [0, semantics.witness_registry._witness_lassos[argument_formula]]


class TestConstraintSetIsQuantifierFree:
    def _contains_quantifier(self, expr) -> bool:
        if z3.is_quantifier(expr):
            return True
        return any(self._contains_quantifier(child) for child in expr.children())

    def test_nested_box_future_example_has_no_quantifier_anywhere(self):
        semantics = BimodalSemantics(_settings(back=2, mid=1, fwd=2))
        premise = _sentence("\\Box \\Future A")
        conclusion = _sentence("B")
        premise_constraint = semantics.premise_behavior(premise)
        conclusion_constraint = semantics.conclusion_behavior(conclusion)
        semantics.finalize_certificate()

        all_constraints = semantics.frame_constraints + [premise_constraint, conclusion_constraint]
        assert all_constraints, "expected a non-empty constraint set"
        for constraint in all_constraints:
            assert not self._contains_quantifier(constraint), constraint
