"""Unit tests for `BimodalProposition` under the certificate redesign (Phase 11): truth
values as label membership at `(lasso, position)` points, empty `proposition_constraints`,
and the no-certificate (`None`) case (D8).
"""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal.operators import bimodal_operators
from model_checker.theory_lib.bimodal.semantic.certificate import LabelledLasso, WitnessFamily
from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics
from model_checker.theory_lib.bimodal.semantic.formula import Atom, Box, translate
from model_checker.theory_lib.bimodal.semantic.proposition import BimodalProposition
from model_checker.theory_lib.bimodal.tests._build_support import _settings


def _sentence(infix: str):
    syntax = Syntax([infix], [], bimodal_operators)
    return syntax.premises[0]


def _fake_model_structure(semantics, certificate=None, target_time=None, lasso=0):
    """A minimal duck-typed stand-in for `BimodalStructure` (not rewritten until Phase 12),
    exposing exactly what `PropositionDefaults.__init__` and `BimodalProposition` read:
    `.semantics`, `.main_point`, `.model_constraints` (itself carrying `.semantics`,
    `.sentence_letters`, `.settings`), `.certificate`, `.target_time`."""
    model_constraints = SimpleNamespace(
        semantics=semantics,
        sentence_letters=[],
        settings=dict(semantics.DEFAULT_EXAMPLE_SETTINGS),
    )
    return SimpleNamespace(
        semantics=semantics,
        main_point={"lasso": lasso, "position": target_time},
        model_constraints=model_constraints,
        certificate=certificate,
        target_time=target_time,
    )


class TestPropositionConstraintsIsEmpty:
    def test_proposition_constraints_always_returns_empty_list(self):
        semantics = BimodalSemantics(_settings())
        structure = _fake_model_structure(semantics)
        sentence = _sentence("A")
        proposition = BimodalProposition(sentence, structure)
        assert proposition.proposition_constraints(sentence.sentence_letter) == []


class TestNoCertificateIsNoneNotFalse:
    def test_truth_value_is_none_without_a_certificate(self):
        semantics = BimodalSemantics(_settings())
        structure = _fake_model_structure(semantics, certificate=None)
        sentence = _sentence("A")
        proposition = BimodalProposition(sentence, structure)
        assert proposition.truth_value_at(0, 0) is None
        assert proposition.extension == {}
        assert proposition.truth_set == set()
        assert proposition.false_set == set()


class TestTruthValueIsLabelMembership:
    def _certificate_for(self, formula_in_main_label):
        """A trivial two-lasso family: main lasso (index 0) whose single label either
        contains `formula_in_main_label` or not; a second lasso whose label never does."""
        main_label = frozenset({formula_in_main_label}) if formula_in_main_label else frozenset()
        main = LabelledLasso(back=(frozenset(),), mid=(), fwd=(main_label,))
        other = LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset(),))
        return WitnessFamily(bx={}, lassos=(main, other))

    def test_atom_true_at_main_lasso_when_in_the_label(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        atom = Atom("A")
        certificate = self._certificate_for(atom)
        structure = _fake_model_structure(semantics, certificate=certificate, target_time=0)
        sentence = _sentence("A")
        proposition = BimodalProposition(sentence, structure)
        assert proposition.truth_value_at(0, 0) is True
        assert proposition.truth_value_at(1, 0) is False

    def test_atom_false_at_main_lasso_when_absent_from_the_label(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        certificate = self._certificate_for(None)
        structure = _fake_model_structure(semantics, certificate=certificate, target_time=0)
        sentence = _sentence("A")
        proposition = BimodalProposition(sentence, structure)
        assert proposition.truth_value_at(0, 0) is False

    def test_compound_truth_value_is_also_a_label_lookup(self):
        """A compound formula's truth value is read the same way as an atom's -- local
        coherence (finalize_certificate's constraints) is what ties a compound's bit to
        its constituents' bits, not any recursion in the proposition class itself."""
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        sentence = _sentence("\\Box A")
        formula = translate(sentence)
        assert isinstance(formula, Box)
        certificate = self._certificate_for(formula)
        structure = _fake_model_structure(semantics, certificate=certificate, target_time=0)
        proposition = BimodalProposition(sentence, structure)
        assert proposition.truth_value_at(0, 0) is True
        assert proposition.truth_value_at(1, 0) is False

    def test_negation_compound_truth_value_is_a_label_lookup(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        sentence = _sentence("\\neg A")
        formula = translate(sentence)
        certificate = self._certificate_for(formula)
        structure = _fake_model_structure(semantics, certificate=certificate, target_time=0)
        proposition = BimodalProposition(sentence, structure)
        assert proposition.truth_value_at(0, 0) is True
        assert proposition.truth_value_at(1, 0) is False

    def test_until_compound_truth_value_is_a_label_lookup(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        sentence = _sentence("(A \\Until B)")
        formula = translate(sentence)
        certificate = self._certificate_for(formula)
        structure = _fake_model_structure(semantics, certificate=certificate, target_time=0)
        proposition = BimodalProposition(sentence, structure)
        assert proposition.truth_value_at(0, 0) is True
        assert proposition.truth_value_at(1, 0) is False

    def test_truth_value_at_an_unknown_lasso_index_is_none(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        certificate = self._certificate_for(Atom("A"))
        structure = _fake_model_structure(semantics, certificate=certificate, target_time=0)
        sentence = _sentence("A")
        proposition = BimodalProposition(sentence, structure)
        assert proposition.truth_value_at(5, 0) is None


class TestFindExtensionAndProposition:
    def test_extension_covers_every_lasso_over_the_representative_window(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        atom = Atom("A")
        main_label = frozenset({atom})
        main = LabelledLasso(back=(frozenset(),), mid=(), fwd=(main_label,))
        other = LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset(),))
        certificate = WitnessFamily(bx={}, lassos=(main, other))
        structure = _fake_model_structure(semantics, certificate=certificate, target_time=0)
        sentence = _sentence("A")
        proposition = BimodalProposition(sentence, structure)

        assert set(proposition.extension.keys()) == {0, 1}
        true_positions, false_positions = proposition.extension[0]
        assert 0 in true_positions
        other_true, other_false = proposition.extension[1]
        assert other_true == []

    def test_find_proposition_at_reports_lasso_indices(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        atom = Atom("A")
        main_label = frozenset({atom})
        main = LabelledLasso(back=(frozenset(),), mid=(), fwd=(main_label,))
        other = LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset(),))
        certificate = WitnessFamily(bx={}, lassos=(main, other))
        structure = _fake_model_structure(semantics, certificate=certificate, target_time=0)
        sentence = _sentence("A")
        proposition = BimodalProposition(sentence, structure)

        assert proposition.truth_set == {0}
        assert proposition.false_set == {1}

    def test_print_proposition_does_not_raise(self, capsys):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        atom = Atom("A")
        main_label = frozenset({atom})
        main = LabelledLasso(back=(frozenset(),), mid=(), fwd=(main_label,))
        certificate = WitnessFamily(bx={}, lassos=(main,))
        structure = _fake_model_structure(semantics, certificate=certificate, target_time=0)
        sentence = _sentence("A")
        proposition = BimodalProposition(sentence, structure)
        proposition.print_proposition({"lasso": 0, "position": 0}, 1, False)
        captured = capsys.readouterr()
        assert "|A|" in captured.out
        assert "(True at L0, t=0)" in captured.out
        assert "in lasso" not in captured.out
        # The extension set is printed with the `L{i}` lasso-name convention, not a bare
        # integer index -- a bare `{0}` is ambiguous with a time on a line that also reads
        # `t=0`.
        assert "{L0}" in captured.out


class TestReprUsesLassoNamesNotBareIndices:
    """The extended set repr must never print a bare lasso-index integer (ambiguous with a
    time), and must use the same `L{i}` naming the rest of the printed block already uses."""

    def test_repr_names_lassos_with_the_l_prefix(self):
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        atom = Atom("A")
        main_label = frozenset({atom})
        main = LabelledLasso(back=(frozenset(),), mid=(), fwd=(main_label,))
        other = LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset(),))
        certificate = WitnessFamily(bx={}, lassos=(main, other))
        structure = _fake_model_structure(semantics, certificate=certificate, target_time=0)
        sentence = _sentence("A")
        proposition = BimodalProposition(sentence, structure)
        text = repr(proposition)
        assert "{L0}" in text
        assert "{0}" not in text

    def test_repr_names_multiple_lassos_in_ascending_numeric_order(self):
        """`pretty_set_print`'s own lexicographic string sort would place `L10` before `L2`;
        the repr must sort by the underlying integer instead, so a reader always sees an
        ascending sequence regardless of lasso count."""
        semantics = BimodalSemantics(_settings(back=1, mid=0, fwd=1))
        atom = Atom("A")
        main_label = frozenset({atom})
        lassos = tuple(
            LabelledLasso(back=(frozenset(),), mid=(), fwd=(main_label,))
            for _ in range(11)
        )
        certificate = WitnessFamily(bx={}, lassos=lassos)
        structure = _fake_model_structure(semantics, certificate=certificate, target_time=0)
        sentence = _sentence("A")
        proposition = BimodalProposition(sentence, structure)
        text = repr(proposition)
        # truth_set covers every lasso here (the atom is in every lasso's label).
        assert text.index("{L0,") < text.index("L2,") < text.index("L10}")
