"""Unit tests for `semantic/render.py`: user-notation rendering of closure `Formula`s.

Pins the two rendering routes and their precedence: (1) the reverse-`translate` lookup built
from a `Syntax`'s `all_sentences` (`build_names`), which prints a formula exactly as the user
wrote it; (2) the structural fallback that mirrors `Formula.lean`'s derived-operator patterns
(`¬`, `∧`, `∨`, `⊤`, `◇`, `\\Future`, `\\Past`) for any formula the user never spelled out.
Every non-ASCII glyph goes through `utils/glyphs.py`, so the cp1252 leg here follows
`TESTING_GUIDE.md` section 9.2's real-encoded-stream recipe rather than `io.StringIO`.
"""

from __future__ import annotations

import io

from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal.operators import bimodal_operators
from model_checker.theory_lib.bimodal.semantic.formula import (
    Atom,
    Bot,
    Box,
    Imp,
    Snce,
    Untl,
    translate,
)
from model_checker.theory_lib.bimodal.semantic.render import build_names, render

A = Atom("A")
B = Atom("B")
TOP = Imp(Bot(), Bot())


def _neg(f):
    return Imp(f, Bot())


class TestBuildNames:
    def test_names_map_every_sentence_and_subsentence_to_its_user_notation(self):
        syntax = Syntax(["\\Box (A \\vee B)"], [], bimodal_operators)
        names = build_names(syntax)
        outer = translate(syntax.premises[0])
        assert names[outer] == "\\Box (A \\vee B)"
        assert names[outer.child] == "(A \\vee B)"
        assert names[A] == "A"
        assert names[B] == "B"

    def test_first_seen_wins_on_duplicate_translations(self):
        """`(A \\rightarrow B)` and `(\\neg A \\vee B)` translate to the same `Formula`
        (`\\rightarrow` is derived as `\\neg A \\vee B`); the name seen first in
        `all_sentences` insertion order (premises before conclusions, outer before inner)
        is the one kept."""
        syntax = Syntax(["(A \\rightarrow B)", "(\\neg A \\vee B)"], [], bimodal_operators)
        names = build_names(syntax)
        first = translate(syntax.premises[0])
        assert first == translate(syntax.premises[1])
        assert names[first] == "(A \\rightarrow B)"

    def test_render_uses_the_users_notation_when_a_name_exists(self):
        syntax = Syntax(["\\Box (A \\vee B)"], [], bimodal_operators)
        names = build_names(syntax)
        outer = translate(syntax.premises[0])
        assert render(outer, None, names) == "\\Box (A \\vee B)"
        assert render(outer.child, None, names) == "(A \\vee B)"

    def test_names_are_consulted_at_every_depth_of_the_fallback(self):
        """A formula with no name of its own still renders named subformulas by name."""
        syntax = Syntax(["(A \\vee B)"], [], bimodal_operators)
        names = build_names(syntax)
        inner = translate(syntax.premises[0])
        assert render(Box(inner), None, names) == "□(A \\vee B)"


class TestStructuralFallback:
    """No `names`: the fallback mirrors `Formula.lean`'s derived-operator patterns."""

    def test_atom_and_bot(self):
        assert render(A, None) == "A"
        assert render(Bot(), None) == "⊥"

    def test_top(self):
        assert render(TOP, None) == "⊤"

    def test_negation(self):
        assert render(_neg(A), None) == "¬A"
        assert render(_neg(_neg(A)), None) == "¬¬A"

    def test_disjunction(self):
        assert render(Imp(_neg(A), B), None) == "(A ∨ B)"

    def test_conjunction(self):
        assert render(_neg(Imp(A, _neg(B))), None) == "(A ∧ B)"

    def test_box_and_diamond(self):
        assert render(Box(A), None) == "□A"
        assert render(_neg(Box(_neg(A))), None) == "◇A"

    def test_box_of_compound_gets_no_extra_parens(self):
        assert render(Box(Imp(_neg(A), B)), None) == "□(A ∨ B)"

    def test_until_and_since(self):
        assert render(Untl(A, B), None) == "(A U B)"
        assert render(Snce(A, B), None) == "(A S B)"

    def test_future_and_past_primitives(self):
        assert render(_neg(Untl(TOP, _neg(A))), None) == "\\Future A"
        assert render(_neg(Snce(TOP, _neg(A))), None) == "\\Past A"

    def test_generic_implication(self):
        assert render(Imp(A, B), None) == "(A → B)"

    def test_fresh_atom_keeps_its_index_visible(self):
        assert render(Atom("A", 2), None) == "A#2"


class TestGlyphFallbacks:
    """Every non-ASCII glyph resolves against the output stream's encoding (section 9.2)."""

    @staticmethod
    def _cp1252():
        return io.TextIOWrapper(io.BytesIO(), encoding="cp1252", newline="")

    def test_cp1252_stream_gets_ascii_forms_and_never_raises(self):
        stream = self._cp1252()
        text = render(_neg(Box(_neg(Imp(_neg(A), B)))), stream)
        assert text == "<>(A | B)"
        stream.write(text)
        stream.flush()

    def test_cp1252_conjunction_implication_and_constants(self):
        stream = self._cp1252()
        assert render(_neg(Imp(A, _neg(B))), stream) == "(A & B)"
        assert render(Imp(A, B), stream) == "(A -> B)"
        assert render(Bot(), stream) == "_|_"
        assert render(TOP, stream) == "T"
        assert render(Box(A), stream) == "[]A"
        # `¬` (U+00AC) is in cp1252, so it survives there; only a stricter codec
        # (e.g. pure ASCII) reaches the `~` fallback.
        assert render(_neg(A), stream) == "¬A"
        ascii_stream = io.TextIOWrapper(io.BytesIO(), encoding="ascii", newline="")
        assert render(_neg(A), ascii_stream) == "~A"

    def test_utf8_stream_keeps_unicode(self):
        stream = io.TextIOWrapper(io.BytesIO(), encoding="utf-8", newline="")
        assert render(Box(Imp(_neg(A), B)), stream) == "□(A ∨ B)"


class TestReprIsUntouched:
    """Z3 variable names in `witness_registry.py` are built from `{formula!r}`; rendering
    must never change the dataclass reprs."""

    def test_reprs_are_the_dataclass_defaults(self):
        assert repr(Box(A)) == "Box(child=Atom(base='A', fresh_index=None))"
        assert repr(Bot()) == "Bot()"
        assert repr(Imp(A, B)) == (
            "Imp(left=Atom(base='A', fresh_index=None), right=Atom(base='B', fresh_index=None))"
        )
        assert repr(Untl(A, B)) == (
            "Untl(guard=Atom(base='A', fresh_index=None), event=Atom(base='B', fresh_index=None))"
        )
        assert repr(Snce(A, B)) == (
            "Snce(guard=Atom(base='A', fresh_index=None), event=Atom(base='B', fresh_index=None))"
        )
