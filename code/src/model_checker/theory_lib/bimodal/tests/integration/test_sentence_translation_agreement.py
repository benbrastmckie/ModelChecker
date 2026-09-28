"""Sentence-translation conformance test: this repository's own `Sentence.update_types` +
`formula.translate` + `formula.to_json` against BimodalLogic's
`Tests/fixtures/sentence-translation-fixtures.jsonl` fixture corpus.

## Why this channel exists

`BimodalTools/README.md`'s "Source-sentence translation protocol" section documents
`lake exe translate_sentence`, a binary that eliminates the source language's defined operators
(`tr`) and proves (`sat_iff`) that the elimination is truth-preserving against the six-primitive
`Formula` image. That theorem is about an *encoding*; the thing that could still be wrong is
*this repository's own implementation* of that same encoding (`Sentence.update_types` deriving
primitive operator shapes, `formula.translate` walking them, `formula.to_json` serializing the
result). The fixture file plus this README section is, in that document's own words, "the
hand-off": "What the consuming repository must assert: that its own translation of `surface`
serializes to `formula` for every line ... That assertion belongs in that repository and is
deliberately not written from here." Before this module, nothing in this repository consumed
that fixture at all -- zero references anywhere in the tree.

## Forward-only

`tr_not_injective` (`FormalSystem/SourceLanguage/Sentence.lean`, per `BimodalTools/README.md`)
proves the elimination is not injective: every defined operator is sent onto the primitive
abbreviation it stands for, so a translated `Formula` does not determine a unique source
`Sentence` back. There is therefore no inverse (formula-to-sentence) pass to check, and none is
attempted here -- this module only ever renders a fixture row's `sentence` field to this
repository's infix syntax and compares the *forward* translation.

## Comparison is on parsed JSON, never on bytes

Both repositories' own docs say so independently, and the fixture demonstrates why:
`to_json`'s `untl`/`snce` branches emit `event` before `guard` (`DataExport.lean:119-121`'s own
field order), while this fixture's `sentence` field (and this repository's own `formula.to_json`
call sites elsewhere) write `guard` before `event`. Neither side promises byte stability for its
`json.dumps`/serializer choices; only structural (dict) equality is a meaningful assertion.

## Driven from `sentence`, not `surface`

A fixture row's `surface` field is the source repository's own *Polish/prefix* pretty-print
(e.g. `"\\Until p q"` with no parentheses), which this repository's `Syntax` does not parse the
same way (this repository's binary connectives are parenthesized infix: `"(p \\Until q)"`; see
`_render_sentence_ast`'s docstring). `sentence` is the structured AST BOTH repositories agree is
the source of truth for what sentence was actually meant, so this module renders `sentence` to
this repository's own infix syntax rather than attempting to reparse `surface`.

## Checkout-absence skip is a distinct, named reason

This leg needs only the BimodalLogic checkout itself (to read the fixture file) -- it never
invokes `lake` or a built binary, unlike `_lean_check.SKIP_REASON` (which additionally requires
`lake` and a bounded `check_certificate` probe). Reusing `SKIP_REASON` here would therefore skip
this leg for reasons that have nothing to do with what it actually needs, so this module computes
its own `_CHECKOUT_ABSENT_SKIP_REASON` from `_lean_check.resolve_bimodal_logic_path()` directly.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List

import pytest

from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal.operators import bimodal_operators
from model_checker.theory_lib.bimodal.semantic.formula import (
    Atom,
    Bot,
    Imp,
    Untl,
    to_json,
    translate,
)
from model_checker.theory_lib.bimodal.tests._lean_check import resolve_bimodal_logic_path

_CHECKOUT_PATH = resolve_bimodal_logic_path()
_CHECKOUT_ABSENT_SKIP_REASON = (
    "BimodalLogic checkout not found (set BIMODAL_LOGIC_PATH or check out to "
    "~/Projects/BimodalLogic) -- this leg only needs the checkout itself to read the fixture "
    "file, not `lake` or a built binary (contrast `_lean_check.SKIP_REASON`, which this module "
    "deliberately does not reuse)"
)

pytestmark = pytest.mark.skipif(_CHECKOUT_PATH is None, reason=_CHECKOUT_ABSENT_SKIP_REASON)

FIXTURE_RELATIVE_PATH = Path("Tests") / "fixtures" / "sentence-translation-fixtures.jsonl"

# Tag -> this repository's surface operator name, per `BimodalTools/README.md`'s source-sentence
# input table and `operators.py`'s `name` fields.
_TAG_TO_OPERATOR = {
    "bot": "\\bot",
    "top": "\\top",
    "neg": "\\neg",
    "box": "\\Box",
    "allFut": "\\Future",
    "allPast": "\\Past",
    "dia": "\\Diamond",
    "someFut": "\\future",
    "somePast": "\\past",
    "next": "\\next",
    "prev": "\\prev",
    "wedge": "\\wedge",
    "vee": "\\vee",
    "cond": "\\rightarrow",
    "bicond": "\\leftrightarrow",
    "untl": "\\Until",
    "snce": "\\Since",
}

# Nullary: no arguments (rendered as the bare operator token).
_NULLARY_TAGS = {"bot", "top"}
# Unary: a single `child` field, prefix-rendered with no parentheses (this repository's own
# infix grammar accepts bare "\\op child" for a unary operator -- see test_formula.py's own
# "\\Box p" / "\\Diamond p" usage).
_UNARY_TAGS = {"neg", "box", "allFut", "allPast", "dia", "someFut", "somePast", "next", "prev"}
# Binary, `left`/`right` fields, rendered as parenthesized infix "(left op right)" -- this
# repository's parser requires the parentheses for a binary connective (a bare prefix
# "\\wedge p q" parses but silently produces the wrong argument structure).
_BINARY_LEFT_RIGHT_TAGS = {"wedge", "vee", "cond", "bicond"}
# Binary, `guard`/`event` fields (Until/Since), same parenthesized-infix rendering, guard first.
_BINARY_GUARD_EVENT_TAGS = {"untl", "snce"}


def _sentence(infix: str):
    """Build one fully type-updated `Sentence` for `infix`, via the real `Syntax` pipeline and
    the theory's own `bimodal_operators` collection. Mirrors `test_formula.py`'s own `_sentence`
    idiom (duplicated here rather than imported: that module's helper is private to its own
    file, and this module's fixture-driven use only needs the same three lines)."""
    syntax = Syntax([infix], [], bimodal_operators)
    return syntax.premises[0]


def _render_sentence_ast(node: Dict[str, Any]) -> str:
    """Render one fixture row's `sentence` field (the structured source-sentence AST) to this
    repository's infix syntax, recursively. Raises `ValueError` on any tag this renderer has no
    mapping for, rather than silently skipping the row -- an unmapped tag means the fixture grew
    a constructor this channel does not cover, which is exactly the kind of drift this channel
    exists to surface."""
    tag = node.get("tag")
    if tag == "atom":
        return node["name"]
    if tag in _NULLARY_TAGS:
        return _TAG_TO_OPERATOR[tag]
    if tag in _UNARY_TAGS:
        return f"{_TAG_TO_OPERATOR[tag]} {_render_sentence_ast(node['child'])}"
    if tag in _BINARY_LEFT_RIGHT_TAGS:
        left = _render_sentence_ast(node["left"])
        right = _render_sentence_ast(node["right"])
        return f"({left} {_TAG_TO_OPERATOR[tag]} {right})"
    if tag in _BINARY_GUARD_EVENT_TAGS:
        guard = _render_sentence_ast(node["guard"])
        event = _render_sentence_ast(node["event"])
        return f"({guard} {_TAG_TO_OPERATOR[tag]} {event})"
    raise ValueError(
        f"sentence-translation-fixtures.jsonl uses tag {tag!r}, which this renderer has no "
        "mapping for -- either the fixture grew a new source-sentence constructor, or this "
        "renderer's tag tables are out of date; fail loudly rather than skip the row"
    )


def _load_fixture_rows() -> List[Dict[str, Any]]:
    """Read the fixture live from the resolved BimodalLogic checkout -- never a copy mirrored
    into this repository, per this module's docstring: one source of truth cannot drift."""
    if _CHECKOUT_PATH is None:
        return []
    fixture_path = _CHECKOUT_PATH / FIXTURE_RELATIVE_PATH
    rows: List[Dict[str, Any]] = []
    with open(fixture_path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rows.append(json.loads(line))
    return rows


_FIXTURE_ROWS = _load_fixture_rows()

# Read at implementation time from the live fixture (26 rows, 4 kinds) -- not trusted from the
# plan or research report. A truncated or partially-read fixture must fail loudly, not pass
# vacuously; see TestFixtureIntegrity below for the mechanical form of this confirmation.
_EXPECTED_ROW_COUNT = 26
_EXPECTED_KINDS = {"primitive", "defined", "asymmetry", "nesting"}


class TestFixtureIntegrity:
    """The row-count and kind-coverage assertions are the mechanical form of "the fixture was
    read correctly, in full" -- a partially-read or silently-truncated fixture must fail one of
    these, not pass the per-row loop vacuously over fewer rows than it should have seen."""

    def test_row_count_matches_expected(self):
        assert len(_FIXTURE_ROWS) == _EXPECTED_ROW_COUNT, (
            f"expected {_EXPECTED_ROW_COUNT} fixture rows, got {len(_FIXTURE_ROWS)} -- a "
            "truncated or partially-read fixture must fail loudly, not pass vacuously"
        )

    def test_every_kind_is_represented(self):
        seen_kinds = {row["kind"] for row in _FIXTURE_ROWS}
        assert seen_kinds == _EXPECTED_KINDS, (
            f"expected every kind in {_EXPECTED_KINDS!r}, saw {seen_kinds!r}"
        )


_ROW_IDS = [row["surface"] for row in _FIXTURE_ROWS] if _FIXTURE_ROWS else []


class TestSentenceTranslationAgreesWithFixture:
    """Per fixture row: render `sentence` to this repository's infix syntax, build the real
    type-updated `Sentence` through `Syntax`, `translate` it, `to_json` the result, and assert
    **dict equality** against the row's `formula` field -- never a serialized-string comparison
    (see module docstring's "Comparison is on parsed JSON, never on bytes")."""

    @pytest.mark.parametrize("row", _FIXTURE_ROWS, ids=_ROW_IDS)
    def test_translation_matches_fixture_formula(self, row):
        infix = _render_sentence_ast(row["sentence"])
        sentence = _sentence(infix)
        actual = to_json(translate(sentence))
        assert actual == row["formula"], (
            f"{row['surface']!r} (kind={row['kind']!r}): this repository's translation "
            f"disagrees with the fixture's expected formula.\n"
            f"  rendered infix: {infix!r}\n"
            f"  actual:   {actual}\n"
            f"  expected: {row['formula']}"
        )


class TestFlaggedOperatorsAreNotTheObviousShape:
    """`BimodalTools/README.md`'s "Three rows are not the obvious operator" section: this
    repository's `\\rightarrow` routes through `¬A ∨ B` (not a bare `imp(p, q)`), and its
    existential tenses are `¬G¬`/`¬H¬` (not a bare `someFuture`/`somePast` primitive read). This
    task names two of the three (`\\rightarrow`, `\\future`) as individually diagnosable
    assertions; the third (`\\past`) is still covered -- along with these two again -- by the
    general per-row loop above, which asserts every fixture row including all three."""

    def test_rightarrow_is_disjunction_of_negation_not_bare_imp(self):
        p, q = Atom("p"), Atom("q")
        sentence = _sentence("(p \\rightarrow q)")
        actual = translate(sentence)
        # A vee B := (not A) -> B (formula.py's translate rule for \vee), applied to
        # (not p) vee q -- the ConditionalOperator's own derived_definition.
        expected = Imp(Imp(Imp(p, Bot()), Bot()), q)
        assert actual == expected
        wrong_bare_imp = Imp(p, q)  # the obvious-but-wrong bare-implication guess
        assert actual != wrong_bare_imp

    def test_future_is_negated_universal_not_bare_until_primitive(self):
        p = Atom("p")
        sentence = _sentence("\\future p")
        actual = translate(sentence)
        top = Imp(Bot(), Bot())
        # \future p := \neg \Future \neg p (DefFutureOperator.derived_definition), and
        # \Future A := \neg (top \Until \neg A) (formula.py's translate rule for \Future).
        expected = Imp(Imp(Untl(guard=top, event=Imp(Imp(p, Bot()), Bot())), Bot()), Bot())
        assert actual == expected
        wrong_bare_until = Untl(guard=top, event=p)  # the obvious-but-wrong bare "eventually" guess
        assert actual != wrong_bare_until


class TestUnknownTagFailsLoudly:
    """An unmapped source-sentence tag must raise, never be silently skipped -- see
    `_render_sentence_ast`'s docstring."""

    def test_unmapped_tag_raises_value_error(self):
        with pytest.raises(ValueError, match="no mapping"):
            _render_sentence_ast({"tag": "not_a_real_tag"})
