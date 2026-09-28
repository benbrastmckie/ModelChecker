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
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Optional

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
from model_checker.theory_lib.bimodal.tests._lean_check import (
    resolve_bimodal_logic_path,
    resolve_lake,
)

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


# ---------------------------------------------------------------------------
# Optional live differential leg: the committed fixture against the live
# `lake exe translate_sentence` binary, invoked directly (not through `lake exe`, mirroring
# `_lean_check.py`'s direct-invocation rationale -- see checker.py's `_invoke` docstring).
# ---------------------------------------------------------------------------

_DIFFERENTIAL_PROBE_TIMEOUT_SECONDS = 30
_DIFFERENTIAL_INVOKE_TIMEOUT_SECONDS = 30


def _resolve_translate_sentence_binary() -> Optional[Path]:
    """The built `translate_sentence` binary inside the resolved checkout, or `None` if there is
    no checkout or the binary has not been built there."""
    if _CHECKOUT_PATH is None:
        return None
    candidate = _CHECKOUT_PATH / ".lake" / "build" / "bin" / "translate_sentence"
    return candidate if candidate.is_file() else None


def _invoke_translate_sentence(
    payload: Dict[str, Any], timeout: float
) -> Optional[Dict[str, Any]]:
    """Invoke the built `translate_sentence` binary directly (never through `lake exe`, which
    pays an incremental build-check overhead on every call -- see `semantic/checker.py`'s
    `_invoke` docstring for the identical rationale this mirrors) on one source-sentence JSON
    payload. Returns the parsed output object, or `None` on timeout, a non-zero exit, a missing
    binary, or an unparseable response -- the caller decides how to report that (an
    environment-absence skip at probe time, or a loud assertion failure at differential-check
    time; never silently folded together)."""
    if _TRANSLATE_SENTENCE_BINARY is None:
        return None
    sent = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
    try:
        result = subprocess.run(
            [str(_TRANSLATE_SENTENCE_BINARY)],
            input=sent,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except (subprocess.TimeoutExpired, OSError):
        return None
    if result.returncode != 0:
        return None
    line = result.stdout.strip().splitlines()[-1] if result.stdout.strip() else ""
    try:
        return json.loads(line)
    except (json.JSONDecodeError, IndexError):
        return None


def _probe_translate_sentence() -> Optional[str]:
    """Bounded probe of the built binary, mirroring `_lean_check.py`'s probe-then-run idiom: a
    binary that never answers within the timeout is an environment-absence condition, safe to
    skip. This probe does NOT classify a wrong answer as a skip condition -- only "did it answer
    at all" -- keeping the environment-absence vocabulary strictly separate from the
    protocol-disagreement vocabulary the differential assertions below enforce (a binary that
    answers with the wrong formula must fail loudly, never skip)."""
    live = _invoke_translate_sentence(
        {"tag": "atom", "name": "p"}, _DIFFERENTIAL_PROBE_TIMEOUT_SECONDS
    )
    if live is None:
        return (
            "`translate_sentence` did not respond within "
            f"{_DIFFERENTIAL_PROBE_TIMEOUT_SECONDS}s, or failed to run"
        )
    return None


_LAKE = resolve_lake()
_TRANSLATE_SENTENCE_BINARY = _resolve_translate_sentence_binary()

_DIFFERENTIAL_SKIP_REASON: Optional[str] = None
if _CHECKOUT_PATH is None:
    _DIFFERENTIAL_SKIP_REASON = _CHECKOUT_ABSENT_SKIP_REASON
elif _LAKE is None:
    _DIFFERENTIAL_SKIP_REASON = "`lake` not found on PATH"
elif _TRANSLATE_SENTENCE_BINARY is None:
    _DIFFERENTIAL_SKIP_REASON = (
        "`translate_sentence` binary not built at "
        f"{_CHECKOUT_PATH / '.lake' / 'build' / 'bin' / 'translate_sentence'} "
        "(run `lake build translate_sentence` in the BimodalLogic checkout)"
    )
else:
    _DIFFERENTIAL_SKIP_REASON = _probe_translate_sentence()


def _select_representative_rows(rows: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """At minimum one row per `kind`, plus the `\\top` row and the two flagged-operator rows --
    never one subprocess invocation per row over the whole fixture (this leg's own risk
    mitigation: a live differential costs one subprocess per row checked, so this selection stays
    small and representative rather than exhaustive; the fixture-only leg above is already
    exhaustive)."""
    chosen: Dict[str, Dict[str, Any]] = {}
    seen_kinds: set = set()
    for row in rows:
        if row["kind"] not in seen_kinds:
            seen_kinds.add(row["kind"])
            chosen[row["surface"]] = row
    for surface in ("\\top", "\\rightarrow p q", "\\future p"):
        for row in rows:
            if row["surface"] == surface:
                chosen[surface] = row
                break
    return list(chosen.values())


_REPRESENTATIVE_ROWS = _select_representative_rows(_FIXTURE_ROWS) if _FIXTURE_ROWS else []
_REPRESENTATIVE_ROW_IDS = [row["surface"] for row in _REPRESENTATIVE_ROWS]


def _assert_translate_sentence_matches_fixture(row: Dict[str, Any]) -> None:
    live = _invoke_translate_sentence(row["sentence"], _DIFFERENTIAL_INVOKE_TIMEOUT_SECONDS)
    assert live is not None, (
        f"`translate_sentence` did not respond in time for {row['surface']!r} despite passing "
        "this module's own availability probe"
    )
    assert live == row["formula"], (
        f"{row['surface']!r}: the live `lake exe translate_sentence` binary disagrees with the "
        "committed fixture's expected formula -- the committed fixture may be stale.\n"
        f"  live:    {live}\n"
        f"  fixture: {row['formula']}"
    )


@pytest.mark.skipif(_DIFFERENTIAL_SKIP_REASON is not None, reason=_DIFFERENTIAL_SKIP_REASON or "")
class TestLiveDifferentialAgainstTranslateSentenceBinary:
    """The committed fixture corpus, checked against what the live `translate_sentence` binary
    emits right now -- so fixture staleness is detectable rather than assumed away. This leg is
    entirely separate from, and does not gate, `TestSentenceTranslationAgreesWithFixture` above
    (the fixture-only leg): with the checkout present but `lake`/the binary unavailable, this
    class skips while the fixture-only leg keeps running unaffected."""

    @pytest.mark.parametrize("row", _REPRESENTATIVE_ROWS, ids=_REPRESENTATIVE_ROW_IDS)
    def test_live_binary_agrees_with_committed_fixture(self, row):
        _assert_translate_sentence_matches_fixture(row)

    def test_deliberately_corrupted_expected_value_fails_not_skips(self):
        """Sanity check that the differential assertion has teeth: a deliberately corrupted
        expected `formula` value must raise `AssertionError`, never silently skip or pass --
        proving the live comparison is load-bearing, not vacuous."""
        row = _REPRESENTATIVE_ROWS[0]
        corrupted_row = dict(
            row, formula={"tag": "atom", "name": "definitely-not-the-real-answer"}
        )
        with pytest.raises(AssertionError):
            _assert_translate_sentence_matches_fixture(corrupted_row)
