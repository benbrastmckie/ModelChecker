"""Unit tests for the stream-encoding-aware glyph fallback helper.

These tests pin the contract that print-path glyph resolution keys off the
target stream's `.encoding` attribute: a stream that cannot encode the
preferred Unicode glyph (e.g. a cp1252-constrained Windows pipe) gets an
ASCII substitute instead of raising `UnicodeEncodeError`.
"""

import io

import pytest

from model_checker.utils.glyphs import glyph, stream_can_encode, to_subscript


class _FakeStream:
    """Minimal stand-in for a stream exposing only `.encoding`."""

    def __init__(self, encoding):
        self.encoding = encoding


class TestStreamCanEncode:
    """Tests for the `stream_can_encode` predicate."""

    def test_none_encoding_is_encodable(self):
        """A `None` encoding (e.g. absent `.encoding`) is treated as capable."""
        assert stream_can_encode(None, "⟹") is True

    def test_utf8_can_encode_unicode_glyph(self):
        assert stream_can_encode("utf-8", "⟹") is True

    def test_cp1252_cannot_encode_double_arrow(self):
        assert stream_can_encode("cp1252", "⟹") is False

    def test_unknown_codec_name_returns_false_not_raise(self):
        """An unknown/bogus codec name must not raise -- treated as unsafe."""
        assert stream_can_encode("totally-bogus-codec-xyz", "⟹") is False


class TestGlyphResolution:
    """Tests for `glyph(name, output)`."""

    def test_cp1252_stream_yields_ascii_double_arrow(self):
        stream = _FakeStream("cp1252")
        assert glyph("DOUBLE_ARROW", stream) == "=>"

    def test_utf8_stream_yields_unicode_double_arrow(self):
        stream = _FakeStream("utf-8")
        assert glyph("DOUBLE_ARROW", stream) == "⟹"

    def test_stringio_yields_unicode(self):
        """`io.StringIO`'s `.encoding` is `None` (it never encodes)."""
        stream = io.StringIO()
        assert stream.encoding is None
        assert glyph("DOUBLE_ARROW", stream) == "⟹"

    def test_bogus_encoding_yields_ascii_not_raise(self):
        stream = _FakeStream("totally-bogus-codec-xyz")
        assert glyph("DOUBLE_ARROW", stream) == "=>"

    def test_none_stream_yields_unicode(self):
        assert glyph("ARROW", None) == "→"

    def test_cp1252_arrow(self):
        stream = _FakeStream("cp1252")
        assert glyph("ARROW", stream) == "->"

    def test_cp1252_down_arrow(self):
        stream = _FakeStream("cp1252")
        assert glyph("DOWN_ARROW", stream) == "v"

    def test_utf8_down_arrow(self):
        stream = _FakeStream("utf-8")
        assert glyph("DOWN_ARROW", stream) == "↓"

    def test_cp1252_block_glyphs(self):
        stream = _FakeStream("cp1252")
        assert glyph("BLOCK_FULL", stream) == "#"
        assert glyph("BLOCK_LIGHT", stream) == "-"

    def test_utf8_block_glyphs(self):
        stream = _FakeStream("utf-8")
        assert glyph("BLOCK_FULL", stream) == "█"
        assert glyph("BLOCK_LIGHT", stream) == "░"

    def test_cp1252_null_state(self):
        """`□` (null state, from `bitvec_to_substates`) falls back to ASCII."""
        stream = _FakeStream("cp1252")
        assert glyph("NULL_STATE", stream) == "_"

    def test_utf8_null_state(self):
        stream = _FakeStream("utf-8")
        assert glyph("NULL_STATE", stream) == "□"

    def test_cp1252_empty_set(self):
        """`∅` (bimodal's world-state fallback) falls back to ASCII."""
        stream = _FakeStream("cp1252")
        assert glyph("EMPTY_SET", stream) == "{}"

    def test_utf8_empty_set(self):
        stream = _FakeStream("utf-8")
        assert glyph("EMPTY_SET", stream) == "∅"

    def test_real_cp1252_textiowrapper(self):
        """The canonical Windows-pipe reproduction: a real cp1252 TextIOWrapper."""
        buf = io.BytesIO()
        stream = io.TextIOWrapper(buf, encoding="cp1252", newline="")
        assert glyph("DOUBLE_ARROW", stream) == "=>"
        # Confirm the ASCII substitute round-trips through the actual codec
        # without raising -- this is the crash the whole task exists to fix.
        stream.write(glyph("DOUBLE_ARROW", stream))
        stream.flush()

    def test_real_utf8_textiowrapper(self):
        buf = io.BytesIO()
        stream = io.TextIOWrapper(buf, encoding="utf-8", newline="")
        assert glyph("DOUBLE_ARROW", stream) == "⟹"


class TestToSubscript:
    """Tests for `to_subscript(n, output)`."""

    def test_utf8_single_digit(self):
        stream = _FakeStream("utf-8")
        assert to_subscript(1, stream) == "₁"

    def test_cp1252_single_digit_falls_back_to_ascii(self):
        stream = _FakeStream("cp1252")
        assert to_subscript(1, stream) == "1"

    def test_cp1252_two_digit_duration_falls_back_to_ascii(self):
        stream = _FakeStream("cp1252")
        assert to_subscript(12, stream) == "12"

    def test_utf8_two_digit_duration(self):
        stream = _FakeStream("utf-8")
        assert to_subscript(12, stream) == "₁₂"

    def test_negative_duration_ascii(self):
        stream = _FakeStream("cp1252")
        assert to_subscript(-3, stream) == "-3"

    def test_width_neutral_across_encodings(self):
        """Both forms are exactly one character per digit -- width-neutral."""
        utf8_stream = _FakeStream("utf-8")
        cp1252_stream = _FakeStream("cp1252")
        assert len(to_subscript(12, utf8_stream)) == len(to_subscript(12, cp1252_stream)) == 2

    def test_none_stream_yields_unicode_subscript(self):
        assert to_subscript(5, None) == "₅"

    def test_stringio_yields_unicode_subscript(self):
        stream = io.StringIO()
        assert to_subscript(5, stream) == "₅"


class TestFormulaGlyphs:
    """The bimodal formula renderer's glyph set (`semantic/render.py`): each entry has a
    Unicode form for a utf-8 stream and a readable ASCII form for a cp1252 pipe."""

    CASES = [
        ("BOX", "□", "[]"),
        ("LOZENGE", "◇", "<>"),
        ("AND", "∧", "&"),
        ("OR", "∨", "|"),
        ("BOT", "⊥", "_|_"),
        ("TOP", "⊤", "T"),
    ]

    @pytest.mark.parametrize("name,unicode_form,ascii_form", CASES)
    def test_cp1252_yields_ascii(self, name, unicode_form, ascii_form):
        buf = io.BytesIO()
        stream = io.TextIOWrapper(buf, encoding="cp1252", newline="")
        assert glyph(name, stream) == ascii_form
        stream.write(glyph(name, stream))
        stream.flush()

    @pytest.mark.parametrize("name,unicode_form,ascii_form", CASES)
    def test_utf8_yields_unicode(self, name, unicode_form, ascii_form):
        buf = io.BytesIO()
        stream = io.TextIOWrapper(buf, encoding="utf-8", newline="")
        assert glyph(name, stream) == unicode_form
        stream.write(glyph(name, stream))
        stream.flush()

    def test_neg_survives_cp1252_and_falls_back_on_ascii(self):
        """`¬` (U+00AC) is a cp1252 code point, so the fallback only fires on a codec
        that genuinely cannot encode it."""
        cp1252 = io.TextIOWrapper(io.BytesIO(), encoding="cp1252", newline="")
        assert glyph("NEG", cp1252) == "¬"
        cp1252.write(glyph("NEG", cp1252))
        cp1252.flush()
        ascii_stream = io.TextIOWrapper(io.BytesIO(), encoding="ascii", newline="")
        assert glyph("NEG", ascii_stream) == "~"

    def test_ellipsis_survives_cp1252_and_falls_back_on_ascii(self):
        """`…` (U+2026, the bimodal history rows' periodic-segment marker) is cp1252 0x85, so
        a cp1252 pipe keeps it; only a codec that genuinely cannot encode it (`ascii`) gets
        the three-dot fallback. Pinned explicitly so a future "fix" cannot silently
        ASCII-ify it on Windows pipes."""
        cp1252 = io.TextIOWrapper(io.BytesIO(), encoding="cp1252", newline="")
        assert glyph("ELLIPSIS", cp1252) == "…"
        cp1252.write(glyph("ELLIPSIS", cp1252))
        cp1252.flush()
        ascii_stream = io.TextIOWrapper(io.BytesIO(), encoding="ascii", newline="")
        assert glyph("ELLIPSIS", ascii_stream) == "..."
        ascii_stream.write(glyph("ELLIPSIS", ascii_stream))
        ascii_stream.flush()
        utf8 = io.TextIOWrapper(io.BytesIO(), encoding="utf-8", newline="")
        assert glyph("ELLIPSIS", utf8) == "…"

    def test_omega_is_retired(self):
        """The `(back)^ω | mid | (fwd)^ω` one-liner is gone; no dead glyph entry survives it."""
        with pytest.raises(KeyError):
            glyph("OMEGA", _FakeStream("utf-8"))

    def test_implication_reuses_arrow(self):
        """`→`/`->` is already `ARROW`; the renderer reuses it rather than adding `IMP`."""
        assert glyph("ARROW", _FakeStream("cp1252")) == "->"
        assert glyph("ARROW", _FakeStream("utf-8")) == "→"
