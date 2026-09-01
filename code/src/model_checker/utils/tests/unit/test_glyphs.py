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
