"""cp1252 regression coverage for `models/structure.py`'s difference-printing arrows.

These tests reproduce the exact `UnicodeEncodeError` a Windows-piped console
script hits when `ModelDefaults._print_sentence_letter_differences`,
`_print_semantic_function_differences`, and `_print_model_structure_differences`
write the `→` (U+2192) arrow to a `cp1252`-constrained stream. All four
theories share this code path via `models/structure.py`, so this is the
single place logos (which has no theory-local non-ASCII print site) is
exercised at all.

Every cp1252 assertion here is expected to FAIL against unmodified source --
this file is landed RED before the corresponding call sites are routed
through `model_checker.utils.glyphs.glyph`.
"""

from unittest.mock import Mock

import pytest

from model_checker.models.structure import ModelDefaults
from model_checker.utils import make_encoding_test_streams, read_encoding_test_stream


@pytest.fixture
def mock_model():
    """Create a mock ModelDefaults with representative differences."""
    model = Mock(spec=ModelDefaults)
    model.model_differences = {
        'sentence_letters': {
            'A': {'old': True, 'new': False},
        },
        'semantic_functions': {
            'verify': {
                '(0, A)': {'old': True, 'new': False}
            }
        },
        'model_structure': {
            'worlds': {'old': 2, 'new': 3}
        }
    }
    return model


class TestSentenceLetterDifferencesEncoding:
    """cp1252 regression coverage for `_print_sentence_letter_differences`."""

    def test_cp1252_stream_does_not_raise(self, mock_model):
        stream = make_encoding_test_streams()["cp1252"]
        ModelDefaults._print_sentence_letter_differences(mock_model, stream)

    def test_cp1252_stream_uses_ascii_arrow(self, mock_model):
        stream = make_encoding_test_streams()["cp1252"]
        ModelDefaults._print_sentence_letter_differences(mock_model, stream)
        output = read_encoding_test_stream(stream)
        assert "->" in output
        assert "→" not in output

    def test_utf8_stream_uses_unicode_arrow(self, mock_model):
        stream = make_encoding_test_streams()["utf8"]
        ModelDefaults._print_sentence_letter_differences(mock_model, stream)
        output = read_encoding_test_stream(stream)
        assert "→" in output

    def test_stringio_stream_uses_unicode_arrow(self, mock_model):
        stream = make_encoding_test_streams()["stringio"]
        ModelDefaults._print_sentence_letter_differences(mock_model, stream)
        output = read_encoding_test_stream(stream)
        assert "→" in output


class TestSemanticFunctionDifferencesEncoding:
    """cp1252 regression coverage for `_print_semantic_function_differences`."""

    def test_cp1252_stream_does_not_raise(self, mock_model):
        stream = make_encoding_test_streams()["cp1252"]
        ModelDefaults._print_semantic_function_differences(mock_model, stream)

    def test_cp1252_stream_uses_ascii_arrow(self, mock_model):
        stream = make_encoding_test_streams()["cp1252"]
        ModelDefaults._print_semantic_function_differences(mock_model, stream)
        output = read_encoding_test_stream(stream)
        assert "->" in output
        assert "→" not in output

    def test_utf8_stream_uses_unicode_arrow(self, mock_model):
        stream = make_encoding_test_streams()["utf8"]
        ModelDefaults._print_semantic_function_differences(mock_model, stream)
        output = read_encoding_test_stream(stream)
        assert "→" in output

    def test_stringio_stream_uses_unicode_arrow(self, mock_model):
        stream = make_encoding_test_streams()["stringio"]
        ModelDefaults._print_semantic_function_differences(mock_model, stream)
        output = read_encoding_test_stream(stream)
        assert "→" in output


class TestModelStructureDifferencesEncoding:
    """cp1252 regression coverage for `_print_model_structure_differences`."""

    def test_cp1252_stream_does_not_raise(self, mock_model):
        stream = make_encoding_test_streams()["cp1252"]
        ModelDefaults._print_model_structure_differences(mock_model, stream)

    def test_cp1252_stream_uses_ascii_arrow(self, mock_model):
        stream = make_encoding_test_streams()["cp1252"]
        ModelDefaults._print_model_structure_differences(mock_model, stream)
        output = read_encoding_test_stream(stream)
        assert "->" in output
        assert "→" not in output

    def test_utf8_stream_uses_unicode_arrow(self, mock_model):
        stream = make_encoding_test_streams()["utf8"]
        ModelDefaults._print_model_structure_differences(mock_model, stream)
        output = read_encoding_test_stream(stream)
        assert "→" in output

    def test_stringio_stream_uses_unicode_arrow(self, mock_model):
        stream = make_encoding_test_streams()["stringio"]
        ModelDefaults._print_model_structure_differences(mock_model, stream)
        output = read_encoding_test_stream(stream)
        assert "→" in output
