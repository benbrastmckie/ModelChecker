"""cp1252 regression coverage for bimodal's aligned world-history print paths.

`BimodalStructure.print_evaluation` writes a double-arrow (`⟹`) plus a
Unicode subscript duration; `print_world_histories` (via `_create_world_line`)
writes the same double-arrow inside a columnar-aligned layout;
`print_world_histories_vertical` writes a down-arrow (`↓`) between rows.
All three raise `UnicodeEncodeError` on a `cp1252`-constrained stream today.

Every cp1252 assertion here is expected to FAIL against unmodified source --
this file is landed RED before Phase 3 routes these call sites through
`model_checker.utils.glyphs`.
"""

from unittest.mock import Mock

import pytest

from model_checker.theory_lib.bimodal.semantic.model import BimodalStructure
from model_checker.utils import make_encoding_test_streams, read_encoding_test_stream


def _make_structure(world_histories, main_world=0, main_time=0, z3_main_world_state=1):
    """Build a BimodalStructure instance without running the solver pipeline.

    Mirrors the `ImpositionModelStructure.__new__` pattern already used in
    `theory_lib/imposition/tests/unit/test_model.py`: bypass `__init__` and
    set exactly the attributes the print methods under test read.
    """
    structure = BimodalStructure.__new__(BimodalStructure)
    structure.z3_model = Mock()  # Truthy sentinel -- print paths only check "is None".
    structure.z3_model_status = True
    structure.world_histories = world_histories
    structure.main_world = main_world
    structure.main_time = main_time
    structure.z3_main_world_state = z3_main_world_state
    return structure


class TestPrintEvaluationEncoding:
    """cp1252 regression coverage for `print_evaluation`'s double-arrow + subscript."""

    def test_cp1252_stream_does_not_raise(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}})
        stream = make_encoding_test_streams()["cp1252"]
        structure.print_evaluation(output=stream)

    def test_cp1252_stream_uses_ascii_double_arrow(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}})
        stream = make_encoding_test_streams()["cp1252"]
        structure.print_evaluation(output=stream)
        output = read_encoding_test_stream(stream)
        assert "=>" in output
        assert "⟹" not in output

    def test_utf8_stream_uses_unicode_double_arrow(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}})
        stream = make_encoding_test_streams()["utf8"]
        structure.print_evaluation(output=stream)
        output = read_encoding_test_stream(stream)
        assert "⟹" in output

    def test_stringio_stream_uses_unicode_double_arrow(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}})
        stream = make_encoding_test_streams()["stringio"]
        structure.print_evaluation(output=stream)
        output = read_encoding_test_stream(stream)
        assert "⟹" in output


class TestPrintWorldHistoriesEncoding:
    """cp1252 regression coverage for the columnar `print_world_histories`."""

    def test_cp1252_stream_does_not_raise(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}, 1: {0: "s2", 1: "s3"}})
        stream = make_encoding_test_streams()["cp1252"]
        structure.print_world_histories(output=stream)

    def test_cp1252_stream_uses_ascii_double_arrow(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}, 1: {0: "s2", 1: "s3"}})
        stream = make_encoding_test_streams()["cp1252"]
        structure.print_world_histories(output=stream)
        output = read_encoding_test_stream(stream)
        assert "=>" in output
        assert "⟹" not in output

    def test_utf8_stream_uses_unicode_double_arrow(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}, 1: {0: "s2", 1: "s3"}})
        stream = make_encoding_test_streams()["utf8"]
        structure.print_world_histories(output=stream)
        output = read_encoding_test_stream(stream)
        assert "⟹" in output

    def test_stringio_stream_uses_unicode_double_arrow(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}, 1: {0: "s2", 1: "s3"}})
        stream = make_encoding_test_streams()["stringio"]
        structure.print_world_histories(output=stream)
        output = read_encoding_test_stream(stream)
        assert "⟹" in output


class TestPrintWorldHistoriesVerticalEncoding:
    """cp1252 regression coverage for `print_world_histories_vertical`'s down-arrow."""

    def test_cp1252_stream_does_not_raise(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}, 1: {0: "s2", 1: "s3"}})
        stream = make_encoding_test_streams()["cp1252"]
        structure.print_world_histories_vertical(output=stream)

    def test_cp1252_stream_uses_ascii_down_arrow(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}, 1: {0: "s2", 1: "s3"}})
        stream = make_encoding_test_streams()["cp1252"]
        structure.print_world_histories_vertical(output=stream)
        output = read_encoding_test_stream(stream)
        assert "v" in output
        assert "↓" not in output

    def test_utf8_stream_uses_unicode_down_arrow(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}, 1: {0: "s2", 1: "s3"}})
        stream = make_encoding_test_streams()["utf8"]
        structure.print_world_histories_vertical(output=stream)
        output = read_encoding_test_stream(stream)
        assert "↓" in output

    def test_stringio_stream_uses_unicode_down_arrow(self):
        structure = _make_structure({0: {0: "s0", 1: "s1"}, 1: {0: "s2", 1: "s3"}})
        stream = make_encoding_test_streams()["stringio"]
        structure.print_world_histories_vertical(output=stream)
        output = read_encoding_test_stream(stream)
        assert "↓" in output
