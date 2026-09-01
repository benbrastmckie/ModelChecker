"""cp1252 regression coverage for imposition's relation printing.

`ImpositionModelStructure.print_imposition` writes a `→_` (U+2192 + `_`)
arrow between an imposed state, the world it is imposed on, and the outcome.
This is the second print site the original traceback never named -- found
only by the repo-wide non-ASCII sweep.

A real (small, N=3) countermodel is built directly through `BuildExample`
using `IM_TR_0` (`theory_lib/imposition/examples.py`, no premises/
conclusions): the base `imposition` relation is a frame-level primitive
extracted for every triple regardless of whether the imposition operator
appears in a formula, so this reliably populates
`z3_imposition_relations` without needing a slower, operator-driven example.

Every cp1252 assertion here is expected to FAIL against unmodified source --
this file is landed RED before Phase 3 routes this call site through
`model_checker.utils.glyphs`.
"""

from types import SimpleNamespace
from unittest.mock import Mock

import pytest

from model_checker.builder.example import BuildExample
from model_checker.theory_lib.imposition import Proposition
from model_checker.theory_lib.imposition.operators import imposition_operators
from model_checker.theory_lib.imposition.semantic.core import ImpositionSemantics
from model_checker.theory_lib.imposition.semantic.model import ImpositionModelStructure
from model_checker.utils import make_encoding_test_streams, read_encoding_test_stream

SEMANTIC_THEORY = {
    "semantics": ImpositionSemantics,
    "proposition": Proposition,
    "model": ImpositionModelStructure,
    "operators": imposition_operators,
}

GENERAL_SETTINGS = {
    'N': 3,
    'contingent': False,
    'non_null': False,
    'non_empty': False,
    'disjoint': False,
    'print_constraints': False,
    'save_output': False,
    'print_impossible': True,
    'print_z3': False,
    'max_time': 10,
}

# IM_TR_0 from `theory_lib/imposition/examples.py`: no premises/conclusions,
# just the frame constraints -- fast, and `imposition` is a base relation so
# `z3_imposition_relations` is populated regardless.
EXAMPLE_CASE = [
    [],
    [],
    {
        'N': 3, 'contingent': False, 'non_null': False, 'non_empty': False,
        'disjoint': False, 'max_time': 10, 'iterate': 1,
    },
]


@pytest.fixture(scope="module")
def solved_example():
    """Build the IM_TR_0 countermodel once and share it across assertions."""
    mock_module = Mock()
    mock_module.semantic_theories = {"imposition": SEMANTIC_THEORY}
    mock_module.general_settings = GENERAL_SETTINGS
    mock_module.raw_general_settings = GENERAL_SETTINGS
    mock_module.module_flags = SimpleNamespace(
        contingent=False, disjoint=False, non_empty=False, non_null=False,
        print_constraints=False, save_output=False, print_impossible=False,
        print_z3=False, maximize=False,
    )
    example = BuildExample(mock_module, SEMANTIC_THEORY, EXAMPLE_CASE)
    assert example.model_structure.z3_model_status, "IM_TR_0 must find a countermodel"
    assert example.model_structure.z3_imposition_relations, (
        "IM_TR_0 must populate at least one imposition relation triple"
    )
    return example


class TestPrintImpositionEncoding:
    """cp1252 regression coverage for `print_imposition`'s arrow."""

    def test_cp1252_stream_does_not_raise(self, solved_example):
        stream = make_encoding_test_streams()["cp1252"]
        solved_example.model_structure.print_imposition(output=stream)

    def test_cp1252_stream_uses_ascii_arrow(self, solved_example):
        stream = make_encoding_test_streams()["cp1252"]
        solved_example.model_structure.print_imposition(output=stream)
        output = read_encoding_test_stream(stream)
        assert "->_" in output
        assert "→_" not in output

    def test_utf8_stream_uses_unicode_arrow(self, solved_example):
        stream = make_encoding_test_streams()["utf8"]
        solved_example.model_structure.print_imposition(output=stream)
        output = read_encoding_test_stream(stream)
        assert "→_" in output

    def test_stringio_stream_uses_unicode_arrow(self, solved_example):
        stream = make_encoding_test_streams()["stringio"]
        solved_example.model_structure.print_imposition(output=stream)
        output = read_encoding_test_stream(stream)
        assert "→_" in output

    def test_cp1252_via_print_all_does_not_raise(self, solved_example):
        """Reproduce the real crash surface: the full `print_all` path."""
        stream = make_encoding_test_streams()["cp1252"]
        solved_example.model_structure.print_all(
            GENERAL_SETTINGS, "IM_TR_0", "imposition", output=stream
        )
