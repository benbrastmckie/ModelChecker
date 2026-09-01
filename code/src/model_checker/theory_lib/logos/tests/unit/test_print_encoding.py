"""cp1252 regression coverage for logos's printed-output path.

The original research report (`specs/182_.../reports/01_windows-unicode-
encode-error.md`, §2) recorded that `theory_lib/logos/semantic/model.py` has
**zero** non-ASCII print hits, and concluded logos crashes only via the
shared `models/structure.py` difference-reporting path. That claim is
correct only for a *literal-character grep* -- it misses a defect this file
pins: `LogosModelStructure.print_states` and `print_evaluation` embed the
result of `model_checker.utils.bitvector.bitvec_to_substates`, which
produces the literal `□` (U+25A1, "null state") glyph at *runtime* for
bitvector 0, not in logos's own source text. A grep over `model.py`'s
source therefore never finds it, but a cp1252-constrained stream still
raises `UnicodeEncodeError` the moment `print_states` renders the null
state -- which happens in virtually every model, since state 0 is always
part of `all_states`.

This file corrects that inventory gap: logos is NOT clean, it has its own
print-path defect, just one invisible to a literal-character sweep. It is
landed RED before `bitvec_to_substates` is made encoding-aware in Phase 3.
"""

from types import SimpleNamespace
from unittest.mock import Mock

import pytest

from model_checker.builder.example import BuildExample
from model_checker.theory_lib.logos import (
    LogosModelStructure, LogosOperatorRegistry, LogosProposition, LogosSemantics,
)
from model_checker.utils import make_encoding_test_streams, read_encoding_test_stream

_registry = LogosOperatorRegistry()
_registry.load_subtheories(['extensional'])

SEMANTIC_THEORY = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": _registry.get_operators(),
}

GENERAL_SETTINGS = {
    'N': 2,
    'contingent': False,
    'disjoint': False,
    'non_empty': True,
    'non_null': True,
    'print_constraints': False,
    'save_output': False,
    'print_impossible': True,
    'print_z3': False,
    'max_time': 5,
}

# Trivial frame-constraints-only countermodel (no premises/conclusions) --
# fast, and `all_states` always includes the null state 0, so `print_states`
# always renders `□`.
EXAMPLE_CASE = [
    [],
    [],
    {
        'N': 2, 'contingent': False, 'disjoint': False, 'non_empty': True,
        'non_null': True, 'max_time': 5, 'iterate': 1,
    },
]


@pytest.fixture(scope="module")
def solved_example():
    """Build a trivial logos countermodel once and share it across assertions."""
    mock_module = Mock()
    mock_module.semantic_theories = {"logos": SEMANTIC_THEORY}
    mock_module.general_settings = GENERAL_SETTINGS
    mock_module.raw_general_settings = GENERAL_SETTINGS
    mock_module.module_flags = SimpleNamespace(
        contingent=False, disjoint=False, non_empty=False, non_null=False,
        print_constraints=False, save_output=False, print_impossible=False,
        print_z3=False, maximize=False,
    )
    example = BuildExample(mock_module, SEMANTIC_THEORY, EXAMPLE_CASE)
    assert example.model_structure.z3_model_status, "Trivial logos example must find a model"
    return example


class TestLogosStructureLocalPrintSitesAreClean:
    """Pins the report's finding for logos's own *literal* arrow/subscript glyphs.

    `models/structure.py`'s shared difference-reporting path (covered by
    `models/tests/unit/test_structure_print_encoding.py`) is the only
    literal-arrow print site logos participates in; this class exists so a
    future logos-local `→`/`⟹`/`↓` literal is caught by a grep-based CI
    check, per the plan's Phase 2 requirement, without re-asserting the
    (now-corrected) claim that logos is *entirely* free of print-path risk.
    """

    def test_no_literal_arrow_glyphs_in_logos_model_source(self):
        import inspect

        from model_checker.theory_lib.logos.semantic import model as logos_model_module

        source = inspect.getsource(logos_model_module)
        for forbidden in ("⟹", "→", "↓"):
            assert forbidden not in source, (
                f"Found literal {forbidden!r} in theory_lib/logos/semantic/model.py -- "
                "route it through model_checker.utils.glyphs.glyph()"
            )


class TestPrintStatesEncoding:
    """cp1252 regression coverage for `print_states`'s null-state glyph.

    This is the gap the report's inventory missed: `bitvec_to_substates`
    renders `□` for the null state at *runtime*, invisible to a
    literal-character grep over `model.py`'s source.
    """

    def test_cp1252_stream_does_not_raise(self, solved_example):
        stream = make_encoding_test_streams()["cp1252"]
        solved_example.model_structure.print_states(output=stream)

    def test_cp1252_stream_uses_ascii_null_state(self, solved_example):
        stream = make_encoding_test_streams()["cp1252"]
        solved_example.model_structure.print_states(output=stream)
        output = read_encoding_test_stream(stream)
        assert "_" in output
        assert "□" not in output

    def test_utf8_stream_uses_unicode_null_state(self, solved_example):
        stream = make_encoding_test_streams()["utf8"]
        solved_example.model_structure.print_states(output=stream)
        output = read_encoding_test_stream(stream)
        assert "□" in output

    def test_stringio_stream_uses_unicode_null_state(self, solved_example):
        stream = make_encoding_test_streams()["stringio"]
        solved_example.model_structure.print_states(output=stream)
        output = read_encoding_test_stream(stream)
        assert "□" in output

    def test_cp1252_via_print_all_does_not_raise(self, solved_example):
        """Reproduce the real crash surface: the full `print_all` path."""
        stream = make_encoding_test_streams()["cp1252"]
        solved_example.model_structure.print_all(
            GENERAL_SETTINGS, "TRIVIAL", "logos", output=stream
        )
