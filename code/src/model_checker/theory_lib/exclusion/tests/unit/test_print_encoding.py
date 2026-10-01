"""cp1252 regression coverage for exclusion's witness-function difference printing.

`WitnessStructure.print_witness_functions` (reached via `print_all` ->
`print_negation`) writes a `→` (U+2192) arrow between an input state and its
witness-function output. This is one of the two print sites the original
traceback never named -- found only by the repo-wide non-ASCII sweep -- so
this file exists to pin that finding against regression.

A real (small, N=3) exclusion negation model is built directly through
`BuildExample`, rather than mocked, because `print_witness_functions`
evaluates real Z3 witness-predicate function declarations
(`z3.substitute(func(arg), (arg, state))`) that are not easily faked without
a real Z3 model.

These cp1252 assertions were landed RED, before this call site was routed
through `model_checker.utils.glyphs`. That routing has since landed, so they
are GREEN now and are ordinary regression coverage -- a failure here is a real
regression, not an expected-red placeholder.
"""

from types import SimpleNamespace
from unittest.mock import Mock

import pytest

from model_checker.builder.example import BuildExample
from model_checker.theory_lib.exclusion import (
    WitnessSemantics, WitnessProposition, WitnessStructure, witness_operators,
)
from model_checker.utils import make_encoding_test_streams, read_encoding_test_stream

SEMANTIC_THEORY = {
    "semantics": WitnessSemantics,
    "proposition": WitnessProposition,
    "model": WitnessStructure,
    "operators": witness_operators,
}

GENERAL_SETTINGS = {
    'N': 3,
    'contingent': True,
    'disjoint': False,
    'non_empty': True,
    'non_null': True,
    'possible': False,
    'fusion_closure': False,
    'print_constraints': False,
    'save_output': False,
    'print_impossible': True,
    'print_z3': False,
    'max_time': 10,
}

# EX_CM_4 from `theory_lib/exclusion/examples.py`: `\neg A` forces a witness
# predicate (`_h`/`_y`) for exclusion negation into the model, which is what
# `print_witness_functions` renders.
EXAMPLE_CASE = [
    ['\\neg A'],
    ['A'],
    {
        'N': 3, 'contingent': True, 'non_empty': True, 'non_null': True,
        'possible': False, 'disjoint': False, 'fusion_closure': False,
        'max_time': 10, 'iterate': 1,
    },
]


@pytest.fixture(scope="module")
def solved_example():
    """Build the EX_CM_4 countermodel once and share it across assertions.

    `print_witness_functions` only reads from the already-solved model
    (`self.z3_model`, `self.all_states`, ...) -- it does not mutate solver
    state -- so a module-scoped fixture is safe to reuse across the RED/GREEN
    variants below.
    """
    mock_module = Mock()
    mock_module.semantic_theories = {"exclusion": SEMANTIC_THEORY}
    mock_module.general_settings = GENERAL_SETTINGS
    mock_module.raw_general_settings = GENERAL_SETTINGS
    mock_module.module_flags = SimpleNamespace(
        contingent=False, disjoint=False, non_empty=False, non_null=False,
        print_constraints=False, save_output=False, print_impossible=False,
        print_z3=False, maximize=False,
    )
    example = BuildExample(mock_module, SEMANTIC_THEORY, EXAMPLE_CASE)
    assert example.model_structure.z3_model_status, "EX_CM_4 must find a countermodel"
    return example


class TestWitnessFunctionsEncoding:
    """cp1252 regression coverage for `print_witness_functions`'s arrow."""

    def test_cp1252_stream_does_not_raise(self, solved_example):
        stream = make_encoding_test_streams()["cp1252"]
        solved_example.model_structure.print_witness_functions(output=stream)

    def test_cp1252_stream_uses_ascii_arrow(self, solved_example):
        stream = make_encoding_test_streams()["cp1252"]
        solved_example.model_structure.print_witness_functions(output=stream)
        output = read_encoding_test_stream(stream)
        assert "->" in output
        assert "→" not in output

    def test_utf8_stream_uses_unicode_arrow(self, solved_example):
        stream = make_encoding_test_streams()["utf8"]
        solved_example.model_structure.print_witness_functions(output=stream)
        output = read_encoding_test_stream(stream)
        assert "→" in output

    def test_stringio_stream_uses_unicode_arrow(self, solved_example):
        stream = make_encoding_test_streams()["stringio"]
        solved_example.model_structure.print_witness_functions(output=stream)
        output = read_encoding_test_stream(stream)
        assert "→" in output

    def test_cp1252_via_print_all_does_not_raise(self, solved_example):
        """Reproduce the real crash surface: the full `print_all` path."""
        stream = make_encoding_test_streams()["cp1252"]
        solved_example.model_structure.print_all(
            GENERAL_SETTINGS, "EX_CM_4", "exclusion", output=stream
        )


class TestEvaluationBlockHasMatchingVisualWeight:
    """`print_evaluation` gains the same visual weight as bimodal's own multi-line
    evaluation-point block: a heading plus an indented, fully-colored value line -- the
    structurally identical change to logos's own (see the plan's Decision 4)."""

    def test_block_is_a_heading_plus_one_indented_value_line(self, solved_example):
        import io

        stream = io.StringIO()
        solved_example.model_structure.print_evaluation(output=stream)
        lines = [line for line in stream.getvalue().splitlines() if line.strip()]
        assert lines[0] == "Evaluation world:"
        assert lines[1].startswith("  ")

    def test_both_lines_are_blue_on_a_color_stream(self, solved_example, monkeypatch):
        import io

        monkeypatch.setenv("FORCE_COLOR", "1")
        monkeypatch.delenv("NO_COLOR", raising=False)
        stream = io.StringIO()
        solved_example.model_structure.print_evaluation(output=stream)
        lines = [line for line in stream.getvalue().splitlines() if line.strip()]
        assert len(lines) == 2
        assert all("\033[34m" in line for line in lines)
        assert all(line.rstrip().endswith("\033[0m") for line in lines)

    def test_block_lines_stay_within_80_columns(self, solved_example):
        import io

        stream = io.StringIO()
        solved_example.model_structure.print_evaluation(output=stream)
        assert max((len(line) for line in stream.getvalue().splitlines()), default=0) <= 80

    def test_plain_rendering_names_the_world_with_no_escapes(self, solved_example):
        import io

        stream = io.StringIO()
        solved_example.model_structure.print_evaluation(output=stream)
        out = stream.getvalue()
        assert "\033[" not in out
        assert "Evaluation world:" in out
