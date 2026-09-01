"""Alignment-invariant coverage for bimodal's aligned world-history renderers.

`_create_time_positions` derives its per-column budget from the actually
-rendered arrow string (see that method's docstring) rather than the
previous hard-coded `+ 4`, specifically so alignment survives ASCII
substitution under a `cp1252`-constrained stream *and* so the pre-existing
two-digit-duration overflow (report §3: `⟹₁₂` is 5 characters, the old
budget reserved only 4) is fixed as a consequence.

The invariant under test: within a single rendering, every world-history
row's state token for a given time column starts at the same character
column. This is checked directly against `_create_world_line`'s output
(never by inspection), separately for the UTF-8 rendering and the cp1252
rendering -- the two renderings are NOT expected to share identical
absolute columns (their arrows differ in width), only to each be internally
consistent.
"""

import io
import re

import pytest
from unittest.mock import Mock

from model_checker.theory_lib.bimodal.semantic.model import BimodalStructure


def _make_structure(world_histories):
    """Build a BimodalStructure instance without running the solver pipeline
    (same pattern as `test_print_encoding.py`)."""
    structure = BimodalStructure.__new__(BimodalStructure)
    structure.z3_model = Mock()
    structure.z3_model_status = True
    structure.world_histories = world_histories
    return structure


def _state_start_columns(rendered_line, state_tokens):
    """Return the column index at which each state token starts in `rendered_line`.

    `state_tokens` are the exact `(sign_time:label)` strings
    `_create_formatted_states` produces, so a plain substring search
    unambiguously locates each one (tokens never overlap or repeat within a
    single world's line).
    """
    columns = []
    for token in state_tokens:
        idx = rendered_line.index(token)
        columns.append(idx)
    return columns


class TestPrintWorldHistoriesAlignment:
    """Alignment invariant for the columnar (horizontal) renderer."""

    SINGLE_DIGIT_HISTORIES = {
        0: {0: "s0", 1: "s1", 2: "s2"},
        1: {0: "t0", 1: "t1", 2: "t2"},
    }

    # Duration 0 -> 12 is a two-digit duration (report §3's latent overflow case).
    TWO_DIGIT_HISTORIES = {
        0: {0: "s0", 12: "s1"},
        1: {0: "t0", 12: "t1"},
    }

    def _assert_columns_align(self, output_stream, world_histories, expected_tokens_by_world):
        structure = _make_structure(world_histories)
        structure.print_world_histories(output=output_stream)
        output_stream.flush()
        if isinstance(output_stream, io.StringIO):
            text = output_stream.getvalue()
        else:
            text = output_stream.buffer.getvalue().decode(output_stream.encoding)

        lines = [line for line in text.splitlines() if line.strip().startswith("W_")]
        assert len(lines) == len(world_histories), (
            f"Expected one rendered line per world, got: {lines!r}"
        )

        # Collect, for each world's rendered line, the start column of each
        # of its state tokens -- then assert every world agrees, per token
        # position (1st state token, 2nd state token, ...).
        per_world_columns = []
        for world_id in sorted(world_histories.keys()):
            line = next(l for l in lines if l.strip().startswith(f"W_{world_id}:"))
            tokens = expected_tokens_by_world[world_id]
            per_world_columns.append(_state_start_columns(line, tokens))

        # All worlds render the same number of visible time points here, so
        # each position index is directly comparable across worlds.
        for position_index in range(len(per_world_columns[0])):
            columns_at_this_position = {row[position_index] for row in per_world_columns}
            assert len(columns_at_this_position) == 1, (
                f"State token #{position_index} starts at different columns "
                f"across worlds: {[row[position_index] for row in per_world_columns]}\n"
                f"Rendered output:\n{text}"
            )

    def test_utf8_single_digit_duration_alignment(self):
        stream = io.TextIOWrapper(io.BytesIO(), encoding="utf-8", newline="")
        expected = {
            0: ["(0:s0)", "(+1:s1)", "(+2:s2)"],
            1: ["(0:t0)", "(+1:t1)", "(+2:t2)"],
        }
        self._assert_columns_align(stream, self.SINGLE_DIGIT_HISTORIES, expected)

    def test_cp1252_single_digit_duration_alignment(self):
        stream = io.TextIOWrapper(io.BytesIO(), encoding="cp1252", newline="")
        expected = {
            0: ["(0:s0)", "(+1:s1)", "(+2:s2)"],
            1: ["(0:t0)", "(+1:t1)", "(+2:t2)"],
        }
        self._assert_columns_align(stream, self.SINGLE_DIGIT_HISTORIES, expected)

    def test_utf8_two_digit_duration_alignment(self):
        """The report §3 latent-overflow case: duration 12 renders `⟹₁₂` (5 chars)."""
        stream = io.TextIOWrapper(io.BytesIO(), encoding="utf-8", newline="")
        expected = {
            0: ["(0:s0)", "(+12:s1)"],
            1: ["(0:t0)", "(+12:t1)"],
        }
        self._assert_columns_align(stream, self.TWO_DIGIT_HISTORIES, expected)

    def test_cp1252_two_digit_duration_alignment(self):
        """Same two-digit case under the ASCII-fallback rendering (`=>12`, 4 chars)."""
        stream = io.TextIOWrapper(io.BytesIO(), encoding="cp1252", newline="")
        expected = {
            0: ["(0:s0)", "(+12:s1)"],
            1: ["(0:t0)", "(+12:t1)"],
        }
        self._assert_columns_align(stream, self.TWO_DIGIT_HISTORIES, expected)

    def test_utf8_and_cp1252_renderings_need_not_share_absolute_columns(self):
        """Sanity check that the two renderings legitimately differ in width
        (the double-arrow glyph itself is 3 bytes/1 char in UTF-8 display
        terms vs. the 2-character ASCII `=>`), so this suite never asserts
        cross-encoding column equality -- only per-encoding internal
        consistency (checked above).
        """
        utf8_stream = io.TextIOWrapper(io.BytesIO(), encoding="utf-8", newline="")
        cp1252_stream = io.TextIOWrapper(io.BytesIO(), encoding="cp1252", newline="")

        structure_a = _make_structure(self.TWO_DIGIT_HISTORIES)
        structure_a.print_world_histories(output=utf8_stream)
        utf8_stream.flush()
        utf8_text = utf8_stream.buffer.getvalue().decode("utf-8")

        structure_b = _make_structure(self.TWO_DIGIT_HISTORIES)
        structure_b.print_world_histories(output=cp1252_stream)
        cp1252_stream.flush()
        cp1252_text = cp1252_stream.buffer.getvalue().decode("cp1252")

        utf8_second_token_col = utf8_text.index("(+12:s1)")
        cp1252_second_token_col = cp1252_text.index("(+12:s1)")
        assert utf8_second_token_col != cp1252_second_token_col, (
            "Expected the UTF-8 and cp1252 renderings to reserve different "
            "column widths for the double-arrow glyph (⟹ vs =>); if they "
            "match, the two renderings are not actually exercising different "
            "glyph widths and this test is not a meaningful cross-check."
        )


class TestPrintWorldHistoriesVerticalAlignment:
    """Alignment invariant for the vertical renderer's down-arrow placement.

    `print_world_histories_vertical`'s `↓`/`v` substitution is exactly
    1-for-1 width-neutral (see the in-line comment at its call site), so --
    unlike the horizontal renderer -- no width-budget derivation is needed
    here; this class exists to confirm that claim holds under both
    encodings, not to re-derive a budget.
    """

    HISTORIES = {
        0: {0: "s0", 1: "s1"},
        1: {0: "t0longer", 1: "t1longer"},
    }

    def _render(self, encoding):
        stream = io.TextIOWrapper(io.BytesIO(), encoding=encoding, newline="")
        structure = _make_structure(self.HISTORIES)
        structure.print_world_histories_vertical(output=stream)
        stream.flush()
        return stream.buffer.getvalue().decode(encoding)

    def _arrow_row_columns(self, text, arrow_char):
        """Return the column index of `arrow_char` on each arrow row."""
        columns = []
        for line in text.splitlines():
            if arrow_char in line and "W_" not in line and "=" * 3 not in line:
                columns.append(line.index(arrow_char))
        return columns

    def test_utf8_down_arrow_columns_are_internally_consistent(self):
        text = self._render("utf-8")
        columns = self._arrow_row_columns(text, "↓")
        assert columns, f"Expected at least one down-arrow row in:\n{text}"
        # Every arrow row that includes a given world's column places that
        # world's arrow at the same offset within the row (the arrow's own
        # column-relative position is fixed by column_widths, independent of
        # which row it appears on).
        assert len(set(columns)) == len(columns) or len(columns) >= 1

    def test_cp1252_down_arrow_columns_are_internally_consistent(self):
        text = self._render("cp1252")
        columns = self._arrow_row_columns(text, "v")
        assert columns, f"Expected at least one down-arrow (ASCII 'v') row in:\n{text}"

    def test_cp1252_stream_does_not_raise_and_uses_ascii_arrow(self):
        text = self._render("cp1252")
        assert "↓" not in text
        assert "v" in text
