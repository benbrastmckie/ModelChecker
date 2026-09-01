"""cp1252 regression coverage for the animated progress bar's block glyphs.

`output/progress/display.py`'s `TerminalDisplay.enabled` is hardcoded `True`
("Always enabled for testing"; the `stream.isatty()` gate is commented out),
and `output/progress/animated.py`'s `TimeBasedProgress._generate_bar`
unconditionally builds `█`/`░` block characters -- only the *color* codes
are isatty-gated, not the glyphs themselves. `TerminalDisplay.update()`
writes these glyphs to `self.stream` exactly as unguarded as the model
-output print paths this task otherwise fixes; a Windows user running any
multi-model iteration would hit the identical `UnicodeEncodeError`
immediately after the crash this task fixes is declared closed, which is
why this progress-bar sweep is in scope (see the plan's "Decision:
output/progress is IN scope" section) even though `TerminalDisplay.enabled`
being always-`True` was not itself part of the original traceback.

Re-enabling the commented-out `stream.isatty()` gate is explicitly OUT of
scope for this task -- see `code/docs/core/TESTING_GUIDE.md`'s
output-encoding section for the recorded boundary. This file fixes glyph
selection only.
"""

import io

import pytest

from model_checker.output.progress.animated import TimeBasedProgress
from model_checker.output.progress.display import TerminalDisplay
from model_checker.utils import make_encoding_test_streams, read_encoding_test_stream


def _make_progress_bar(stream):
    display = TerminalDisplay(stream=stream)
    return TimeBasedProgress(
        timeout=60.0,
        model_number=1,
        total_models=2,
        display=display,
    )


class TestGenerateBarEncoding:
    """cp1252 regression coverage for `_generate_bar`'s block glyphs."""

    def test_cp1252_stream_does_not_raise(self):
        stream = make_encoding_test_streams()["cp1252"]
        bar = _make_progress_bar(stream)
        rendered = bar._generate_bar(0.5)
        stream.write(rendered)
        stream.flush()

    def test_cp1252_stream_uses_ascii_blocks(self):
        stream = make_encoding_test_streams()["cp1252"]
        bar = _make_progress_bar(stream)
        rendered = bar._generate_bar(0.5)
        assert "#" in rendered
        assert "-" in rendered
        assert "█" not in rendered
        assert "░" not in rendered

    def test_utf8_stream_uses_unicode_blocks(self):
        stream = make_encoding_test_streams()["utf8"]
        bar = _make_progress_bar(stream)
        rendered = bar._generate_bar(0.5)
        assert "█" in rendered
        assert "░" in rendered

    def test_stringio_stream_uses_unicode_blocks(self):
        stream = make_encoding_test_streams()["stringio"]
        bar = _make_progress_bar(stream)
        rendered = bar._generate_bar(0.5)
        assert "█" in rendered
        assert "░" in rendered

    def test_bar_width_unaffected_by_substitution(self):
        """Both substitutes are one character, so BAR_WIDTH arithmetic holds."""
        cp1252_bar = _make_progress_bar(make_encoding_test_streams()["cp1252"])
        utf8_bar = _make_progress_bar(make_encoding_test_streams()["utf8"])
        cp1252_rendered = cp1252_bar._generate_bar(0.5)
        utf8_rendered = utf8_bar._generate_bar(0.5)
        # Strip the surrounding brackets; both renderings should have exactly
        # BAR_WIDTH glyph characters (no color codes present -- these streams
        # are never sys.__stdout__/isatty, so _supports_color() is False).
        assert len(cp1252_rendered) == len(utf8_rendered) == TimeBasedProgress.BAR_WIDTH + 2

    def test_cp1252_via_terminal_display_update_does_not_raise(self):
        """Reproduce the real crash surface: TerminalDisplay.update() writing to stream."""
        stream = make_encoding_test_streams()["cp1252"]
        bar = _make_progress_bar(stream)
        message = f"Finding non-isomorphic models: {bar._generate_bar(0.3)} 1/2"
        bar.display.update(message)
        output = read_encoding_test_stream(stream)
        assert "#" in output
        assert "█" not in output
