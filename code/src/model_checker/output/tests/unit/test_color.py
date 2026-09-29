"""Tests for `model_checker.output.color.use_colors`, the single color-gating predicate
every printer consults before emitting ANSI escapes.

Precedence (no-color.org, clig.dev): `NO_COLOR` set and non-empty disables color
unconditionally; otherwise `FORCE_COLOR` set and non-empty enables it (even into a pipe or
`StringIO`); otherwise `TERM=dumb` disables it; otherwise the stream's own `isatty()` decides,
and a stream with no `isatty` at all is never colored.
"""

import io

import pytest

from model_checker.output import use_colors as reexported_use_colors
from model_checker.output.color import use_colors


class _TTY:
    def isatty(self):
        return True


class _NoIsatty:
    pass


@pytest.fixture(autouse=True)
def _clean_env(monkeypatch):
    monkeypatch.delenv("NO_COLOR", raising=False)
    monkeypatch.delenv("FORCE_COLOR", raising=False)
    monkeypatch.setenv("TERM", "xterm-256color")


def test_stringio_is_not_colored():
    assert use_colors(io.StringIO()) is False


def test_tty_stream_is_colored():
    assert use_colors(_TTY()) is True


def test_no_color_disables_a_tty(monkeypatch):
    monkeypatch.setenv("NO_COLOR", "1")
    assert use_colors(_TTY()) is False


def test_empty_no_color_is_ignored(monkeypatch):
    """no-color.org: only a present *and non-empty* `NO_COLOR` counts."""
    monkeypatch.setenv("NO_COLOR", "")
    assert use_colors(_TTY()) is True


def test_term_dumb_disables_a_tty(monkeypatch):
    monkeypatch.setenv("TERM", "dumb")
    assert use_colors(_TTY()) is False


def test_force_color_enables_a_stringio(monkeypatch):
    monkeypatch.setenv("FORCE_COLOR", "1")
    assert use_colors(io.StringIO()) is True


def test_stream_without_isatty_is_not_colored():
    assert use_colors(_NoIsatty()) is False
    assert use_colors(None) is False


def test_no_color_beats_force_color(monkeypatch):
    monkeypatch.setenv("NO_COLOR", "1")
    monkeypatch.setenv("FORCE_COLOR", "1")
    assert use_colors(_TTY()) is False
    assert use_colors(io.StringIO()) is False


def test_isatty_raising_is_treated_as_not_a_tty():
    class _Broken:
        def isatty(self):
            raise ValueError("I/O operation on closed file")

    assert use_colors(_Broken()) is False


def test_reexported_from_output_package():
    assert reexported_use_colors is use_colors
