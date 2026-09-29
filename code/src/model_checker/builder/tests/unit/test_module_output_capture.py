"""`BuildModule._capture_model_output` captures into an `io.StringIO`, which
`output.color.use_colors` treats as non-TTY: the captured text carries no ANSI escapes by
default (so `ANSIToMarkdown`'s input is unchanged from before the shared predicate existed),
and `FORCE_COLOR=1` is the one sanctioned way to get colored capture."""

from unittest.mock import Mock

import pytest

from model_checker.builder.module import BuildModule
from model_checker.output.color import use_colors


class _ColorAwareExample:
    """Stands in for a `BuildExample`: prints red text only when the stream wants color."""

    def print_model(self, example_name=None, theory_name=None, output=None):
        if use_colors(output):
            print(f"\033[31m{example_name}\033[0m", file=output)
        else:
            print(example_name, file=output)


@pytest.fixture(autouse=True)
def _clean_env(monkeypatch):
    monkeypatch.delenv("NO_COLOR", raising=False)
    monkeypatch.delenv("FORCE_COLOR", raising=False)
    monkeypatch.setenv("TERM", "xterm")


def test_captured_output_carries_no_escapes_by_default():
    raw, converted = BuildModule._capture_model_output(Mock(), _ColorAwareExample(), "EX", "logos")
    assert "\033[" not in raw
    assert raw.strip() == "EX"
    assert converted.strip() == "EX"


def test_force_color_opts_the_capture_into_escapes(monkeypatch):
    monkeypatch.setenv("FORCE_COLOR", "1")
    raw, converted = BuildModule._capture_model_output(Mock(), _ColorAwareExample(), "EX", "logos")
    assert "\033[31m" in raw
    assert converted.strip() == "**EX**"  # ANSIToMarkdown: red -> bold
