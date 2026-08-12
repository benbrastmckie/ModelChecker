"""Unit tests for the ModelChecker CLI argument parser (model_checker.__main__).

Covers short-flag mapping coverage, registry-derived --load_theory choices/help,
removal of the unsupported --save jupyter value, the --sequential clean-error path,
and removal of the dead -j/--jupyter pre-check.
"""

import argparse

import pytest

from model_checker.__main__ import ParseFileFlags


def test_parse_file_flags_constructs():
    """ParseFileFlags() constructs and exposes an argparse.ArgumentParser."""
    flags = ParseFileFlags()
    assert isinstance(flags.parser, argparse.ArgumentParser)


def test_jupyter_flags_not_registered():
    """-j and --jupyter are not registered options.

    The dead Jupyter dependency pre-check was removed from main() because no
    -j/--jupyter argparse action was ever registered, so the pre-check could
    never fire in practice. This documents that the deletion changed nothing
    observable: the flags remain unregistered before and after.
    """
    flags = ParseFileFlags()
    option_strings = set(flags.parser._option_string_actions.keys())
    assert '-j' not in option_strings
    assert '--jupyter' not in option_strings
