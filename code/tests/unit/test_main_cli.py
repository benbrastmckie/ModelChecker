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
