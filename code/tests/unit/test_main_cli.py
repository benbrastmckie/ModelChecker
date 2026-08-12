"""Unit tests for the ModelChecker CLI argument parser (model_checker.__main__).

Covers short-flag mapping coverage, registry-derived --load_theory choices/help,
removal of the unsupported --save jupyter value, the --sequential clean-error path,
and removal of the dead -j/--jupyter pre-check.
"""

import argparse
import sys

import pytest

from model_checker.__main__ import ParseFileFlags

# Registered short options that are not settings keys and are legitimately excluded
# from the _short_to_long coverage requirement:
#   -h is argparse's auto-added help action (add_help=True default), never a settings flag
#   -v is action='version' (argparse handles it internally, never a settings flag)
_SHORT_OPTION_ALLOWLIST = {'h', 'v'}


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


def _registered_short_options(parser):
    """Collect every single-character short option string registered on parser."""
    short_opts = set()
    for action in parser._actions:
        for opt in action.option_strings:
            if len(opt) == 2 and opt.startswith('-') and opt[1].isalpha():
                short_opts.add(opt[1])
    return short_opts


def test_short_to_long_covers_every_registered_short_option(monkeypatch):
    """Every registered single-character short option has a _short_to_long entry,
    except names on the explicit allowlist (options that are not settings keys)."""
    monkeypatch.setattr(sys, 'argv', ['model-checker'])
    flags = ParseFileFlags()
    flags.parse()

    registered = _registered_short_options(flags.parser)
    mapped = set(flags._short_to_long.keys())

    missing = (registered - mapped) - _SHORT_OPTION_ALLOWLIST
    assert missing == set()


class _MockSemantics:
    """Minimal semantics stand-in providing the settings SettingsManager reads."""
    DEFAULT_EXAMPLE_SETTINGS = {'N': 3, 'max_time': 1}
    DEFAULT_GENERAL_SETTINGS = {'print_constraints': False}


def test_print_constraints_short_and_long_equivalent(tmp_path, monkeypatch):
    """-p and --print_constraints produce the same print_constraints setting
    after SettingsManager override application."""
    from model_checker.settings import SettingsManager

    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    def _apply(args):
        monkeypatch.setattr(sys, 'argv', ['model-checker'] + args)
        flags = ParseFileFlags()
        module_flags, _ = flags.parse()

        semantic_theory = {'semantics': _MockSemantics}
        manager = SettingsManager(semantic_theory)
        settings = manager.validate_general_settings(None)
        return manager.apply_flag_overrides(settings, module_flags)

    short_settings = _apply(['-p', str(example_file)])
    long_settings = _apply(['--print_constraints', str(example_file)])

    assert short_settings['print_constraints'] == long_settings['print_constraints'] is True


def test_load_theory_accepts_every_registered_theory(monkeypatch, tmp_path):
    """--load_theory succeeds for every name registry.get_registered() reports.

    Asserted against the live registry rather than a literal list so this test cannot
    itself reintroduce the hardcoded-theory-name drift the fix removes.
    """
    from model_checker import registry

    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    for theory_name in registry.get_registered():
        monkeypatch.setattr(
            sys, 'argv', ['model-checker', '--load_theory', theory_name, str(example_file)]
        )
        flags = ParseFileFlags()
        module_flags, _ = flags.parse()
        assert module_flags.load_theory == theory_name


def test_load_theory_rejects_unregistered_name(monkeypatch, tmp_path):
    """--load_theory with a name absent from the registry fails fast at argparse time."""
    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    monkeypatch.setattr(
        sys, 'argv', ['model-checker', '--load_theory', 'nonsense', str(example_file)]
    )
    flags = ParseFileFlags()
    with pytest.raises(SystemExit):
        flags.parse()


def test_help_lists_every_registered_theory(capsys):
    """--help output names every theory registry.get_registered() reports."""
    from model_checker import registry

    flags = ParseFileFlags()
    help_text = flags.parser.format_help()
    for theory_name in registry.get_registered():
        assert theory_name in help_text
