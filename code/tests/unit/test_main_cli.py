"""Unit tests for the ModelChecker CLI argument parser (model_checker.__main__).

Covers short-flag mapping coverage, registry-derived --load_theory choices/help,
removal of the unsupported --save jupyter value, the --sequential clean-error path,
and removal of the dead -j/--jupyter pre-check.
"""

import argparse
import sys

import pytest

from model_checker.__main__ import ParseFileFlags
from tests.utils.helpers import run_cli_command

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


def test_save_jupyter_rejected(monkeypatch, tmp_path):
    """--save jupyter is rejected at argparse time (no Jupyter writer exists)."""
    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    # file_path precedes --save so argparse's nargs='*' greedy consumption doesn't
    # swallow the positional file_path as a --save value.
    monkeypatch.setattr(sys, 'argv', ['model-checker', str(example_file), '--save', 'jupyter'])
    flags = ParseFileFlags()
    with pytest.raises(SystemExit):
        flags.parse()


def test_bare_save_yields_markdown_and_json(monkeypatch, tmp_path):
    """Bare --save (no args) still yields formats == ['markdown', 'json']."""
    from model_checker.output.config import create_output_config

    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    monkeypatch.setattr(sys, 'argv', ['model-checker', str(example_file), '--save'])
    flags = ParseFileFlags()
    module_flags, _ = flags.parse()

    config = create_output_config(module_flags)
    assert config.formats == ['markdown', 'json']


def test_project_name_flag_registered_with_short_alias():
    """--project_name/-y is registered and mapped in _short_to_long."""
    flags = ParseFileFlags()
    option_strings = set(flags.parser._option_string_actions.keys())
    assert '--project_name' in option_strings
    assert '-y' in option_strings


def test_project_name_absent_defaults_to_none(monkeypatch, tmp_path):
    """Without -y/--project_name, module_flags.project_name is None (opt-in only)."""
    from model_checker import registry

    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    monkeypatch.setattr(
        sys, 'argv',
        ['model-checker', '--load_theory', registry.get_registered()[0], str(example_file)],
    )
    flags = ParseFileFlags()
    module_flags, _ = flags.parse()
    assert module_flags.project_name is None


def test_non_interactive_project_generation_no_prompt(monkeypatch, tmp_path):
    """`-l <theory> -y <name>` generates a project with no stdin read (EOFError-safe).

    Uses the CLI subprocess with stdin closed (input='') to prove main() never
    calls input() on this path -- the RED-defining scenario for non-interactive
    project generation.
    """
    from model_checker import registry

    theory_name = registry.get_registered()[0]
    project_name = "cli_noninteractive_test"

    result = run_cli_command(
        ['--load_theory', theory_name, '--project_name', project_name, str(tmp_path)],
        check=False,
        input='',
    )

    assert result.returncode == 0, (result.stdout, result.stderr)
    assert 'EOFError' not in (result.stderr or '')
    created = tmp_path / f"project_{project_name}"
    assert created.exists() and created.is_dir()


def test_non_interactive_honors_destination_directory(tmp_path):
    """The positional file_path argument is honored as the destination directory,
    not silently discarded, when combined with --load_theory --project_name."""
    from model_checker import registry

    theory_name = registry.get_registered()[0]
    project_name = "cli_dest_test"
    dest_dir = tmp_path / "chosen_destination"
    dest_dir.mkdir()

    result = run_cli_command(
        ['--load_theory', theory_name, '--project_name', project_name, str(dest_dir)],
        check=False,
        input='',
    )

    assert result.returncode == 0, (result.stdout, result.stderr)
    created = dest_dir / f"project_{project_name}"
    assert created.exists() and created.is_dir()
    # Confirm it was NOT created in the cwd instead (destination honored, not discarded).
    assert not (tmp_path / f"project_{project_name}").exists()


def test_non_interactive_missing_name_exits_nonzero_with_clear_message():
    """`-l <theory> -y` (flag present, name omitted) exits non-zero with a clear,
    actionable message rather than raising or silently prompting."""
    from model_checker import registry

    theory_name = registry.get_registered()[0]

    result = run_cli_command(
        ['--load_theory', theory_name, '--project_name'],
        check=False,
        input='',
    )

    assert result.returncode != 0
    combined_output = (result.stdout or '') + (result.stderr or '')
    assert 'Traceback' not in combined_output
    assert 'project_name' in combined_output or '-y' in combined_output


def test_interactive_path_unchanged_when_flag_absent(tmp_path):
    """--load_theory without --project_name still reaches the interactive
    ask_generate() path (answering 'n' to the first prompt exits cleanly)."""
    from model_checker import registry

    theory_name = registry.get_registered()[0]

    result = run_cli_command(
        ['--load_theory', theory_name],
        check=False,
        input='n\n',
        cwd=tmp_path,
    )

    assert result.returncode == 0, (result.stdout, result.stderr)
    assert 'Would you like to generate a new' in (result.stdout or '')


def test_sequential_flag_exits_cleanly_without_traceback(tmp_path):
    """--sequential exits non-zero with a one-line error, no Python traceback.

    NotImplementedError raised by builder/module.py's
    _initialize_output_management is caught at the BuildModule(...) call site in
    main() and converted into a clean "Error: ..." message plus sys.exit(1).
    """
    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    result = run_cli_command(['--sequential', str(example_file)], check=False)

    assert result.returncode != 0
    combined_output = (result.stdout or '') + (result.stderr or '')
    assert 'Traceback' not in combined_output
