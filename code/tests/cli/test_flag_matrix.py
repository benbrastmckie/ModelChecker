"""Flag matrix: every registered `model-checker` flag exercised through
`python -m model_checker`, fast, without building a venv.

Console-script (not `python -m`) behavior lives in `code/tests/packaging/`.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

from model_checker.__main__ import ParseFileFlags
from model_checker.solver.registry import detect_cvc5

from tests.utils.helpers import run_cli_command


# ---------------------------------------------------------------------------------------------
# Programmatic flag-coverage assertion
# ---------------------------------------------------------------------------------------------

# Every flag dispatch-tested below by a dedicated test in this file (argparse `dest` names).
_COVERED_FLAGS = {
    'version',
    'contingent', 'non_null', 'non_empty', 'disjoint',
    'print_constraints', 'print_z3', 'print_impossible',
    'align_vertically',
    'save',
    'maximize',
    'z3', 'cvc5',
    'upgrade',
    'sequential',
    'load_theory',
    'project_name',
}
# No exclusions: -l/--load_theory dispatches to BuildProject.ask_generate(), which blocks on
# input() -- but run_cli_command's existing `input=` parameter pipes answers through the
# subprocess's stdin, closing the matrix with no source change. See
# test_load_theory_generates_project_non_interactively below.
_EXCLUDED_FLAGS = set()


def test_every_registered_flag_is_covered_or_excluded():
    """Enumerate the parser's own registered actions -- never a hand-transcribed list -- and
    confirm every non-builtin flag is either dispatch-tested in this file or on the explicit,
    commented exclusion list above."""
    parser = ParseFileFlags().parser
    registered = {
        action.dest for action in parser._actions
        if action.option_strings and action.dest not in ('help',)
    }

    accounted = _COVERED_FLAGS | _EXCLUDED_FLAGS
    assert registered == accounted, (
        f"Registered flags not accounted for: {registered - accounted}; "
        f"accounted flags no longer registered: {accounted - registered}"
    )
    # No flag is both covered and excluded.
    assert _COVERED_FLAGS.isdisjoint(_EXCLUDED_FLAGS)


# ---------------------------------------------------------------------------------------------
# --version / -v
# ---------------------------------------------------------------------------------------------


@pytest.mark.parametrize("flag", ["--version", "-v"])
def test_version(flag):
    result = run_cli_command([flag], check=False)
    assert result.returncode == 0
    assert result.stdout.strip(), "expected non-empty stdout"
    assert 'model-checker' in result.stdout.lower()


# ---------------------------------------------------------------------------------------------
# --help / -h
# ---------------------------------------------------------------------------------------------


@pytest.mark.parametrize("flag", ["--help", "-h"])
def test_help_lists_every_registered_long_flag(flag):
    """--help's output names every long flag string the parser actually registers, so a newly
    added flag missing from help text is caught rather than relying on a hand-copied list."""
    result = run_cli_command([flag], check=False)
    assert result.returncode == 0

    parser = ParseFileFlags().parser
    long_flags = [
        opt for action in parser._actions for opt in action.option_strings
        if opt.startswith('--')
    ]
    assert long_flags, "sanity: parser must register at least one long flag"
    for long_flag in long_flags:
        assert long_flag in result.stdout, f"{long_flag} missing from --help output"


def _help_for(dest):
    """The registered help string for an argparse `dest`."""
    parser = ParseFileFlags().parser
    for action in parser._actions:
        if action.dest == dest:
            return action.help
    raise AssertionError(f"no action registered for dest {dest!r}")


def test_non_null_help_describes_the_null_state_constraint():
    """`non_null` emits `Not(verify(0, letter))` / `Not(falsify(0, letter))` -- it bars the null
    state from verifying or falsifying (logos `semantic/proposition.py`
    `get_non_null_constraints`; exclusion `semantic/core.py` `atom_constraints`). Its help text
    must describe that, not the existential `non_empty` constraint."""
    help_text = _help_for('non_null').lower()
    assert 'null state' in help_text, (
        f"--non_null help must mention the null state, got: {help_text!r}"
    )
    assert 'non-empty' not in help_text, (
        f"--non_null help must not describe the non_empty constraint, got: {help_text!r}"
    )


def test_non_empty_help_describes_the_existential_constraint():
    """`non_empty` emits `Exists(x, y) verify(x) & falsify(y)` -- at least one verifier and (in
    bilateral theories) one falsifier. Its help text must describe that, not subject matter,
    which belongs to `--disjoint`."""
    help_text = _help_for('non_empty').lower()
    assert 'verifier' in help_text, (
        f"--non_empty help must mention verifiers, got: {help_text!r}"
    )
    assert 'subject matter' not in help_text, (
        f"--non_empty help must not describe subject matter, got: {help_text!r}"
    )


# ---------------------------------------------------------------------------------------------
# Boolean flags: both spellings against the tiny example, exit 0, no Traceback.
# For -p/-z/-i, output must differ from the no-flag baseline.
# ---------------------------------------------------------------------------------------------

_BOOLEAN_FLAGS = [
    ('contingent', '-c', '--contingent'),
    ('non_null', '-n', '--non_null'),
    ('non_empty', '-e', '--non_empty'),
    ('disjoint', '-d', '--disjoint'),
    ('print_constraints', '-p', '--print_constraints'),
    ('print_z3', '-z', '--print_z3'),
    ('print_impossible', '-i', '--print_impossible'),
    ('align_vertically', '-a', '--align_vertically'),
]

_OUTPUT_AFFECTING = {'print_constraints', 'print_z3', 'print_impossible'}


@pytest.mark.parametrize(
    "name,short,long",
    _BOOLEAN_FLAGS,
    ids=[name for name, _, _ in _BOOLEAN_FLAGS],
)
@pytest.mark.parametrize("spelling", ["short", "long"])
def test_boolean_flag_accepted(name, short, long, spelling, tiny_example_file):
    flag = short if spelling == "short" else long
    result = run_cli_command([flag, str(tiny_example_file)], check=False)
    assert result.returncode == 0, (
        f"{flag} exited {result.returncode}:\nSTDOUT:{result.stdout}\nSTDERR:{result.stderr}"
    )
    assert 'Traceback' not in (result.stderr or ''), f"{flag} produced a Traceback"
    assert 'Traceback' not in (result.stdout or ''), f"{flag} produced a Traceback"


@pytest.mark.parametrize(
    "name,short,long",
    [entry for entry in _BOOLEAN_FLAGS if entry[0] in _OUTPUT_AFFECTING],
    ids=[name for name, _, _ in _BOOLEAN_FLAGS if name in _OUTPUT_AFFECTING],
)
def test_output_affecting_boolean_flag_changes_output(name, short, long, tiny_example_file):
    """-p/-z/-i must not merely be accepted -- their output must differ from the no-flag
    baseline, or the flag-accepted test above would pass vacuously for a no-op flag."""
    baseline = run_cli_command([str(tiny_example_file)], check=False)
    assert baseline.returncode == 0

    with_flag = run_cli_command([short, str(tiny_example_file)], check=False)
    assert with_flag.returncode == 0
    assert with_flag.stdout != baseline.stdout, (
        f"{short} produced identical output to the no-flag baseline"
    )


# ---------------------------------------------------------------------------------------------
# --save / -s
# ---------------------------------------------------------------------------------------------


def test_save_absent_produces_no_output_directory(tmp_path, tiny_example_content):
    example_file = tmp_path / "ex.py"
    example_file.write_text(tiny_example_content)

    result = run_cli_command([str(example_file)], check=False, cwd=tmp_path)
    assert result.returncode == 0
    assert list(tmp_path.glob("output_*")) == []


def test_save_bare_produces_markdown_and_json(tmp_path, tiny_example_content):
    """Bare -s (nargs='*' with zero args) saves both markdown and json."""
    example_file = tmp_path / "ex.py"
    example_file.write_text(tiny_example_content)

    # file_path precedes --save so argparse's nargs='*' greedy consumption doesn't swallow the
    # positional file_path as a --save value.
    result = run_cli_command([str(example_file), '--save'], check=False, cwd=tmp_path)
    assert result.returncode == 0

    output_dirs = list(tmp_path.glob("output_*"))
    assert len(output_dirs) == 1, f"expected exactly one output_* dir, found {output_dirs}"
    saved_files = {p.name for p in output_dirs[0].iterdir()}
    assert 'EXAMPLES.md' in saved_files
    assert 'MODELS.json' in saved_files


@pytest.mark.parametrize("fmt,expected_file", [("markdown", "EXAMPLES.md"), ("json", "MODELS.json")])
def test_save_with_explicit_format(tmp_path, tiny_example_content, fmt, expected_file):
    example_file = tmp_path / "ex.py"
    example_file.write_text(tiny_example_content)

    result = run_cli_command([str(example_file), '--save', fmt], check=False, cwd=tmp_path)
    assert result.returncode == 0

    output_dirs = list(tmp_path.glob("output_*"))
    assert len(output_dirs) == 1
    saved_files = {p.name for p in output_dirs[0].iterdir()}
    assert saved_files == {expected_file}, (
        f"--save {fmt} should produce exactly {{{expected_file}}}, got {saved_files}"
    )


# ---------------------------------------------------------------------------------------------
# --maximize / -m
# ---------------------------------------------------------------------------------------------

# Uses logos rather than bimodal: asserts only dispatch to
# module.comparison.run_comparison() (see the consuming test's own docstring), nothing
# bimodal-specific. Same remedy, same rationale as this file's _CVC5_COMPATIBLE_EXAMPLE swap
# below and tests/cli/conftest.py's precedent fix.
_MAXIMIZE_EXAMPLE = '''"""Minimal comparison example for --maximize CLI testing."""

from model_checker.theory_lib import logos

theory = logos.get_theory()
semantic_theories = {
    "theory_a": theory,
    "theory_b": theory,
}

_settings = dict(theory["semantics"].DEFAULT_EXAMPLE_SETTINGS)
_settings.update({"N": 2, "max_time": 0.3})

example_range = {
    "CMP_TEST": [
        [],
        ["A"],
        _settings,
    ]
}

general_settings = {
    "maximize": True,
}
'''


@pytest.mark.parametrize("flag", ["--maximize", "-m"])
def test_maximize_dispatches_to_run_comparison(tmp_path, flag):
    """Asserts dispatch to module.comparison.run_comparison() (__main__.py's maximize branch),
    not comparison depth or specific max-N results -- those are covered, if at all, by
    builder/tests/. Uses the smallest viable example (N=2, tight max_time, two theory entries)
    with an explicit subprocess timeout since this path forks a ProcessPoolExecutor.
    """
    example_file = tmp_path / "cmp.py"
    example_file.write_text(_MAXIMIZE_EXAMPLE)

    result = run_cli_command([flag, str(example_file)], check=False, timeout=60)

    assert result.returncode == 0, (
        f"--maximize exited {result.returncode}:\nSTDOUT:{result.stdout}\nSTDERR:{result.stderr}"
    )
    assert 'Traceback' not in result.stderr
    assert 'EXAMPLE' in result.stdout
    assert 'Comparison Results' in result.stdout


# ---------------------------------------------------------------------------------------------
# --z3 / --cvc5 (solver selection group)
# ---------------------------------------------------------------------------------------------


def test_z3_flag_selects_backend_and_runs(tiny_example_file):
    result = run_cli_command(['--z3', str(tiny_example_file)], check=False)
    assert result.returncode == 0
    assert 'Traceback' not in result.stderr


_CVC5_COMPATIBLE_EXAMPLE = '''"""Minimal logos example for --cvc5 CLI testing.

Uses logos rather than bimodal: bimodal's frame constraints call z3.MultiPattern via the
z3_shim, which cvc5.pythonic does not implement, so bimodal cannot complete a solve under the
--cvc5 backend in this environment. logos does not hit that gap.
"""

from model_checker.theory_lib import logos

theory = logos.get_theory()
semantic_theories = {"cli_test": theory}
example_range = {"CLI_TEST": [[], ["A"], {"N": 2}]}
'''


def test_cvc5_flag(tmp_path):
    """Guards on cvc5 import availability so neither environment yields a vacuous pass: when
    cvc5 is installed, asserts a real successful dispatch; when it is not, asserts the clean
    ImportError-handling path at __main__.py's cvc5 branch (exit 0, not a crash).
    """
    example_file = tmp_path / "cvc5_ex.py"

    if detect_cvc5():
        example_file.write_text(_CVC5_COMPATIBLE_EXAMPLE)
        result = run_cli_command(['--cvc5', str(example_file)], check=False)
        assert result.returncode == 0, (
            f"--cvc5 exited {result.returncode}:\nSTDOUT:{result.stdout}\nSTDERR:{result.stderr}"
        )
        assert 'Traceback' not in result.stderr
        assert result.stdout.strip()
    else:
        example_file.write_text(
            'semantic_theories = {}\nexample_range = {}\n'
        )
        result = run_cli_command(['--cvc5', str(example_file)], check=False)
        # __main__.py's cvc5 branch catches ImportError, prints two lines, and returns --
        # exit 0, not a crash.
        assert result.returncode == 0, (
            f"--cvc5 (uninstalled) exited {result.returncode}:\n"
            f"STDOUT:{result.stdout}\nSTDERR:{result.stderr}"
        )
        assert 'Traceback' not in result.stderr
        assert 'cvc5' in result.stdout.lower()
        assert 'pip install cvc5' in result.stdout


# ---------------------------------------------------------------------------------------------
# --upgrade / -u -- unit test with mocked subprocess.run, NEVER executed for real.
# ---------------------------------------------------------------------------------------------


@pytest.mark.parametrize("argv_flag", ["--upgrade", "-u"])
def test_upgrade_constructs_expected_pip_command_without_executing(monkeypatch, argv_flag):
    """Asserts the constructed argv and check=True without ever running pip."""
    import model_checker.__main__ as main_module

    monkeypatch.setattr(sys, 'argv', ['model-checker', argv_flag])

    with patch('subprocess.run') as mock_run:
        mock_run.return_value.returncode = 0
        main_module.main()

    mock_run.assert_called_once()
    call_args, call_kwargs = mock_run.call_args
    package_name = ParseFileFlags().parser.prog
    assert call_args[0] == [sys.executable, '-m', 'pip', 'install', '--upgrade', package_name]
    assert call_kwargs.get('check') is True


# ---------------------------------------------------------------------------------------------
# --sequential / -q -- fail-fast contract
# ---------------------------------------------------------------------------------------------


@pytest.mark.parametrize("flag", ["--sequential", "-q"])
def test_sequential_fails_fast_without_traceback(tiny_example_file, flag):
    """module.py's _initialize_output_management raises NotImplementedError whenever
    config.sequential is truthy (SequentialSaveManager/ConsoleInputProvider were deliberately
    removed); __main__.py's main() catches it, prints 'Error: ...', and exits 1. This is the
    correct current behavior, not a defect -- restoring interactive save is a declared Non-Goal.
    """
    result = run_cli_command([flag, str(tiny_example_file)], check=False)
    assert result.returncode == 1
    combined = (result.stdout or '') + (result.stderr or '')
    assert 'Traceback' not in combined


# ---------------------------------------------------------------------------------------------
# --load_theory / -l -- dispatches to BuildProject.ask_generate(), which blocks on input();
# piped through run_cli_command's existing `input=` parameter rather than left excluded.
# ---------------------------------------------------------------------------------------------


@pytest.mark.parametrize("flag", ["--load_theory", "-l"])
def test_load_theory_generates_project_non_interactively(tmp_path, flag):
    """Answer all three ask_generate()/`_handle_example_script` prompts ('y' to generate,
    a project name, 'n' to skip the example run) via stdin, run in `tmp_path` so the generated
    project is contained, and confirm a clean, error-free, successful generation."""
    result = run_cli_command(
        [flag, 'bimodal'],
        input="y\ngen_project\nn\n",
        cwd=tmp_path,
        timeout=30,
        check=False,
    )
    assert result.returncode == 0, (
        f"load_theory generation failed: stdout={result.stdout!r} stderr={result.stderr!r}"
    )
    assert 'Error creating project' not in result.stdout
    assert 'Traceback' not in result.stdout and 'Traceback' not in (result.stderr or '')
    assert (tmp_path / 'project_gen_project').is_dir()


def test_load_theory_does_not_hang_with_closed_stdin(tmp_path):
    """A closed stdin (EOF on the very first prompt) must fail fast, not hang -- confirms the
    30s default timeout is a backstop, not the normal path."""
    result = run_cli_command(
        ['-l', 'bimodal'], input="", cwd=tmp_path, timeout=30, check=False
    )
    assert result.returncode != 0


# ---------------------------------------------------------------------------------------------
# --project_name / -y -- non-interactive project generation, no stdin reads at all. Deeper
# scenario coverage (missing-name error message, destination-directory honoring, interactive
# path left unchanged) lives in code/tests/unit/test_main_cli.py; this file's own dispatch
# test exists for _COVERED_FLAGS bookkeeping parity with every other registered flag.
# ---------------------------------------------------------------------------------------------


@pytest.mark.parametrize("flag", ["--project_name", "-y"])
def test_project_name_generates_project_non_interactively(tmp_path, flag):
    """-l/--load_theory combined with -y/--project_name generates a project with stdin
    closed (input="") -- no prompt is ever read, unlike the plain --load_theory path above."""
    result = run_cli_command(
        ['--load_theory', 'bimodal', flag, 'gen_project_flag_matrix'],
        input="",
        cwd=tmp_path,
        timeout=30,
        check=False,
    )
    assert result.returncode == 0, (
        f"non-interactive generation failed: stdout={result.stdout!r} stderr={result.stderr!r}"
    )
    assert 'Error creating project' not in result.stdout
    assert 'Traceback' not in result.stdout and 'Traceback' not in (result.stderr or '')
    assert (tmp_path / 'project_gen_project_flag_matrix').is_dir()
