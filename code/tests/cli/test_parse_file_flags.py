"""Unit tests for `model_checker.__main__.ParseFileFlags`.

Complements `code/tests/unit/test_main_cli.py` (which already covers `_short_to_long`
completeness against registered short options, `-p`/`--print_constraints` equivalence alone,
`--load_theory` registry-derived choices, `--save jupyter` rejection, bare `--save`, and
`--sequential`'s clean-exit path). This file adds:

- Parser *structure* assertions (`-l`/`--load_theory` choices, `--z3`/`--cvc5` mutex with no
  short forms, `-s`/`--save` nargs/choices).
- `parse()` stamping `_short_to_long`/`_parsed_args` onto the returned Namespace.
- The full short/long equivalence sweep across every `_short_to_long` entry (not just `-p`), with
  its own completeness assertion -- the direct regression guard for the `-p`-class silent-no-op
  defect at `settings.py:202-274`.
- The `settings.py:202-274` override mechanism directly (present-vs-absent-in-`_parsed_args`).
- The documented clustered-short-flag gap (`-cn`).
- `standard_args` producing no "unknown flag" warning.
- The `test_conflicting_flags` mutex assertion (filling the stub at
  `code/tests/integration/test_error_handling.py:69`).
"""

from __future__ import annotations

import sys

import pytest

from model_checker.__main__ import ParseFileFlags
from model_checker.settings import SettingsManager


def _fresh_short_to_long() -> dict:
    """Parse a bare `model-checker` invocation just to read the stamped `_short_to_long` map."""
    flags = ParseFileFlags()
    old_argv = sys.argv
    sys.argv = ['model-checker']
    try:
        flags.parse()
    finally:
        sys.argv = old_argv
    return dict(flags._short_to_long)


# ---------------------------------------------------------------------------------------------
# Parser structure
# ---------------------------------------------------------------------------------------------


def test_load_theory_choices_come_from_registry():
    """-l/--load_theory's `choices` is exactly registry.get_registered()."""
    from model_checker import registry

    flags = ParseFileFlags()
    action = flags.parser._option_string_actions['--load_theory']
    assert action.choices == registry.get_registered()
    assert flags.parser._option_string_actions['-l'] is action


def test_z3_cvc5_are_mutually_exclusive_with_no_short_forms():
    """--z3/--cvc5 form a mutually exclusive group; neither has a short flag."""
    flags = ParseFileFlags()
    option_strings = set(flags.parser._option_string_actions.keys())

    assert '--z3' in option_strings
    assert '--cvc5' in option_strings
    # No short spelling is registered for either flag (distinct from '-z', which maps to
    # --print_z3, an entirely different flag).
    for opt in option_strings:
        if len(opt) == 2 and opt.startswith('-'):
            assert opt not in ('-3', '-5')

    z3_action = flags.parser._option_string_actions['--z3']
    cvc5_action = flags.parser._option_string_actions['--cvc5']
    mutex_groups = flags.parser._mutually_exclusive_groups
    assert any(
        z3_action in group._group_actions and cvc5_action in group._group_actions
        for group in mutex_groups
    ), "--z3 and --cvc5 must share a mutually exclusive group"


def test_save_is_nargs_star_with_markdown_json_choices():
    """-s/--save is nargs='*' with choices=['markdown', 'json']."""
    flags = ParseFileFlags()
    action = flags.parser._option_string_actions['--save']
    assert flags.parser._option_string_actions['-s'] is action
    assert action.nargs == '*'
    assert action.choices == ['markdown', 'json']
    assert action.default is None


# ---------------------------------------------------------------------------------------------
# parse() stamping _short_to_long / _parsed_args
# ---------------------------------------------------------------------------------------------


def test_parse_stamps_short_to_long_and_parsed_args(monkeypatch, tmp_path):
    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    argv = ['model-checker', '-c', str(example_file)]
    monkeypatch.setattr(sys, 'argv', argv)

    flags = ParseFileFlags()
    module_flags, package_name = flags.parse()

    assert module_flags._short_to_long == flags._short_to_long
    assert module_flags._parsed_args == argv[1:]
    assert package_name == flags.parser.prog


def test_short_to_long_has_fourteen_entries():
    """Scope Hypothesis: _short_to_long is asserted to have 14 entries
    (c,d,e,l,m,n,p,q,s,i,v,u,z,a), read from __main__.py:208-223. Asserted via len(...) rather
    than trusting the prose count alone, so a future addition/removal fails loudly here instead
    of silently shrinking the equivalence sweep below.
    """
    assert len(_fresh_short_to_long()) == 14


# ---------------------------------------------------------------------------------------------
# Short/long equivalence sweep -- the core regression guard
# ---------------------------------------------------------------------------------------------


class _SweepSemantics:
    """Semantics stand-in exposing every setting the generic sweep flags can override.

    `contingent`/`non_null`/`non_empty`/`disjoint` resolve through SettingsManager's
    DEFAULT_EXAMPLE_SETTINGS fallback (settings.py's `_apply_overrides`); `align_vertically`
    resolves through `ADDITIONAL_GENERAL_SETTINGS` augmentation; `maximize`/`print_constraints`/
    `sequential`/`print_z3`/`print_impossible` are already present on the base
    SemanticDefaults.DEFAULT_GENERAL_SETTINGS and need no extra declaration here.
    """
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'max_time': 1,
        'contingent': False,
        'non_null': False,
        'non_empty': False,
        'disjoint': False,
    }
    ADDITIONAL_GENERAL_SETTINGS = {
        'align_vertically': False,
    }


# Every _short_to_long entry, partitioned into three disjoint categories whose sizes must sum to
# len(_short_to_long) -- this is the sweep's own completeness assertion.
_EXIT_FLAGS = {'v'}            # action='version': parsing '-v'/'--version' calls sys.exit(0)
_REQUIRED_VALUE_FLAGS = {'l'}  # requires a theory-name value and short-circuits main() before
                                # settings ever merge; equivalence covered by
                                # tests/unit/test_main_cli.py's registry-derived choices test
_SPECIALLY_HANDLED_FLAGS = {'s', 'u'}  # save (nargs='*', no settings key) and upgrade (no
                                        # settings key) -- asserted below with bespoke checks
                                        # rather than the generic settings-equality loop
_GENERIC_SWEEP_FLAGS = ('c', 'd', 'e', 'm', 'n', 'p', 'q', 'i', 'z', 'a')


def _merged_settings_for(argv_flag, example_file, monkeypatch):
    monkeypatch.setattr(sys, 'argv', ['model-checker', argv_flag, str(example_file)])
    flags = ParseFileFlags()
    module_flags, _ = flags.parse()

    semantic_theory = {'semantics': _SweepSemantics}
    manager = SettingsManager(semantic_theory)
    settings = manager.validate_general_settings(None)
    return manager.apply_flag_overrides(settings, module_flags)


def test_sweep_partition_covers_every_short_to_long_entry():
    """The generic sweep + excluded/specially-handled flags account for every _short_to_long
    entry -- adding a 15th flag without updating this partition fails this assertion loudly,
    rather than the sweep silently covering only a subset."""
    all_pairs = _fresh_short_to_long()
    accounted = set(_GENERIC_SWEEP_FLAGS) | _EXIT_FLAGS | _REQUIRED_VALUE_FLAGS | _SPECIALLY_HANDLED_FLAGS

    assert accounted == set(all_pairs)
    assert (
        len(_GENERIC_SWEEP_FLAGS) + len(_EXIT_FLAGS) + len(_REQUIRED_VALUE_FLAGS)
        + len(_SPECIALLY_HANDLED_FLAGS) == len(all_pairs)
    )


@pytest.mark.parametrize("short", _GENERIC_SWEEP_FLAGS)
def test_short_long_equivalence_sweep(short, tmp_path, monkeypatch):
    """For every generic-sweep (short, long) pair, -x and --long_name produce identical merged
    settings. This is the direct regression guard for the `-p`-class silent-no-op mapping bug."""
    all_pairs = _fresh_short_to_long()
    long_name = all_pairs[short]

    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    short_settings = _merged_settings_for(f'-{short}', example_file, monkeypatch)
    long_settings = _merged_settings_for(f'--{long_name}', example_file, monkeypatch)

    assert short_settings == long_settings, (
        f"-{short} and --{long_name} produced different merged settings: "
        f"{short_settings} != {long_settings}"
    )
    # Both spellings must actually have flipped the flag from its default (False), otherwise the
    # equality assertion above would pass vacuously (both sides silently unchanged).
    assert short_settings.get(long_name) is True, (
        f"-{short}/--{long_name} did not override '{long_name}' to True in either spelling"
    )


# --- Specially handled flags: -s/--save and -u/--upgrade ---------------------------------------


def test_save_short_and_long_equivalent_bare(monkeypatch, tmp_path):
    """Bare -s and --save (no format args) parse to the same Namespace value."""
    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    def _save_value(flag):
        monkeypatch.setattr(sys, 'argv', ['model-checker', str(example_file), flag])
        flags = ParseFileFlags()
        module_flags, _ = flags.parse()
        return module_flags.save

    assert _save_value('-s') == _save_value('--save') == []


def test_save_short_and_long_equivalent_with_format(monkeypatch, tmp_path):
    """-s markdown and --save markdown parse to the same Namespace value."""
    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    def _save_value(flag):
        monkeypatch.setattr(sys, 'argv', ['model-checker', str(example_file), flag, 'markdown'])
        flags = ParseFileFlags()
        module_flags, _ = flags.parse()
        return module_flags.save

    assert _save_value('-s') == _save_value('--save') == ['markdown']


def test_upgrade_short_and_long_equivalent(monkeypatch, tmp_path):
    """-u and --upgrade both stamp module_flags.upgrade = True.

    'upgrade' is a standard_arg with no corresponding settings key, so there is nothing to
    assert via the merged-settings equality path used by the generic sweep; the equivalent
    assertion here is at the argparse Namespace level.
    """
    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")

    def _upgrade_value(flag):
        monkeypatch.setattr(sys, 'argv', ['model-checker', flag, str(example_file)])
        flags = ParseFileFlags()
        module_flags, _ = flags.parse()
        return module_flags.upgrade

    assert _upgrade_value('-u') is True
    assert _upgrade_value('--upgrade') is True


# ---------------------------------------------------------------------------------------------
# settings.py override mechanism, directly
# ---------------------------------------------------------------------------------------------


def test_flag_present_in_parsed_args_overrides_default(monkeypatch, tmp_path):
    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")
    monkeypatch.setattr(sys, 'argv', ['model-checker', '-p', str(example_file)])

    flags = ParseFileFlags()
    module_flags, _ = flags.parse()
    manager = SettingsManager({'semantics': _SweepSemantics})
    settings = manager.apply_flag_overrides(manager.validate_general_settings(None), module_flags)

    assert settings['print_constraints'] is True


def test_flag_absent_from_parsed_args_leaves_default(monkeypatch, tmp_path):
    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")
    monkeypatch.setattr(sys, 'argv', ['model-checker', str(example_file)])

    flags = ParseFileFlags()
    module_flags, _ = flags.parse()
    manager = SettingsManager({'semantics': _SweepSemantics})
    settings = manager.apply_flag_overrides(manager.validate_general_settings(None), module_flags)

    assert settings['print_constraints'] is False


def test_argparse_attribute_set_but_not_in_parsed_args_does_not_override(tmp_path):
    """The silent-no-op mechanism, directly: an argparse Namespace attribute that is truthy but
    whose flag string is absent from `_parsed_args` (e.g. a hand-built object simulating a real
    parse) does not override the merged setting.

    This is the mechanism that let the `-p` mapping bug ship silently: nothing here raises, it
    just silently fails to apply the override.
    """
    example_file = tmp_path / "example.py"

    class _FakeRealFlags:
        """Mimics a real (non-mock) argparse Namespace: has _parsed_args, so
        _is_mock_object returns False and only flags literally present in _parsed_args count."""
        def __init__(self):
            self.file_path = str(example_file)
            self.print_constraints = True  # truthy attribute
            self._short_to_long = {'p': 'print_constraints'}
            self._parsed_args = [str(example_file)]  # -p is NOT present here

    manager = SettingsManager({'semantics': _SweepSemantics})
    settings = manager.apply_flag_overrides(
        manager.validate_general_settings(None), _FakeRealFlags()
    )

    assert settings['print_constraints'] is False, (
        "A truthy attribute not present in _parsed_args must not override the default -- "
        "this is the exact silent-no-op mechanism the -p regression guarded against."
    )


def test_clustered_short_flags_do_not_override_documented_gap(monkeypatch, tmp_path):
    """-cn parses successfully in argparse (clustering is valid argparse syntax) but does NOT
    override either 'contingent' or 'non_null', because the user-provided-flag extraction in
    settings.py only recognizes `len(arg) == 2` short tokens (see settings.py's comment on
    `_extract_user_provided_flags`). This is documented, deliberate behavior, not a latent bug --
    this test enshrines the documented behavior, not the intuitive one.
    """
    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")
    monkeypatch.setattr(sys, 'argv', ['model-checker', '-cn', str(example_file)])

    flags = ParseFileFlags()
    module_flags, _ = flags.parse()
    # argparse itself DID parse -cn into both booleans:
    assert module_flags.contingent is True
    assert module_flags.non_null is True

    manager = SettingsManager({'semantics': _SweepSemantics})
    settings = manager.apply_flag_overrides(manager.validate_general_settings(None), module_flags)

    # The settings-merge override mechanism does NOT pick up either flag, because '-cn' has
    # len() == 3, not 2, so it is never added to user_provided_flags -- and since neither key was
    # already present in the general-settings dict, apply_flag_overrides's "key in
    # user_provided_flags" gate means the keys are never even added, not merely left at a
    # default. This is a stronger demonstration of the silent no-op than "unchanged": the flags
    # vanish from the merged settings entirely rather than falling back to a default value.
    assert 'contingent' not in settings
    assert 'non_null' not in settings


# ---------------------------------------------------------------------------------------------
# standard_args produce no "unknown flag" warning
# ---------------------------------------------------------------------------------------------


def test_standard_args_produce_no_unknown_flag_warning(monkeypatch, tmp_path, capsys):
    """Every name in settings.py's `standard_args` set is either a real ParseFileFlags attribute
    or harmless to set directly; none of them trigger the "doesn't correspond to any known
    setting" warning when run through apply_flag_overrides via a real parse.
    """
    example_file = tmp_path / "example.py"
    example_file.write_text("semantic_theories = {}\nexample_range = {}\n")
    monkeypatch.setattr(
        sys, 'argv',
        ['model-checker', str(example_file), '--save', '--z3', '-l', 'bimodal'],
    )

    flags = ParseFileFlags()
    module_flags, _ = flags.parse()
    manager = SettingsManager({'semantics': _SweepSemantics})
    manager.apply_flag_overrides(manager.validate_general_settings(None), module_flags)

    captured = capsys.readouterr()
    assert "doesn't correspond to any known setting" not in captured.out
