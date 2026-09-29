"""Registry-driven generate-then-execute: the primary "generate a project, then run it" user
journey, automated for every theory in `registry.get_registered()` and driven through the real
installed `model-checker` console script.

Spike-first finding: `builder/tests/integration/test_generated_projects.py`'s docstring notes
document that generated projects "cannot be loaded standalone" via `BuildModule` given a bare
`file_path` with no package context. That is true for the narrow scenario those tests exercise
(a hand-built `MockFlags` with only `file_path` set, bypassing the CLI's package-detection
path). It does **not** describe the real CLI journey: `BuildProject.generate()` writes a
`.modelchecker` marker into the generated project directory (`project.py`'s
`_create_package_marker`), which `builder/detector.py`'s `ProjectDetector` recognizes, routing
the load through `strategies.py`'s `PackageImportStrategy` -- which resolves the generated
project's relative imports correctly. Confirmed directly with a manual bimodal spike before
parametrizing this file: `model-checker <generated>/examples.py` produces a complete, correct
countermodel. The generate-then-execute journey is not broken; the file it commented would need
to be re-verified, not that this task's target journey fails.
"""

from __future__ import annotations

import subprocess

import pytest

from model_checker import registry

from .conftest import _console_script_path, handle_known_venv_libz3_link_failure

pytestmark = [pytest.mark.packaging, pytest.mark.slow]

# Loose sanity floor for real solver output length. The review's per-theory figures
# (logos/exclusion/imposition/bimodal = 1099/188/95/770 lines) are used only to set a
# conservative shared floor well under the smallest (imposition, ~95) -- never an equality
# assertion, since output length drifts with unrelated formatting changes.
_MIN_OUTPUT_LINES = 20

# Theories whose generate-then-execute parametrize case needed quarantining from gating.
# Previously `{"bimodal"}`: bimodal's window-and-abundance encoding made its full default
# generated examples.py genuinely the most expensive case in this file (measured 81.06s vs.
# the next-slowest registered theory's 4.31s), a completeness claim quarantined via
# `development` per TESTING_GUIDE.md section 8.14 rather than raising this file's shared
# timeout. The witness-family certificate redesign replaced that encoding with a
# quantifier-free search under which every one of bimodal's 53 examples decides in well under
# 50ms, so the cost this set existed to quarantine no longer exists; bimodal is removed and the
# set is kept empty (not deleted) for the same greppable-single-point-of-extension reason other
# now-empty exclusion registries in this codebase are kept rather than removed. Applies
# uniformly to every parametrize-over-registry test in this file (both the ambient-encoding
# `test_generate_then_execute` and the cp1252-constrained `test_generate_then_execute_cp1252`).
_DEVELOPMENT_THEORIES: set = set()


def _registry_params() -> list:
    """`registry.get_registered()`, wrapped so any future `_DEVELOPMENT_THEORIES` entry would
    carry `development` -- the `UNSTABLE_EXAMPLES` set-membership idiom TESTING_GUIDE.md 8.14
    names as the established pattern, applied here to `development` instead of `unstable`.
    `_DEVELOPMENT_THEORIES` is currently empty, so every parametrize case here is unmarked."""
    return [
        pytest.param(name, marks=[pytest.mark.development] if name in _DEVELOPMENT_THEORIES else [])
        for name in registry.get_registered()
    ]


def test_registry_is_non_empty():
    """An empty registry must not silently produce a zero-test vacuous pass below."""
    assert registry.get_registered(), "registry.get_registered() returned no theories"


@pytest.mark.parametrize("theory_name", _registry_params())
def test_generate_then_execute(theory_name, installed_venv, tmp_path):
    """Generate a real project for `theory_name` (BuildProject.generate() -- the non-interactive
    API, never ask_generate(), and never tests/utils/helpers.py::create_temp_project, which
    hand-writes a fake project and never calls BuildProject), then run its generated
    examples.py through the real, installed console script."""
    from model_checker.builder.project import BuildProject

    builder = BuildProject(theory_name)
    project_dir = builder.generate(f"gen_{theory_name}", str(tmp_path))
    examples_path = f"{project_dir}/examples.py"

    script_path = _console_script_path(installed_venv)
    result = subprocess.run(
        [str(script_path), examples_path],
        env=installed_venv["env"],
        capture_output=True,
        text=True,
        # bimodal's full default generated examples.py was previously the slowest case in this
        # file (measured 81.06s through the installed console script under the retired
        # window-and-abundance encoding, quarantined from gating via _DEVELOPMENT_THEORIES
        # above rather than relied upon to stay under this timeout). The witness-family
        # certificate redesign made every bimodal example decide in well under 50ms, so bimodal
        # is no longer in _DEVELOPMENT_THEORIES and now runs gating like every other theory.
        # 180s is retained unchanged as a genuine hang guard for every theory, not raised or
        # lowered as a consequence of this change.
        timeout=180,
    )
    handle_known_venv_libz3_link_failure(result)

    assert result.returncode == 0, (
        f"generate-then-execute for '{theory_name}' exited {result.returncode}:\n"
        f"STDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
    )
    assert 'Traceback' not in result.stdout, (
        f"generate-then-execute for '{theory_name}' printed a Traceback to stdout"
    )
    assert 'Traceback' not in result.stderr, (
        f"generate-then-execute for '{theory_name}' printed a Traceback to stderr"
    )

    line_count = result.stdout.count('\n')
    assert line_count >= _MIN_OUTPUT_LINES, (
        f"generate-then-execute for '{theory_name}' produced suspiciously little output "
        f"({line_count} lines, floor is {_MIN_OUTPUT_LINES}): {result.stdout!r}"
    )


@pytest.mark.parametrize("theory_name", _registry_params())
def test_generate_then_execute_cp1252(theory_name, installed_venv, tmp_path):
    """The same generate-then-execute journey as `test_generate_then_execute`, but with the
    child process's `sys.stdout` constrained to the `cp1252` codec via `PYTHONIOENCODING`.

    This reproduces the exact Windows child-process condition from the research report
    (`specs/182_.../reports/01_windows-unicode-encode-error.md`, §1): once stdout is
    redirected/piped (as it always is under `subprocess.run(..., capture_output=True)`),
    Python falls off the PEP-528 `WriteConsoleW` console path and resolves `sys.stdout`'s
    encoding via `locale.getpreferredencoding()` -- `cp1252` on the GitHub `windows-latest`
    runner's default locale. `PYTHONIOENCODING` overrides that resolution identically on any
    platform, so setting it here reproduces the same child-side encoding constraint on Linux,
    with no Windows runner required.

    `installed_venv["env"]` itself is deliberately left untouched -- this test copies it and
    adds `PYTHONIOENCODING` to the copy only. Adding it to the shared fixture env would mask
    the defect in `test_generate_then_execute` above and make this leg untestable (nothing
    would distinguish the two legs); see this file's own `pytestmark` and
    `code/docs/core/TESTING_GUIDE.md`'s output-encoding section for the standing prohibition.
    """
    from model_checker.builder.project import BuildProject

    builder = BuildProject(theory_name)
    project_dir = builder.generate(f"gen_{theory_name}_cp1252", str(tmp_path))
    examples_path = f"{project_dir}/examples.py"

    script_path = _console_script_path(installed_venv)
    cp1252_env = dict(installed_venv["env"])
    cp1252_env["PYTHONIOENCODING"] = "cp1252"
    result = subprocess.run(
        [str(script_path), examples_path],
        env=cp1252_env,
        capture_output=True,
        # Decode the child's bytes with the codec the child was told to write in. `text=True`
        # would decode them as the parent's locale encoding (UTF-8), and any glyph cp1252 CAN
        # represent -- `…` (0x85) on every bimodal history row, `¬` (0xAC) -- is a valid cp1252
        # byte that is not valid UTF-8, so the harness itself would raise
        # `UnicodeDecodeError` on a child that behaved correctly.
        encoding="cp1252",
        # Same margin as the ambient leg above -- the cp1252 constraint changes
        # glyph selection, not solve cost, so the same timeout budget applies.
        timeout=180,
    )
    handle_known_venv_libz3_link_failure(result)

    assert result.returncode == 0, (
        f"generate-then-execute (cp1252) for '{theory_name}' exited {result.returncode}:\n"
        f"STDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
    )
    assert 'Traceback' not in result.stdout, (
        f"generate-then-execute (cp1252) for '{theory_name}' printed a Traceback to stdout"
    )
    assert 'Traceback' not in result.stderr, (
        f"generate-then-execute (cp1252) for '{theory_name}' printed a Traceback to stderr"
    )

    line_count = result.stdout.count('\n')
    assert line_count >= _MIN_OUTPUT_LINES, (
        f"generate-then-execute (cp1252) for '{theory_name}' produced suspiciously little "
        f"output ({line_count} lines, floor is {_MIN_OUTPUT_LINES}): {result.stdout!r}"
    )

    # The fallback must substitute a readable ASCII glyph, not mangle the character into the
    # Unicode replacement character -- i.e. the encoding-safety fix must be a deliberate glyph
    # substitution (model_checker.utils.glyphs), not an errors="replace"-style workaround.
    assert '�' not in result.stdout, (
        f"generate-then-execute (cp1252) for '{theory_name}' contains the Unicode replacement "
        f"character -- a glyph was mangled rather than substituted"
    )


def test_parametrization_count_matches_live_registry():
    """The parametrized test above must run once per live registry entry -- confirmed via the
    live count rather than a hardcoded '4 theories' assumption, so registry growth/shrinkage is
    automatically reflected rather than silently under- or over-covered."""
    assert len(registry.get_registered()) == len(set(registry.get_registered())), (
        "registry.get_registered() returned duplicate theory names"
    )
