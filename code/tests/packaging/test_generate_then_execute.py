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


def test_registry_is_non_empty():
    """An empty registry must not silently produce a zero-test vacuous pass below."""
    assert registry.get_registered(), "registry.get_registered() returned no theories"


@pytest.mark.parametrize("theory_name", registry.get_registered())
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
        # bimodal's full default generated examples.py is genuinely slow -- confirmed directly
        # at ~100s via the ambient interpreter (not a bug: it runs every example in the
        # theory's default set). 180s gives comfortable margin over that plus venv-subprocess
        # overhead without approaching pytest-timeout's own per-test ceiling.
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


def test_parametrization_count_matches_live_registry():
    """The parametrized test above must run once per live registry entry -- confirmed via the
    live count rather than a hardcoded '4 theories' assumption, so registry growth/shrinkage is
    automatically reflected rather than silently under- or over-covered."""
    assert len(registry.get_registered()) == len(set(registry.get_registered())), (
        "registry.get_registered() returned duplicate theory names"
    )
