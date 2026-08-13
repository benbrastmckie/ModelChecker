"""The mandatory anti-vacuous-pass guard.

If `code/src` reaches `sys.path` while a non-source `MODELCHECKER_CLI_TEST_MODE` is active,
`import model_checker` silently resolves to the working tree instead of the installed wheel, and
the entire installed-mode verification effort passes without ever touching its subject. This
test exists to make that failure loud rather than silent (see the plan's Phase 3 rationale,
carried from research finding F8 / decision D6).

In `source` mode this test is a deliberate, loudly-reasoned skip -- the assertion below applies
only to installed modes, where the source tree must NOT be importable.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

from tests.utils.cli_mode import get_cli_test_mode


def test_installed_mode_does_not_shadow_via_source_tree():
    """Assert the installed package -- not the working tree -- is what `import model_checker`
    resolves to, whenever a non-source mode is active."""
    mode = get_cli_test_mode()
    if mode == "source":
        pytest.skip(
            "source mode: this assertion applies to installed modes only "
            "(MODELCHECKER_CLI_TEST_MODE=installed or installed-module)"
        )

    import model_checker

    assert "site-packages" in model_checker.__file__, (
        f"installed mode ({mode!r}) is resolving model_checker to "
        f"{model_checker.__file__!r} -- the source tree is shadowing the installed wheel, "
        "so the suite would pass vacuously without ever exercising the wheel"
    )

    repo_src = str((Path(__file__).parent.parent.parent / "src").resolve())
    shadowing_entries = [
        entry for entry in sys.path
        if entry and str(Path(entry).resolve()) == repo_src
    ]
    assert not shadowing_entries, (
        f"installed mode ({mode!r}) still has code/src on sys.path: {shadowing_entries!r} -- "
        "this must be purged so a subsequent import cannot silently fall back to the source tree"
    )
