"""Single source of the CLI invocation-mode vocabulary and its validation.

`MODELCHECKER_CLI_TEST_MODE` selects how `tests.utils.helpers.run_cli_command` invokes the
`model-checker` CLI:

- ``source`` (default) -- `python -m model_checker` with `code/src` injected onto `PYTHONPATH`.
  Byte-for-byte today's developer-loop behavior; nothing reads this module's env var to change
  that path.
- ``installed`` -- the pip-installed `model-checker` console script, resolved via
  `shutil.which`, with no `PYTHONPATH` injection. Any accidental reliance on the source tree
  fails here by construction.
- ``installed-module`` -- `python -m model_checker`, also with no `PYTHONPATH` injection, so it
  can only succeed against a package actually installed into the running interpreter. Used for
  console-script vs. `python -m` parity checks across the whole CLI suite.

No other module in this test tree should re-derive this vocabulary; import `get_cli_test_mode`
from here instead.
"""

from __future__ import annotations

import os

_VALID_MODES = ("source", "installed", "installed-module")


def get_cli_test_mode() -> str:
    """Read and validate `MODELCHECKER_CLI_TEST_MODE`, defaulting to `'source'`.

    Raises:
        ValueError: if the env var is set to a value outside `_VALID_MODES`. The offending
            value is included in the message so a typo'd mode fails loudly rather than silently
            falling back to a default.
    """
    mode = os.environ.get("MODELCHECKER_CLI_TEST_MODE", "source")
    if mode not in _VALID_MODES:
        raise ValueError(
            f"Unknown MODELCHECKER_CLI_TEST_MODE: {mode!r}; expected one of {_VALID_MODES}"
        )
    return mode
