"""The one color-gating predicate for printed model output.

Every printer in the framework (`models/structure.py`'s interpreted-sentence tree) and in the
theories (`theory_lib/*/semantic/model.py`) asks `use_colors(output)` before emitting an ANSI
escape. The predicate replaced a framework-wide `output is sys.__stdout__` identity test, which
colored a redirected or piped stdout exactly as it colored a terminal (so `dev_cli.py ... | cat`
and `> file` received raw `\\033[` sequences) and never honored the `NO_COLOR` convention.

Precedence, following no-color.org and clig.dev:

1. `NO_COLOR` present and non-empty: never color, whatever else holds.
2. `FORCE_COLOR` present and non-empty: always color, even into a pipe, a file, or an
   `io.StringIO` (the opt-in for a caller that captures output and wants the escapes).
3. `TERM=dumb`: never color.
4. Otherwise the stream decides: `output.isatty()` when the stream has one, else `False`.

A `StringIO` has an `isatty()` that returns `False`, so captured output (`capsys`,
`builder/module.py`'s `_capture_model_output`, `--save`) is plain text by default -- exactly
what `output/formatters.py`'s `ANSIToMarkdown` consumers saw before this predicate existed.
See `code/docs/core/CODE_STANDARDS.md`'s "Printed Output Conventions" section for the palette
each color carries and the rule that color never carries information alone.
"""

from __future__ import annotations

import os
from typing import Any

__all__ = ["use_colors"]


def use_colors(output: Any) -> bool:
    """Whether ANSI color escapes should be written to `output`. See the module docstring
    for the `NO_COLOR` > `FORCE_COLOR` > `TERM=dumb` > `isatty()` precedence."""
    if os.environ.get("NO_COLOR"):
        return False
    if os.environ.get("FORCE_COLOR"):
        return True
    if os.environ.get("TERM") == "dumb":
        return False
    isatty = getattr(output, "isatty", None)
    if isatty is None:
        return False
    try:
        return bool(isatty())
    except (ValueError, OSError):
        return False
