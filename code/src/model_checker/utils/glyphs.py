"""Stream-encoding-aware glyph fallback for printed model output.

Printed model output writes a small set of non-ASCII glyphs (`⟹`, `→`, `↓`,
subscript digits, progress-bar block characters) to a caller-supplied
`output` stream. When that stream cannot encode a glyph -- most notably a
Windows pipe that falls back to the `cp1252` ANSI codepage once redirected
off the PEP-528 `WriteConsoleW` console path -- printing the raw glyph
raises `UnicodeEncodeError` and crashes the caller.

This module provides a single shared resolution helper: probe
`getattr(output, "encoding", None)`, test-encode the preferred Unicode
glyph against that encoding, and substitute an ASCII equivalent only when
the target codec cannot represent it. A stream with no `.encoding`
attribute (e.g. `io.StringIO`, which never encodes at all) or an
`encoding` of `None` defaults to the Unicode glyph, preserving existing
`StringIO`-based test expectations.

See `code/docs/core/TESTING_GUIDE.md`'s output-encoding testing section and
`theory_lib/bimodal/docs/ARCHITECTURE.md`'s rendering policy subsection for
the durable record of this convention.
"""

from __future__ import annotations

from functools import lru_cache
from typing import Optional

# Semantic glyph name -> (unicode form, ascii fallback form).
#
# Each ASCII fallback is chosen to be readable on its own; callers that need
# the substitution to stay width-neutral against a fixed layout budget (the
# bimodal aligned world-history renderer) must derive their column budget
# from the actually-rendered string rather than assuming any fixed width --
# see `theory_lib/bimodal/semantic/model.py`'s `_create_time_positions`.
_GLYPHS: dict[str, tuple[str, str]] = {
    "DOUBLE_ARROW": ("⟹", "=>"),   # ⟹
    "ARROW": ("→", "->"),          # →
    "DOWN_ARROW": ("↓", "v"),      # ↓
    "BLOCK_FULL": ("█", "#"),      # █
    "BLOCK_LIGHT": ("░", "-"),     # ░
    # Not part of the report's original 9-site inventory: `□` is produced at
    # runtime by `model_checker.utils.bitvector.bitvec_to_substates` for the
    # null/bottom state, so a literal-character grep over theory source never
    # finds it -- it only surfaces by tracing data flow or by actually
    # running a cp1252-constrained print. Found during Phase 2 regression
    # testing; see `code/docs/core/TESTING_GUIDE.md`'s output-encoding
    # section for the full account of why a grep sweep alone is insufficient.
    "NULL_STATE": ("□", "_"),      # □ -- exclusion/imposition/logos state fusions
    # Same discovery path as NULL_STATE: `∅` is a hardcoded fallback literal
    # in `theory_lib/bimodal/semantic/proposition.py`, reachable only via a
    # bare `print()` that targets `sys.stdout` directly (see that module for
    # the known, documented scope boundary this implies).
    "EMPTY_SET": ("∅", "{}"),      # ∅ -- bimodal's "no world state found" fallback
}

# Unicode subscript digits (U+2080-U+2089) and subscript minus (U+208B),
# keyed by their ASCII digit/sign. Both the Unicode and ASCII renderings are
# exactly one character per input character, so `to_subscript` is
# width-neutral by construction -- no column-budget derivation is needed for
# it, unlike the arrow glyphs above.
_SUBSCRIPT_DIGITS: dict[str, str] = {
    '0': '₀', '1': '₁', '2': '₂', '3': '₃', '4': '₄',
    '5': '₅', '6': '₆', '7': '₇', '8': '₈', '9': '₉',
    '-': '₋',
}

# A representative subscript glyph used to probe stream capability once per
# call to `to_subscript` -- all ten digits plus the minus sign live in the
# same contiguous Unicode block and share encodability under every codec
# this module has to reason about, so a single probe suffices.
_SUBSCRIPT_PROBE = _SUBSCRIPT_DIGITS['0']


@lru_cache(maxsize=None)
def stream_can_encode(encoding: Optional[str], text: str) -> bool:
    """Return whether `text` can be encoded using `encoding`.

    Args:
        encoding: The target codec name (e.g. ``"cp1252"``, ``"utf-8"``), or
            `None` when the stream exposes no `.encoding` attribute (or the
            attribute itself is `None`, e.g. `io.StringIO`).
        text: The candidate glyph or string to test-encode.

    Returns:
        `True` when `encoding` is `None` (a stream with no declared
        encoding never encodes, so nothing can fail to encode) or when
        `text.encode(encoding)` succeeds. `False` when encoding raises
        `UnicodeEncodeError` (codec exists but cannot represent `text`) or
        `LookupError` (unknown/bogus codec name) -- the latter is treated
        as "cannot safely render" rather than propagated, since a caller
        printing output should never crash merely because a stream reports
        an encoding this process cannot resolve.

    This predicate is memoized: the glyph set is small (~5 entries) and the
    set of distinct stream encodings encountered in a process is also
    small, so caching `(encoding, text) -> bool` avoids repeating a
    trial-encode on every print call in a hot loop (e.g. per-row printing
    in the bimodal world-history renderer).
    """
    if encoding is None:
        return True
    try:
        text.encode(encoding)
        return True
    except UnicodeEncodeError:
        return False
    except LookupError:
        return False


def glyph(name: str, output) -> str:
    """Resolve glyph `name` to its Unicode or ASCII form for `output`.

    Args:
        name: One of the keys in the module-level substitution table
            (``"DOUBLE_ARROW"``, ``"ARROW"``, ``"DOWN_ARROW"``,
            ``"BLOCK_FULL"``, ``"BLOCK_LIGHT"``).
        output: The destination stream (or `None`). Only
            ``getattr(output, "encoding", None)`` is read -- the stream
            itself is never written to or mutated.

    Returns:
        The Unicode glyph when `output`'s encoding can represent it (or has
        no declared encoding), otherwise the ASCII fallback.
    """
    unicode_glyph, ascii_glyph = _GLYPHS[name]
    encoding = getattr(output, "encoding", None)
    if stream_can_encode(encoding, unicode_glyph):
        return unicode_glyph
    return ascii_glyph


def to_subscript(n: int, output) -> str:
    """Render `n` as Unicode subscript digits, or plain ASCII digits.

    Args:
        n: The integer to render (e.g. a bimodal world-history duration).
        output: The destination stream (or `None`); see `glyph` for the
            encoding-probe contract.

    Returns:
        Unicode subscript characters when `output`'s stream can encode
        them, otherwise the plain ASCII `str(n)`. Both forms are exactly
        one character per digit (and per leading `-`), so this function is
        width-neutral by construction and needs no column-budget special
        casing anywhere it is used.
    """
    encoding = getattr(output, "encoding", None)
    chars = str(n)
    if stream_can_encode(encoding, _SUBSCRIPT_PROBE):
        return ''.join(_SUBSCRIPT_DIGITS.get(c, c) for c in chars)
    return chars
