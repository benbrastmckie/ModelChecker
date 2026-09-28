"""Shared `lake exe check_certificate` invocation and skip-resolution helper.

Extracted from `test_certificate_lean_agreement.py` once a second consumer
(`test_certificate_a2_triangle.py`, `docs/ADEQUACY.md` section 7.3's A2-triangle Tier 2 leg)
needed the identical BimodalLogic-checkout resolution, `lake` resolution, subprocess invocation,
and skip-reason computation. Every name below is exported under a public spelling -- no leading
underscore -- since other modules are meant to import them.

Resolves the BimodalLogic checkout from the `BIMODAL_LOGIC_PATH` environment variable first, then
`~/Projects/BimodalLogic`, and resolves `lake` via `PATH`. `SKIP_REASON` is computed once, at this
module's first import: `None` if the checkout, `lake`, and a bounded probe of `lake exe
check_certificate` all succeed, else a named reason a consumer can pass straight to
`pytest.mark.skipif`.

**Runs once per session, not once per consuming module.** The module-level probe used to be a
private copy inside `test_certificate_lean_agreement.py`, re-run every time that module was
imported. Since Python caches module imports, every consumer importing this module now shares
the single probe run performed at this module's own first import -- one subprocess invocation
per pytest session across every consumer, not one per consumer.

**Environment absence versus protocol failure.** `SKIP_REASON` and `PROTOCOL_FAILURE` are two
separate vocabularies, deliberately not folded into one, because conflating them once deleted
this whole differential tier silently: an upstream migration to a strict canonical-bytes parser
(BimodalLogic commit `12be620c2`) began rejecting this repository's non-canonical `json.dumps`
whitespace, the probe saw `{"status": "error", ...}`, the old single-vocabulary `probe()` folded
that into `SKIP_REASON`, and every differential test module reported a clean skip -- with a
present checkout and a working binary -- for as long as that regression went unnoticed.
`SKIP_REASON` covers **environment absence only**: no checkout, no `lake`, or a binary that never
answers within the probe timeout (unresponsive or unbuildable) -- conditions where skipping is
the only sane thing to do, since there is nothing to test against. `PROTOCOL_FAILURE` covers a
binary that **does** answer, but not with the `"countermodel"` status the trivial, well-formed
probe certificate below must produce -- a protocol disagreement between this repository and the
binary it is talking to, which must fail loudly rather than disappear as a skip. Exactly one of
the two is a skip condition for `pytest.mark.skipif`; `PROTOCOL_FAILURE` is asserted `None` by a
dedicated test instead (`test_certificate_lean_agreement.py`'s `TestErrorPaths`).

**Parse-echo verification (axis 2).** The Lean side parses the exported JSON, so a parser defect
could mean the verified side certifies a different certificate than the one this repository
exported. A `countermodel` or `rejected` verdict now carries an `"echo"` field -- a canonical
*reprint* of what the binary parsed, not a verbatim copy -- which `run_check_certificate_with_sent`
(returning the exact bytes sent alongside the verdict) and `assert_echo_matches_sent` exist to
compare bytewise. A mismatch is a protocol error, not a rejection: the two sides are talking about
different certificates.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

from model_checker.theory_lib.bimodal.semantic.certificate import canonical_wire_bytes

__all__ = [
    "BIMODAL_LOGIC_COMMIT",
    "BIMODAL_LOGIC_PATH",
    "LAKE",
    "PROBE_TIMEOUT_SECONDS",
    "PROTOCOL_FAILURE",
    "SKIP_REASON",
    "assert_echo_matches_sent",
    "resolve_bimodal_logic_path",
    "resolve_lake",
    "run_check_certificate",
    "run_check_certificate_with_sent",
    "probe",
]

# Hard timeout bound for the module-level probe, explicit in source rather than implicit in the
# test harness. See `context/patterns/bounded-build-waiter.md` for the general discipline this
# probe-then-run structure follows.
PROBE_TIMEOUT_SECONDS = 60

BIMODAL_LOGIC_COMMIT = "d55e2760e6731a2240f3db5d761658947bf69125"


def resolve_bimodal_logic_path() -> Optional[Path]:
    """The BimodalLogic checkout directory, or `None` if it cannot be found."""
    env_path = os.environ.get("BIMODAL_LOGIC_PATH")
    if env_path:
        candidate = Path(env_path).expanduser()
    else:
        candidate = Path("~/Projects/BimodalLogic").expanduser()
    if candidate.is_dir() and (candidate / "lakefile.toml").is_file():
        return candidate
    return None


def resolve_lake() -> Optional[str]:
    """The `lake` executable path, or `None` if it is not on `PATH`."""
    return shutil.which("lake")


BIMODAL_LOGIC_PATH = resolve_bimodal_logic_path()
LAKE = resolve_lake()


def run_check_certificate(payload: Dict[str, Any], timeout: int) -> Optional[Dict[str, Any]]:
    """Run `lake exe check_certificate` on one JSON payload. Returns the parsed verdict, or
    `None` if the process failed or timed out (the caller decides how to report that).

    Thin wrapper over `run_check_certificate_with_sent`, keeping this function's return shape
    exactly as it was before axis 2 (parse-echo verification) needed the sent bytes too -- the
    three pre-existing consumers (`test_certificate_lean_agreement.py`,
    `test_certificate_a2_triangle.py`, `test_semantics_core.py`) import this name unchanged.
    """
    verdict, _sent = run_check_certificate_with_sent(payload, timeout)
    return verdict


def run_check_certificate_with_sent(
    payload: Dict[str, Any], timeout: int
) -> Tuple[Optional[Dict[str, Any]], str]:
    """Run `lake exe check_certificate` on one JSON payload, returning `(verdict, sent)` --
    `sent` is the exact canonical bytes written to the binary's stdin, needed by
    `assert_echo_matches_sent` for axis 2's parse-echo comparison: the Lean side's `"echo"` field
    must match *this* string bytewise, not merely `json.dumps(payload)` recomputed after the
    fact, since a caller might otherwise recompute it with different `json.dumps` arguments than
    what was actually sent."""
    sent = canonical_wire_bytes(payload)
    try:
        result = subprocess.run(
            [LAKE, "exe", "check_certificate"],
            input=sent,
            capture_output=True,
            text=True,
            cwd=str(BIMODAL_LOGIC_PATH),
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return None, sent
    if result.returncode != 0:
        return None, sent
    line = result.stdout.strip().splitlines()[-1] if result.stdout.strip() else ""
    try:
        return json.loads(line), sent
    except (json.JSONDecodeError, IndexError):
        return None, sent


def assert_echo_matches_sent(verdict: Dict[str, Any], sent: str) -> None:
    """Assert axis 2's parse-echo comparison: the Lean side must echo back exactly what it
    parsed, and that echo must match the canonical bytes this repository actually sent --
    bytewise, modulo surrounding whitespace only (the producer's own trailing newline), never
    modulo interior whitespace (canonical bytes have none to begin with, per Phase 1).

    `"echo"` appears on `countermodel` and `rejected` verdicts; `"error"` never carries one (a
    wire-level parse failure has nothing to echo). A mismatch, or a missing `"echo"` where one is
    expected, is classified as a **protocol error** in the same PROTOCOL_FAILURE-grade vocabulary
    the environment-versus-protocol split (`probe`, module docstring) established -- never a
    `"rejected"`-shaped outcome, and never a fixture-corpus disagreement: the task description's
    own discipline is that a mismatch means the two sides are talking about different
    certificates, which is a protocol failure by definition, not a semantic one.
    """
    status = verdict.get("status")
    if status == "error":
        assert "echo" not in verdict, (
            f"protocol error: an 'error' verdict must never carry an 'echo' field (a wire-level "
            f"parse failure has nothing to echo), got {verdict!r}"
        )
        return
    echo = verdict.get("echo")
    assert echo is not None, (
        f"protocol error: a {status!r} verdict is missing its 'echo' field -- this repository "
        f"cannot confirm the verified side parsed the certificate it was actually sent, "
        f"verdict={verdict!r}"
    )
    assert echo.strip() == sent.strip(), (
        "protocol error: the Lean side's echo of what it parsed does not match the canonical "
        "bytes this repository sent -- the two sides are talking about different certificates. "
        "This bytewise comparison holds only because this repository already emits canonical "
        "key order (WitnessFamily.to_json/formula.to_json insertion order); a mismatch may "
        "signal a key-order or escaping regression in this repository's own exporter rather "
        f"than a Lean-side defect.\nsent: {sent!r}\necho: {echo!r}"
    )


def probe() -> Tuple[Optional[str], Optional[str]]:
    """Probe the binary once, under a hard timeout, before any real invocation.

    Returns `(skip_reason, protocol_failure)`; at most one is non-`None`, and both are `None` on
    success. `skip_reason` covers a binary that never answers within the timeout -- unresponsive
    or unbuildable, an environment condition safe to skip. `protocol_failure` covers a binary
    that *does* answer, but not with the `"countermodel"` status this trivial, well-formed probe
    certificate must produce -- a protocol disagreement (see module docstring's M1 account),
    which is reported separately rather than folded into `skip_reason`.
    """
    trivial = {
        "target": {"premises": [], "conclusions": [{"tag": "atom", "name": "p"}], "time": 0},
        "bx": [],
        "lassos": [{"back": [[]], "mid": [], "fwd": [[]]}],
    }
    verdict = run_check_certificate(trivial, PROBE_TIMEOUT_SECONDS)
    if verdict is None:
        return (
            f"`lake exe check_certificate` did not respond within {PROBE_TIMEOUT_SECONDS}s "
            "or failed to build",
            None,
        )
    if verdict.get("status") != "countermodel":
        return None, f"probe certificate produced unexpected verdict: {verdict!r}"
    return None, None


SKIP_REASON: Optional[str] = None
PROTOCOL_FAILURE: Optional[str] = None
if BIMODAL_LOGIC_PATH is None:
    SKIP_REASON = (
        "BimodalLogic checkout not found (set BIMODAL_LOGIC_PATH or check out to "
        "~/Projects/BimodalLogic)"
    )
elif LAKE is None:
    SKIP_REASON = "`lake` not found on PATH"

if SKIP_REASON is None:
    SKIP_REASON, PROTOCOL_FAILURE = probe()
