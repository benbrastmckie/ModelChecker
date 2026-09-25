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
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path
from typing import Any, Dict, Optional

__all__ = [
    "BIMODAL_LOGIC_COMMIT",
    "BIMODAL_LOGIC_PATH",
    "LAKE",
    "PROBE_TIMEOUT_SECONDS",
    "SKIP_REASON",
    "resolve_bimodal_logic_path",
    "resolve_lake",
    "run_check_certificate",
    "probe",
]

# Hard timeout bound for the module-level probe, explicit in source rather than implicit in the
# test harness. See `context/patterns/bounded-build-waiter.md` for the general discipline this
# probe-then-run structure follows.
PROBE_TIMEOUT_SECONDS = 60

BIMODAL_LOGIC_COMMIT = "6529c6e853f1c29358a7e74a76055f64f68b7ff7"


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
    `None` if the process failed or timed out (the caller decides how to report that)."""
    try:
        result = subprocess.run(
            [LAKE, "exe", "check_certificate"],
            input=json.dumps(payload),
            capture_output=True,
            text=True,
            cwd=str(BIMODAL_LOGIC_PATH),
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return None
    if result.returncode != 0:
        return None
    line = result.stdout.strip().splitlines()[-1] if result.stdout.strip() else ""
    try:
        return json.loads(line)
    except (json.JSONDecodeError, IndexError):
        return None


def probe() -> Optional[str]:
    """Probe the binary once, under a hard timeout, before any real invocation. Returns an
    error string on failure, or `None` on success."""
    trivial = {
        "target": {"premises": [], "conclusions": [{"tag": "atom", "name": "p"}], "time": 0},
        "bx": [],
        "lassos": [{"back": [[]], "mid": [], "fwd": [[]]}],
    }
    verdict = run_check_certificate(trivial, PROBE_TIMEOUT_SECONDS)
    if verdict is None:
        return (
            f"`lake exe check_certificate` did not respond within {PROBE_TIMEOUT_SECONDS}s "
            "or failed to build"
        )
    if verdict.get("status") != "countermodel":
        return f"probe certificate produced unexpected verdict: {verdict!r}"
    return None


SKIP_REASON: Optional[str] = None
if BIMODAL_LOGIC_PATH is None:
    SKIP_REASON = (
        "BimodalLogic checkout not found (set BIMODAL_LOGIC_PATH or check out to "
        "~/Projects/BimodalLogic)"
    )
elif LAKE is None:
    SKIP_REASON = "`lake` not found on PATH"

if SKIP_REASON is None:
    SKIP_REASON = probe()
