"""Differential test: the certificate fixture corpus against `lake exe check_certificate`.

This is the mechanical discharge of `ADEQUACY.md` Section 5.3's periodicity obligation and
Section 7.3's A2-triangle test's re-checker leg: the fixture corpus's expected verdicts
(adjudicated by `test_certificate_fixtures.py`'s self-contained Python evaluator) must agree with
`lake exe check_certificate`, the executable built directly on the four `Decidable` instances
`WitnessFamily.joint_countermodel` consumes
(`~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/WitnessFamily/Agreement.lean:232`).
Where the Lean predicates and the Python re-checker disagree, the Lean predicates are the
contract (ADEQUACY.md Section 5.3) -- a disagreement here is a Python-side defect by definition.

**Agreement observed against BimodalLogic commit**: `6529c6e853f1c29358a7e74a76055f64f68b7ff7`
(2026-09-24T22:21:44-07:00). Re-run this module after updating the BimodalLogic checkout to
confirm the corpus still agrees; a disagreement after an update is a signal that either the
corpus's expected verdicts or the Lean side's decision procedure changed shape.

This module resolves the BimodalLogic checkout from the `BIMODAL_LOGIC_PATH` environment
variable first, then `~/Projects/BimodalLogic`, and resolves `lake` via `PATH`. It skips the
whole module -- cleanly, with a named reason, never a failure -- if either is unavailable, or if
a bounded probe of `lake exe check_certificate` does not succeed within the module's hard
timeout. See `context/patterns/bounded-build-waiter.md` for the general discipline this module's
probe-then-run structure follows.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

FIXTURES_DIR = Path(__file__).parent.parent / "fixtures" / "certificates"

# Hard timeout bounds, explicit in source rather than implicit in the test harness.
PROBE_TIMEOUT_SECONDS = 60
PER_FIXTURE_TIMEOUT_SECONDS = 30

BIMODAL_LOGIC_COMMIT = "6529c6e853f1c29358a7e74a76055f64f68b7ff7"


def _resolve_bimodal_logic_path() -> Path | None:
    env_path = os.environ.get("BIMODAL_LOGIC_PATH")
    if env_path:
        candidate = Path(env_path).expanduser()
    else:
        candidate = Path("~/Projects/BimodalLogic").expanduser()
    if candidate.is_dir() and (candidate / "lakefile.toml").is_file():
        return candidate
    return None


def _resolve_lake() -> str | None:
    return shutil.which("lake")


BIMODAL_LOGIC_PATH = _resolve_bimodal_logic_path()
LAKE = _resolve_lake()

_SKIP_REASON: str | None = None
if BIMODAL_LOGIC_PATH is None:
    _SKIP_REASON = (
        "BimodalLogic checkout not found (set BIMODAL_LOGIC_PATH or check out to "
        "~/Projects/BimodalLogic)"
    )
elif LAKE is None:
    _SKIP_REASON = "`lake` not found on PATH"


def _run_check_certificate(payload: dict, timeout: int) -> dict | None:
    """Run `lake exe check_certificate` on one JSON payload. Returns the parsed verdict, or
    None if the process failed or timed out (the caller decides how to report that)."""
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


def _probe() -> str | None:
    """Probe the binary once, under a hard timeout, before the fixture loop. Returns an error
    string on failure, or None on success."""
    trivial = {
        "target": {"premises": [], "conclusions": [{"tag": "atom", "name": "p"}], "time": 0},
        "bx": [],
        "lassos": [{"back": [[]], "mid": [], "fwd": [[]]}],
    }
    verdict = _run_check_certificate(trivial, PROBE_TIMEOUT_SECONDS)
    if verdict is None:
        return (
            f"`lake exe check_certificate` did not respond within {PROBE_TIMEOUT_SECONDS}s "
            "or failed to build"
        )
    if verdict.get("status") != "countermodel":
        return f"probe certificate produced unexpected verdict: {verdict!r}"
    return None


if _SKIP_REASON is None:
    _SKIP_REASON = _probe()

pytestmark = pytest.mark.skipif(_SKIP_REASON is not None, reason=_SKIP_REASON or "")


def _load_expected_verdicts() -> dict:
    with open(FIXTURES_DIR / "expected_verdicts.json") as f:
        return json.load(f)


def _fixture_files():
    return sorted(p for p in FIXTURES_DIR.glob("*.json") if p.name != "expected_verdicts.json")


class TestLeanAgreement:
    """Every fixture's verdict, decided by `lake exe check_certificate`, must agree with
    `expected_verdicts.json` on `status` and, where recorded, on `condition`."""

    @pytest.mark.parametrize("fixture_path", _fixture_files(), ids=lambda p: p.name)
    def test_lean_verdict_matches_expected(self, fixture_path):
        expected = _load_expected_verdicts()[fixture_path.name]
        with open(fixture_path) as f:
            payload = json.load(f)

        verdict = _run_check_certificate(payload, PER_FIXTURE_TIMEOUT_SECONDS)
        assert verdict is not None, (
            f"{fixture_path.name}: lake exe check_certificate did not respond within "
            f"{PER_FIXTURE_TIMEOUT_SECONDS}s"
        )
        assert verdict["status"] == expected["status"], (
            f"{fixture_path.name}: Lean says status {verdict['status']!r}, "
            f"corpus expects {expected['status']!r} -- the Lean predicates are the contract, "
            "so this is a Python-side (fixture or evaluator) defect, not a Lean-side one"
        )
        if expected["status"] != "countermodel" and "condition" in expected:
            failed = verdict.get("failed") or []
            conditions = {entry.get("condition") for entry in failed}
            assert expected["condition"] in conditions, (
                f"{fixture_path.name}: expected condition {expected['condition']!r} among "
                f"Lean's reported conditions {conditions!r}"
            )


class TestErrorPaths:
    """A certificate missing `target`, or missing `target.time`, must be answered `error`,
    never `rejected` -- ADEQUACY.md Section 6.1's protocol-vs-condition distinction."""

    def test_missing_target_is_error(self):
        payload = {
            "bx": [],
            "lassos": [{"back": [[]], "mid": [], "fwd": [[]]}],
        }
        verdict = _run_check_certificate(payload, PER_FIXTURE_TIMEOUT_SECONDS)
        assert verdict is not None, "lake exe check_certificate did not respond in time"
        assert verdict["status"] == "error", (
            f"a certificate missing 'target' must be 'error', got {verdict!r}"
        )

    def test_missing_target_time_is_error(self):
        payload = {
            "target": {"premises": [], "conclusions": []},
            "bx": [],
            "lassos": [{"back": [[]], "mid": [], "fwd": [[]]}],
        }
        verdict = _run_check_certificate(payload, PER_FIXTURE_TIMEOUT_SECONDS)
        assert verdict is not None, "lake exe check_certificate did not respond in time"
        assert verdict["status"] == "error", (
            f"a certificate missing 'target.time' must be 'error', got {verdict!r}"
        )
