"""Differential test: the certificate fixture corpus against `lake exe check_certificate`.

This is the mechanical discharge of `ADEQUACY.md` Section 5.3's periodicity obligation: the
fixture corpus's expected verdicts (adjudicated by `test_certificate_fixtures.py`'s
self-contained Python evaluator) must agree with `lake exe check_certificate`, the executable
built directly on the four `Decidable` instances `WitnessFamily.joint_countermodel` consumes
(`~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/WitnessFamily/Agreement.lean:232`).
Where the Lean predicates and the Python re-checker disagree, the Lean predicates are the
contract (ADEQUACY.md Section 5.3) -- a disagreement here is a Python-side defect by definition.

**Scope correction.** This module covers legs (i) (the Python re-checker) and (ii)
(`lake exe check_certificate`) of Section 7.3's A2-triangle test, but only on the fixture corpus
-- it does not build a live `BimodalStructure`/Z3 search, so it cannot exercise leg (iii)
(encoding completeness). The full three-leg triangle, including leg (iii), lives in
`test_certificate_a2_triangle.py`; see that module's docstring.

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

The checkout/`lake` resolution, the subprocess invocation, and the skip-reason computation
itself now live in the shared `bimodal/tests/_lean_check.py` helper -- this module only imports
them, so a second consumer needing the identical plumbing (`test_certificate_a2_triangle.py`)
does not duplicate it.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from model_checker.theory_lib.bimodal.semantic.certificate import recheck_json
from model_checker.theory_lib.bimodal.tests._lean_check import (
    PROTOCOL_FAILURE,
    SKIP_REASON,
    run_check_certificate as _run_check_certificate,
)

FIXTURES_DIR = Path(__file__).parent.parent / "fixtures" / "certificates"

# Hard timeout bound for this module's own per-fixture invocations, explicit in source rather
# than implicit in the test harness. The probe timeout lives with the shared helper.
PER_FIXTURE_TIMEOUT_SECONDS = 30

pytestmark = pytest.mark.skipif(SKIP_REASON is not None, reason=SKIP_REASON or "")


def _load_expected_verdicts() -> dict:
    with open(FIXTURES_DIR / "expected_verdicts.json") as f:
        return json.load(f)


def _fixture_files():
    return sorted(p for p in FIXTURES_DIR.glob("*.json") if p.name != "expected_verdicts.json")


class TestProtocolFailureIsLoud:
    """`PROTOCOL_FAILURE` must be `None` whenever this module runs at all (it is computed once,
    at `_lean_check`'s first import, before `pytestmark`'s `skipif` decides whether this module's
    tests run). A present, responding binary that disagrees with the trivial probe certificate's
    expected `"countermodel"` verdict is a protocol-level regression -- exactly the failure mode
    that once made this whole differential tier silently report clean skips (see `_lean_check`'s
    module docstring, M1) -- and must fail this assertion loudly rather than hide behind a skip.
    """

    def test_protocol_failure_is_none(self):
        assert PROTOCOL_FAILURE is None, (
            "the BimodalLogic binary answered the trivial probe certificate, but not with "
            f"the expected 'countermodel' status -- protocol disagreement: {PROTOCOL_FAILURE}"
        )


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
    never `rejected` -- ADEQUACY.md Section 6.1's protocol-vs-condition distinction. Checked on
    *both* sides: the Lean binary and this theory's own JSON-boundary wrapper, `recheck_json`
    (`semantic/certificate.py`), which cannot be exercised by `recheck` directly since `recheck`
    takes an already-decoded, already-typed target time and so never sees a raw payload that
    could be missing either field."""

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
        assert recheck_json(payload)["status"] == "error", (
            "the Python-side recheck_json must agree with the Lean side on this payload"
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
        assert recheck_json(payload)["status"] == "error", (
            "the Python-side recheck_json must agree with the Lean side on this payload"
        )


class TestPythonRecheckerAgreesWithLean:
    """Direct agreement, on the whole fixture corpus, between this theory's own re-checker
    (`recheck_json`, decoding through the same `WitnessFamily`/`LabelledLasso` datatypes the Z3
    encoding will build) and `lake exe check_certificate`. `TestLeanAgreement` above compares the
    Lean verdict against `expected_verdicts.json`, itself adjudicated by an independent,
    checker-agnostic evaluator (`tests/unit/test_certificate_fixtures.py`); this class instead
    exercises the theory's actual re-checker end to end, which is the object the periodicity
    obligation (ADEQUACY.md section 5.3) is about."""

    @pytest.mark.parametrize("fixture_path", _fixture_files(), ids=lambda p: p.name)
    def test_recheck_json_status_matches_lean(self, fixture_path):
        with open(fixture_path) as f:
            payload = json.load(f)

        lean_verdict = _run_check_certificate(payload, PER_FIXTURE_TIMEOUT_SECONDS)
        assert lean_verdict is not None, (
            f"{fixture_path.name}: lake exe check_certificate did not respond within "
            f"{PER_FIXTURE_TIMEOUT_SECONDS}s"
        )
        python_verdict = recheck_json(payload)
        assert python_verdict["status"] == lean_verdict["status"], (
            f"{fixture_path.name}: recheck_json says {python_verdict['status']!r}, "
            f"lake exe check_certificate says {lean_verdict['status']!r} -- the Lean predicates "
            "are the contract, so this is a Python-side defect, not a Lean-side one"
        )
        if lean_verdict["status"] == "rejected":
            python_conditions = {entry.get("condition") for entry in python_verdict.get("failed", [])}
            lean_conditions = {entry.get("condition") for entry in lean_verdict.get("failed", [])}
            assert python_conditions & lean_conditions, (
                f"{fixture_path.name}: recheck_json's failed condition(s) {python_conditions!r} "
                f"share nothing with Lean's {lean_conditions!r}"
            )
