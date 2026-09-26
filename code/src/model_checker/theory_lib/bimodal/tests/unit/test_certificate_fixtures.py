"""Fixture-driven tests for the witness-family certificate decoder/evaluator.

The decoder and evaluator (`parse_formula`, `Lasso`, `Certificate`, `coherent_at`,
`box_faithful`, `decide`, etc.) live in `_certificate_model.py`, relocated there (not
duplicated) so that `test_formula.py` can import the identical, independent decoder for its
label-family differential property test. This module imports that model via
`importlib.util.spec_from_file_location` against the sibling file's own path, since
`pyproject.toml`'s `--import-mode=importlib` does not add `tests/unit/` to `sys.path` for a
plain `import _certificate_model`. See `tests/fixtures/certificates/README.md` for the corpus
and the window-discriminating fixture's construction, and `_certificate_model.py`'s own
docstring for the decoding/window-bounds detail.
"""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest

FIXTURES_DIR = Path(__file__).parent.parent / "fixtures" / "certificates"


def _load_certificate_model():
    path = Path(__file__).parent / "_certificate_model.py"
    spec = importlib.util.spec_from_file_location("_certificate_model", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_certificate_model = _load_certificate_model()

FORMULA_TAGS = _certificate_model.FORMULA_TAGS
parse_formula = _certificate_model.parse_formula
parse_label = _certificate_model.parse_label
subformulas = _certificate_model.subformulas
closure_of = _certificate_model.closure_of
BOT = _certificate_model.BOT
Lasso = _certificate_model.Lasso
Certificate = _certificate_model.Certificate
coherent_at = _certificate_model.coherent_at
local_coherent_over = _certificate_model.local_coherent_over
fulfil_at = _certificate_model.fulfil_at
fulfilling_over = _certificate_model.fulfilling_over
box_faithful = _certificate_model.box_faithful
target_holds = _certificate_model.target_holds
decide = _certificate_model.decide


# ---------------------------------------------------------------------------
# Fixture loading
# ---------------------------------------------------------------------------


def _load_expected_verdicts() -> dict:
    with open(FIXTURES_DIR / "expected_verdicts.json") as f:
        return json.load(f)


def _fixture_files():
    return sorted(p for p in FIXTURES_DIR.glob("*.json") if p.name != "expected_verdicts.json")


EXPECTED = _load_expected_verdicts()
FIXTURE_FILES = _fixture_files()


@pytest.fixture(params=FIXTURE_FILES, ids=lambda p: p.name)
def fixture_path(request):
    return request.param


class TestCertificateFixtures:
    """Every fixture's expected verdict, decided by the self-contained evaluator alone."""

    def test_verdict_matches_expected(self, fixture_path):
        with open(fixture_path) as f:
            raw = json.load(f)
        cert = Certificate(raw)
        verdict = decide(cert)
        expected = EXPECTED[fixture_path.name]

        assert verdict["status"] == expected["status"], (
            f"{fixture_path.name}: expected status {expected['status']!r}, got {verdict['status']!r}"
        )
        if expected["status"] == "countermodel":
            assert verdict["time"] == expected["time"]
        else:
            assert verdict["condition"] == expected["condition"], (
                f"{fixture_path.name}: expected condition {expected['condition']!r}, "
                f"got {verdict.get('condition')!r}"
            )
            if expected.get("position") is not None:
                assert verdict["position"] == expected["position"], (
                    f"{fixture_path.name}: expected position {expected['position']!r}, "
                    f"got {verdict.get('position')!r}"
                )

    def test_every_fixture_parses_as_wire_format(self, fixture_path):
        with open(fixture_path) as f:
            raw = json.load(f)

        assert "target" in raw, f"{fixture_path.name}: missing target"
        assert "time" in raw["target"], f"{fixture_path.name}: missing target.time"

        for lasso in raw["lassos"]:
            assert lasso["back"], f"{fixture_path.name}: back must be non-empty"
            assert lasso["fwd"], f"{fixture_path.name}: fwd must be non-empty"
            for segment_name in ("back", "mid", "fwd"):
                for label in lasso.get(segment_name, []):
                    assert isinstance(label, list), (
                        f"{fixture_path.name}: {segment_name} label must be a list"
                    )
                    for formula in label:
                        assert formula["tag"] in FORMULA_TAGS, (
                            f"{fixture_path.name}: unknown tag {formula.get('tag')!r}"
                        )
                        # Atom identity is base-only (Formula.toJson drops Atom.freshIndex):
                        # a fixture carrying a fresh-indexed atom is malformed.
                        if formula["tag"] == "atom":
                            assert set(formula.keys()) <= {"tag", "name"}, (
                                f"{fixture_path.name}: atom carries unexpected fields "
                                f"(possible fresh index): {formula!r}"
                            )


class TestWindowDiscrimination:
    """The window-discriminating fixture must genuinely discriminate: the wide (proved) window
    catches the violation the narrow (one-period) window misses."""

    FIXTURE_NAME = "04_window_discriminator_coherence.json"

    def _load(self):
        with open(FIXTURES_DIR / self.FIXTURE_NAME) as f:
            raw = json.load(f)
        return Certificate(raw)

    def test_narrow_window_misses_the_violation(self):
        cert = self._load()
        lasso = cert.lassos[0]
        ok, pos = local_coherent_over(cert, lasso, lasso.narrow_window())
        assert ok, (
            "the narrow (one-period) window was expected to find no violation "
            f"(that is the unsoundness this fixture demonstrates); found one at {pos}"
        )

    def test_wide_window_catches_the_violation_in_the_outer_band(self):
        cert = self._load()
        lasso = cert.lassos[0]
        ok, pos = local_coherent_over(cert, lasso, lasso.coherence_window())
        assert not ok, "the wide (proved) window was expected to find the violation"
        outer_band_lo, outer_band_hi = -2 * lasso.nb, -lasso.nb
        assert outer_band_lo <= pos < outer_band_hi, (
            f"expected the violation inside the outer band [{outer_band_lo}, {outer_band_hi}), "
            f"got position {pos}"
        )
        expected = EXPECTED[self.FIXTURE_NAME]
        assert pos == expected["position"]

    def test_assertion_genuinely_fails_if_window_is_narrowed(self):
        """Confirms the discriminating assertion is two-sided: deliberately checking the FULL
        wide window but pretending it is the narrow bound must disagree with the (correct)
        narrow-window result above -- i.e. narrowing the window parameter changes the verdict."""
        cert = self._load()
        lasso = cert.lassos[0]
        narrow_ok, _ = local_coherent_over(cert, lasso, lasso.narrow_window())
        wide_ok, _ = local_coherent_over(cert, lasso, lasso.coherence_window())
        assert narrow_ok != wide_ok, (
            "the window parameter must be load-bearing: narrowing it from the proved window "
            "to the one-period window must flip the verdict on this fixture"
        )
