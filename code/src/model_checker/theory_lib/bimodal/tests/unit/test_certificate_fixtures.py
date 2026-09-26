"""Self-contained decoder and evaluator for witness-family certificate fixtures.

This module is deliberately **independent of `model_checker.theory_lib.bimodal.semantic`** (and
of every other bimodal module): it is a from-scratch re-implementation of the wire format and the
four certificate conditions (C1)-(C4) described in
`code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`. Its purpose is to test the
*specification* the fixture corpus pins, not any particular encoder or re-checker built against
it. See `tests/fixtures/certificates/README.md` for the corpus and the window-discriminating
fixture's construction.

The decoding (`decode_label`) mirrors `Periodic.unrollOf` /
`~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/BiLasso/Periodic.lean`: strictly
negative positions read the `back` segment cyclically, `[0, |mid|)` reads `mid` directly, and
positions at or past `|mid|` read the `fwd` segment cyclically. Python's `%` operator agrees with
Lean's `Int.emod` for a positive modulus (both non-negative), so no adjustment is needed.

The window bounds mirror
`Metalogic/Decidability/WitnessFamily/Decide.lean`'s `coherent_iff_window` (`:335`),
`fulfil_iff_window` (`:743`) and `mem_all_iff_window` (`:809`, `:883`): local coherence and
fulfilment collapse to `[-2*nb, nm + 2*nf)`, box faithfulness to the narrower `[-nb, nm + nf)`.
The forward/backward witness scan bounds mirror `scan_forward` / `scan_backward`
(`Decide.lean:192, 212`).
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

FIXTURES_DIR = Path(__file__).parent.parent / "fixtures" / "certificates"

FORMULA_TAGS = {"atom", "bot", "imp", "box", "untl", "snce"}


# ---------------------------------------------------------------------------
# Formula representation and parsing
# ---------------------------------------------------------------------------
# A formula is represented as an immutable tuple:
#   ("atom", name)
#   ("bot",)
#   ("imp", left, right)
#   ("box", child)
#   ("untl", guard, event)
#   ("snce", guard, event)
# where `left`/`right`/`child`/`guard`/`event` are themselves formula tuples. Guard-first,
# matching `semantic.formula.Untl`/`Snce`'s own field order -- this module is independent of
# that module (see the file docstring), but keeps the same positional convention rather than
# putting two different orders in the same field of view once `test_formula.py` imports this
# decoder.


def parse_formula(obj: dict) -> tuple:
    """Parse one wire-format formula object into its internal tuple representation.

    Raises ValueError on an unrecognized tag or a missing required field, rather than silently
    defaulting -- a malformed fixture should fail loudly, not decode into something else.
    """
    if not isinstance(obj, dict) or "tag" not in obj:
        raise ValueError(f"not a formula object: {obj!r}")
    tag = obj["tag"]
    if tag not in FORMULA_TAGS:
        raise ValueError(f"unknown formula tag: {tag!r}")
    if tag == "atom":
        return ("atom", obj["name"])
    if tag == "bot":
        return ("bot",)
    if tag == "imp":
        return ("imp", parse_formula(obj["left"]), parse_formula(obj["right"]))
    if tag == "box":
        return ("box", parse_formula(obj["child"]))
    if tag in ("untl", "snce"):
        return (tag, parse_formula(obj["guard"]), parse_formula(obj["event"]))
    raise AssertionError("unreachable")  # FORMULA_TAGS membership already checked above


def parse_label(label_list: list) -> frozenset:
    """A label is a list of formula objects, read as a set."""
    return frozenset(parse_formula(f) for f in label_list)


def subformulas(f: tuple) -> set:
    """The subformula closure of a single formula, including itself."""
    out = {f}
    tag = f[0]
    if tag == "imp":
        out |= subformulas(f[1])
        out |= subformulas(f[2])
    elif tag == "box":
        out |= subformulas(f[1])
    elif tag in ("untl", "snce"):
        out |= subformulas(f[1])
        out |= subformulas(f[2])
    return out


def closure_of(formulas) -> set:
    """The subformula closure of a collection of formulas."""
    out: set = set()
    for f in formulas:
        out |= subformulas(f)
    return out


BOT = ("bot",)


# ---------------------------------------------------------------------------
# The certificate datatype
# ---------------------------------------------------------------------------


class Lasso:
    """A parsed `LabelledLasso`: three label segments plus the decoded, cached label function."""

    def __init__(self, back: list, mid: list, fwd: list):
        if not back:
            raise ValueError("back must be non-empty (LabelledLasso.back_ne)")
        if not fwd:
            raise ValueError("fwd must be non-empty (LabelledLasso.fwd_ne)")
        self.back = [parse_label(x) for x in back]
        self.mid = [parse_label(x) for x in mid]
        self.fwd = [parse_label(x) for x in fwd]
        self.nb = len(self.back)
        self.nm = len(self.mid)
        self.nf = len(self.fwd)

    def lab(self, t: int) -> frozenset:
        """Decode the label at integer position `t`, exactly mirroring `Periodic.unrollOf`."""
        if t < 0:
            return self.back[t % self.nb]
        if t < self.nm:
            return self.mid[t]
        return self.fwd[(t - self.nm) % self.nf]

    # Window bounds (Decide.lean's collapse results) -----------------------------------

    def coherence_window(self) -> range:
        """`[-2*nb, nm + 2*nf)` -- the proved window for local coherence and fulfilment."""
        return range(-2 * self.nb, self.nm + 2 * self.nf)

    def narrow_window(self) -> range:
        """`[-nb, nm + nf)` -- the (unsound, for coherence/fulfilment) one-period window."""
        return range(-self.nb, self.nm + self.nf)

    def box_window(self) -> range:
        """`[-nb, nm + nf)` -- the proved window for box faithfulness (one period each side)."""
        return range(-self.nb, self.nm + self.nf)

    def scan_forward_bound(self, t: int) -> int:
        """`max(t, nm) + nf` -- the corrected forward witness-scan bound (`scan_forward`)."""
        return max(t, self.nm) + self.nf

    def scan_backward_bound(self, t: int) -> int:
        """`min(t, 0) - nb` -- the corrected backward witness-scan bound (`scan_backward`)."""
        return min(t, 0) - self.nb


class Certificate:
    """A parsed witness-family certificate: box guess, lassos, and the target."""

    def __init__(self, raw: dict):
        target = raw["target"]
        if "time" not in target:
            raise ValueError("target.time is required (no default)")
        self.premises = [parse_formula(f) for f in target.get("premises", [])]
        self.conclusions = [parse_formula(f) for f in target.get("conclusions", [])]
        self.time = target["time"]

        self.bx: dict = {}
        for entry in raw.get("bx", []):
            formula, value = entry
            self.bx[parse_formula(formula)] = bool(value)

        raw_lassos = raw["lassos"]
        if not raw_lassos:
            raise ValueError("lassos must be non-empty")
        self.lassos = [Lasso(l["back"], l.get("mid", []), l["fwd"]) for l in raw_lassos]

        self.closure = closure_of(
            self.premises
            + self.conclusions
            + list(self.bx.keys())
            + [f for lasso in self.lassos for label in (lasso.back + lasso.mid + lasso.fwd) for f in label]
        )

    def bx_of(self, chi: tuple) -> bool:
        return self.bx.get(chi, False)


# ---------------------------------------------------------------------------
# (C1) Local coherence, at a single position
# ---------------------------------------------------------------------------


def coherent_at(cert: Certificate, lasso: Lasso, t: int) -> tuple:
    """Evaluate (C1) at position `t` of `lasso`. Returns (ok, failing_formula_or_None)."""
    L = lasso.lab(t)
    if BOT in L:
        return False, BOT
    for f in cert.closure:
        tag = f[0]
        if tag in ("atom", "bot"):
            continue  # atoms are deliberately unconstrained; bot handled above
        if tag == "imp":
            _, a, b = f
            lhs = f in L
            rhs = (a not in L) or (b in L)
            if lhs != rhs:
                return False, f
        elif tag == "box":
            _, chi = f
            lhs = f in L
            rhs = cert.bx_of(chi)
            if lhs != rhs:
                return False, f
        elif tag == "untl":
            _, guard, event = f
            lhs = f in L
            Lnext = lasso.lab(t + 1)
            rhs = (event in Lnext) or (guard in Lnext and f in Lnext)
            if lhs != rhs:
                return False, f
        elif tag == "snce":
            _, guard, event = f
            lhs = f in L
            Lprev = lasso.lab(t - 1)
            rhs = (event in Lprev) or (guard in Lprev and f in Lprev)
            if lhs != rhs:
                return False, f
    return True, None


def local_coherent_over(cert: Certificate, lasso: Lasso, window: range):
    """Check (C1) over every position in `window`. Returns (ok, failing_position_or_None)."""
    for t in window:
        ok, _ = coherent_at(cert, lasso, t)
        if not ok:
            return False, t
    return True, None


# ---------------------------------------------------------------------------
# (C2) Fulfilment, at a single position
# ---------------------------------------------------------------------------


def fulfil_at(cert: Certificate, lasso: Lasso, t: int) -> tuple:
    """Evaluate (C2) at position `t` of `lasso`. Returns (ok, failing_formula_or_None)."""
    L = lasso.lab(t)
    for f in cert.closure:
        tag = f[0]
        if tag == "untl":
            if f not in L:
                continue
            _, guard, event = f
            hi = lasso.scan_forward_bound(t)
            found = False
            for s in range(t + 1, hi + 1):
                if event in lasso.lab(s):
                    if all(guard in lasso.lab(r) for r in range(t + 1, s)):
                        found = True
                        break
            if not found:
                return False, f
        elif tag == "snce":
            if f not in L:
                continue
            _, guard, event = f
            lo = lasso.scan_backward_bound(t)
            found = False
            for s in range(t - 1, lo - 1, -1):
                if event in lasso.lab(s):
                    if all(guard in lasso.lab(r) for r in range(s + 1, t)):
                        found = True
                        break
            if not found:
                return False, f
    return True, None


def fulfilling_over(cert: Certificate, lasso: Lasso, window: range):
    """Check (C2) over every position in `window`. Returns (ok, failing_position_or_None)."""
    for t in window:
        ok, _ = fulfil_at(cert, lasso, t)
        if not ok:
            return False, t
    return True, None


# ---------------------------------------------------------------------------
# (C3) Box faithfulness
# ---------------------------------------------------------------------------


def box_faithful(cert: Certificate):
    """Check (C3) across every lasso, using each lasso's own one-period window.

    Returns (ok, failing_box_formula_or_None).
    """
    box_formulas = [f for f in cert.closure if f[0] == "box"]
    for f in box_formulas:
        _, chi = f
        guess = cert.bx_of(chi)
        actual = all(
            chi in lasso.lab(t) for lasso in cert.lassos for t in lasso.box_window()
        )
        if guess != actual:
            return False, f
    return True, None


# ---------------------------------------------------------------------------
# (C4) Target
# ---------------------------------------------------------------------------


def target_holds(cert: Certificate) -> bool:
    main = cert.lassos[0]
    L0 = main.lab(cert.time)
    return all(g in L0 for g in cert.premises) and all(s not in L0 for s in cert.conclusions)


# ---------------------------------------------------------------------------
# Aggregate decision, mirroring `check_certificate`'s verdict vocabulary
# ---------------------------------------------------------------------------


def decide(cert: Certificate) -> dict:
    """Decide (C1)-(C4) over the proved windows. Returns a verdict dict shaped like the wire
    protocol's output (never a validity claim -- see ADEQUACY.md Section 6.1)."""
    for i, lasso in enumerate(cert.lassos):
        ok, pos = local_coherent_over(cert, lasso, lasso.coherence_window())
        if not ok:
            return {"status": "rejected", "condition": "local_coherent", "lasso": i, "position": pos}
    for i, lasso in enumerate(cert.lassos):
        ok, pos = fulfilling_over(cert, lasso, lasso.coherence_window())
        if not ok:
            return {"status": "rejected", "condition": "fulfilling", "lasso": i, "position": pos}
    ok, _ = box_faithful(cert)
    if not ok:
        return {"status": "rejected", "condition": "box_faithful", "lasso": None, "position": None}
    if not target_holds(cert):
        return {"status": "rejected", "condition": "target", "lasso": 0, "position": cert.time}
    return {"status": "countermodel", "time": cert.time}


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
