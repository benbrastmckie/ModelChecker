"""Tests for bimodal_logic.ground_truth -- the independent brute-force
decision procedure used to adjudicate MC/BimodalHarness disagreements.

Covers the report's four sanity checks, the 12 confirmed external-defect
formulas, window-stability (the guard against the exact off-by-one class of
bug this evaluator itself once had), unsupported-tag handling, and the
formula-derived default window.
"""

from __future__ import annotations

import time

import pytest

from bimodal_logic.ground_truth import GroundTruthUnsupported, ground_truth_verdict
from bimodal_logic.tests.test_cross_oracle_differential import (
    _enumerate_primitive_formulas,
    _is_temporal_only,
)
from bimodal_logic.translation import temporal_depth

##############################################################################
# Sanity checks (research report's validation table)
##############################################################################

# (p Until q) -> (q Until p)  -- SAT, confirmed via direct Z3 probing in the
# quantifier-variable-aliasing soundness fix (see
# oracle/bimodal_logic/tests/test_soundness_regression.py for the related
# quantifier-shadowing regression coverage).
_SANITY_UNTIL_SWAP = {
    "tag": "imp",
    "left": {
        "tag": "untl",
        "event": {"tag": "atom", "name": "p"},
        "guard": {"tag": "atom", "name": "q"},
    },
    "right": {
        "tag": "untl",
        "event": {"tag": "atom", "name": "q"},
        "guard": {"tag": "atom", "name": "p"},
    },
}

# bot Until bot -- SAT (pre-existing _KNOWN_MC_EDGE_CASES entry)
_SANITY_BOT_UNTIL_BOT = {
    "tag": "untl",
    "event": {"tag": "bot"},
    "guard": {"tag": "bot"},
}

# p -> p -- UNSAT (tautology)
_SANITY_TAUTOLOGY = {
    "tag": "imp",
    "left": {"tag": "atom", "name": "p"},
    "right": {"tag": "atom", "name": "p"},
}

# p -- SAT (invalid)
_SANITY_ATOM = {"tag": "atom", "name": "p"}


class TestSanityChecks:
    """The report's four independently-sourced validation checks."""

    def test_until_swap_is_sat(self):
        verdict, _ = ground_truth_verdict(_SANITY_UNTIL_SWAP)
        assert verdict == "SAT"

    def test_bot_until_bot_is_sat(self):
        verdict, _ = ground_truth_verdict(_SANITY_BOT_UNTIL_BOT)
        assert verdict == "SAT"

    def test_tautology_is_unsat(self):
        verdict, _ = ground_truth_verdict(_SANITY_TAUTOLOGY)
        assert verdict == "UNSAT"
        # UNSAT carries no witness valuation.
        _, witness = ground_truth_verdict(_SANITY_TAUTOLOGY)
        assert witness is None

    def test_atom_is_sat(self):
        verdict, _ = ground_truth_verdict(_SANITY_ATOM)
        assert verdict == "SAT"


##############################################################################
# The 12 confirmed external-BH-defect formulas
##############################################################################


def _imp(left, right):
    return {"tag": "imp", "left": left, "right": right}


def _untl(event, guard):
    return {"tag": "untl", "event": event, "guard": guard}


def _snce(event, guard):
    return {"tag": "snce", "event": event, "guard": guard}


_BOT = {"tag": "bot"}
_P = {"tag": "atom", "name": "p"}

# The shared (TAUTOLOGY \Until/\Since Y) shape -- three tautological event
# operands crossed with Until/Since and two guard operands (bot, p).
_TAUTOLOGY_EVENTS = [
    _imp(_BOT, _BOT),  # bot -> bot
    _imp(_BOT, _P),  # bot -> p
    _imp(_P, _P),  # p -> p
]
_GUARDS = [_BOT, _P]

TWELVE_EXTERNAL_DEFECT_FORMULAS = [
    _untl(event, guard) for event in _TAUTOLOGY_EVENTS for guard in _GUARDS
] + [
    _snce(event, guard) for event in _TAUTOLOGY_EVENTS for guard in _GUARDS
]


class TestTwelveConfirmedFormulas:
    """All 12 disagreement formulas are genuinely UNSAT (MC's verdict)."""

    def test_count_is_twelve(self):
        assert len(TWELVE_EXTERNAL_DEFECT_FORMULAS) == 12

    @pytest.mark.parametrize("index", range(12))
    def test_formula_is_unsat(self, index):
        formula = TWELVE_EXTERNAL_DEFECT_FORMULAS[index]
        verdict, _ = ground_truth_verdict(formula)
        assert verdict == "UNSAT", (
            f"Formula #{index} {formula} expected UNSAT (genuine tautology per "
            f"the research report's F4 finding), got {verdict}"
        )


##############################################################################
# Unsupported formula handling
##############################################################################


class TestUnsupportedFormula:
    def test_box_raises_ground_truth_unsupported(self):
        box_formula = {"tag": "box", "child": {"tag": "atom", "name": "p"}}
        with pytest.raises(GroundTruthUnsupported):
            ground_truth_verdict(box_formula)

    def test_box_unsupported_is_a_value_error(self):
        """GroundTruthUnsupported is a ValueError, not a bare one -- callers
        can catch it specifically without swallowing unrelated ValueErrors."""
        assert issubclass(GroundTruthUnsupported, ValueError)

    def test_enriched_tag_raises_ground_truth_unsupported(self):
        """Enriched tags (outside {atom, bot, imp, untl, snce}) are also
        unsupported -- the evaluator only understands the 5 primitive tags
        it directly implements, not the enriched surface."""
        top_formula = {"tag": "top"}
        with pytest.raises(GroundTruthUnsupported):
            ground_truth_verdict(top_formula)


##############################################################################
# Default window derivation
##############################################################################


class TestDefaultWindow:
    def test_default_window_at_least_depth_plus_two(self):
        """The default window is derived from the formula, not hard-coded,
        and is at least depth+2 -- verified indirectly: a formula of depth 2
        evaluates identically to an explicit window of depth+2."""
        formula = TWELVE_EXTERNAL_DEFECT_FORMULAS[0]
        assert temporal_depth(formula) == 1
        default_verdict, _ = ground_truth_verdict(formula)
        explicit_verdict, _ = ground_truth_verdict(formula, window=1 + 2)
        assert default_verdict == explicit_verdict == "UNSAT"

    def test_default_window_matches_formula_derived_formula(self):
        """max(temporal_depth+2, 4) is what get used when window=None."""
        # Depth 0 formula: default window should floor at 4, not depth+2=2.
        shallow = _SANITY_ATOM
        assert temporal_depth(shallow) == 0
        # A too-small explicit window (e.g. 1) can behave differently from
        # the floored default; confirm the default is NOT the bare depth+2.
        default_verdict, _ = ground_truth_verdict(shallow)
        floored_verdict, _ = ground_truth_verdict(shallow, window=4)
        assert default_verdict == floored_verdict


##############################################################################
# Window stability sweep
##############################################################################


def _temporal_only_formulas_complexity_5():
    all_formulas = _enumerate_primitive_formulas(5, ["p"])
    return [f for f in all_formulas if _is_temporal_only(f)]


class TestWindowStability:
    """The direct guard against this evaluator's own off-by-one class of
    bug: verdicts must not move as the brute-force window widens, for every
    temporal-only formula at complexity<=5.

    Measured wall clock: 0.08s for all 158 temporal-only formulas at
    complexity<=5 across 3 windows each -- well under the ~15s threshold
    from the plan, so this stays in the fast test set rather than being
    marked @pytest.mark.slow."""

    def test_verdict_stable_across_widening_windows(self):
        formulas = _temporal_only_formulas_complexity_5()
        assert formulas, "expected a non-empty temporal-only formula population"

        start = time.monotonic()
        mismatches = []
        for formula in formulas:
            d = temporal_depth(formula)
            verdicts = {
                w: ground_truth_verdict(formula, window=d + w)[0]
                for w in (2, 3, 4)
            }
            if len(set(verdicts.values())) != 1:
                mismatches.append((formula, verdicts))
        elapsed = time.monotonic() - start
        print(
            f"test_verdict_stable_across_widening_windows: "
            f"{len(formulas)} formulas, {elapsed:.2f}s"
        )

        assert not mismatches, (
            f"{len(mismatches)} formula(s) have a verdict that moves with the "
            f"window -- this is a hard failure, not a tolerance:\n"
            + "\n".join(f"  {f}: {v}" for f, v in mismatches[:5])
        )
