"""Tests for the solver-free MC/BimodalHarness disagreement classifier.

Drives `classify_disagreement` with synthetic mc_sat/bh_sat values so no
solver is invoked -- this test module runs in seconds, not minutes. See
`oracle/bimodal_logic/tests/ground_truth_classify.py` for the implementation
(a test-support module, not collected as a test itself since pytest's
`python_files = "test_*.py"` only picks up `test_*.py`).
"""

from __future__ import annotations

import pytest

from bimodal_logic.tests.ground_truth_classify import (
    EXTERNAL_BH_DEFECT,
    MC_SOUNDNESS_BUG,
    UNCLASSIFIED,
    classify_disagreement,
)

# One of the 12 confirmed external-BH-defect formulas: (bot -> bot) Until bot.
# Ground truth: UNSAT (genuine tautology; MC is correct).
_TAUTOLOGY_UNTIL_BOT = {
    "tag": "untl",
    "event": {"tag": "imp", "left": {"tag": "bot"}, "right": {"tag": "bot"}},
    "guard": {"tag": "bot"},
}

# A box-containing formula: outside the ground-truth evaluator's supported
# fragment (GroundTruthUnsupported).
_BOX_FORMULA = {"tag": "box", "child": {"tag": "atom", "name": "p"}}

# A formula that is genuinely SAT per ground truth (a bare atom).
_ATOM_P = {"tag": "atom", "name": "p"}


class TestExternalBhDefect:
    """Ground truth UNSAT, mc_sat=False, bh_sat=True -- MC correct, BH wrong."""

    def test_classified_as_external_bh_defect(self):
        outcome = classify_disagreement(_TAUTOLOGY_UNTIL_BOT, mc_sat=False, bh_sat=True)
        assert outcome == EXTERNAL_BH_DEFECT


class TestMcSoundnessBug:
    """Ground truth sides against MC's verdict -- a real in-repo defect."""

    def test_ground_truth_unsat_mc_true_bh_false(self):
        """Same formula as the external-defect case, verdicts swapped: proves
        the classifier is not keying on formula shape, only on the
        ground-truth-vs-verdict relationship."""
        outcome = classify_disagreement(_TAUTOLOGY_UNTIL_BOT, mc_sat=True, bh_sat=False)
        assert outcome == MC_SOUNDNESS_BUG

    def test_ground_truth_sat_mc_false_bh_true(self):
        """Ground truth SAT, mc_sat=False (MC wrongly says UNSAT), bh_sat=True
        (BH correctly says SAT) -- MC is the wrong side here."""
        outcome = classify_disagreement(_ATOM_P, mc_sat=False, bh_sat=True)
        assert outcome == MC_SOUNDNESS_BUG


class TestUnclassified:
    """A disagreement ground truth cannot adjudicate."""

    def test_box_formula_is_unclassified(self):
        """GroundTruthUnsupported (raised for box-containing formulas) is
        mapped to UNCLASSIFIED, not propagated as an exception."""
        outcome = classify_disagreement(_BOX_FORMULA, mc_sat=False, bh_sat=True)
        assert outcome == UNCLASSIFIED


class TestAgreementRejected:
    """Agreement (mc_sat == bh_sat) is a programming error, not a disagreement."""

    def test_agreement_raises_value_error(self):
        with pytest.raises(ValueError):
            classify_disagreement(_TAUTOLOGY_UNTIL_BOT, mc_sat=True, bh_sat=True)

    def test_agreement_raises_value_error_both_false(self):
        with pytest.raises(ValueError):
            classify_disagreement(_TAUTOLOGY_UNTIL_BOT, mc_sat=False, bh_sat=False)


class TestOutcomeConstants:
    """The three outcome strings are distinct module-level constants."""

    def test_three_distinct_outcomes(self):
        outcomes = {EXTERNAL_BH_DEFECT, MC_SOUNDNESS_BUG, UNCLASSIFIED}
        assert len(outcomes) == 3
