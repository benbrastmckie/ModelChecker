"""ground_truth_classify - Solver-free MC/BimodalHarness disagreement classifier.

A test-support module, not a test module: pytest's `python_files = "test_*.py"`
does not collect this file (it lives in `tests/` alongside `test_*.py` files
but is named without the `test_` prefix), so it can be imported by both
`test_disagreement_classification.py` (synthetic, Z3-free) and
`test_cross_oracle_differential.py` (real solves) without being re-collected
as its own test suite.

`classify_disagreement` adjudicates a single MC/BH disagreement against the
`ground_truth` module's brute-force verdict and returns exactly one of three
outcomes -- the "cannot adjudicate" case is explicit (`UNCLASSIFIED`), never
swallowed into a default.
"""

from __future__ import annotations

from bimodal_logic.ground_truth import GroundTruthUnsupported, ground_truth_verdict

# Named constants so the differential test and the defect record refer to
# the same tokens rather than duplicating string literals.
EXTERNAL_BH_DEFECT = "external_bh_defect"
MC_SOUNDNESS_BUG = "mc_soundness_bug"
UNCLASSIFIED = "unclassified"


def classify_disagreement(formula_json: dict, mc_sat: bool, bh_sat: bool) -> str:
    """Adjudicate a single MC/BH disagreement against ground truth.

    Args:
        formula_json: The disagreeing formula.
        mc_sat: MC's verdict (True = countermodel found / SAT, False = UNSAT).
        bh_sat: BH's verdict (True = countermodel found / SAT, False = UNSAT).

    Returns:
        One of:
            EXTERNAL_BH_DEFECT: ground truth agrees with MC (mc_sat is
                correct) and disagrees with BH -- BH is the wrong side, and
                (per the confirmed research) this is BimodalHarness's own
                boundary-scan defect, external to this repository.
            MC_SOUNDNESS_BUG: ground truth agrees with BH and disagrees with
                MC -- MC is the wrong side, a real in-repo soundness defect.
            UNCLASSIFIED: ground truth cannot adjudicate this formula (it
                uses a tag outside the evaluator's supported fragment).

    Raises:
        ValueError: if `mc_sat == bh_sat` -- that is agreement, not a
            disagreement, and calling this function on it is a programming
            error in the caller, not a classifiable outcome.
    """
    if mc_sat == bh_sat:
        raise ValueError(
            f"classify_disagreement called on an agreement (mc_sat=bh_sat={mc_sat!r}); "
            "this function only adjudicates genuine disagreements"
        )

    try:
        verdict, _ = ground_truth_verdict(formula_json)
    except GroundTruthUnsupported:
        return UNCLASSIFIED

    ground_truth_sat = verdict == "SAT"

    if ground_truth_sat == mc_sat:
        # Ground truth sides with MC -- BH is the wrong side.
        return EXTERNAL_BH_DEFECT
    # ground_truth_sat == bh_sat by construction (mc_sat != bh_sat and
    # ground_truth_sat must equal exactly one of them).
    return MC_SOUNDNESS_BUG
