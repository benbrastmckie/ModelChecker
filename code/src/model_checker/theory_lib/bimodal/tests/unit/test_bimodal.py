"""
1. To run all tests in the file run from your PROJECT_DIRECTORY:
pytest PROJECT_DIRECTORY/code/src/model_checker/theory_lib/bimodal/test/test_bimodal.py

2. To run a specific example test by name:
pytest PROJECT_DIRECTORY/code/src/model_checker/theory_lib/bimodal/test/test_bimodal.py -k "example_name"

3. To see more detailed output including print statements:
pytest -v PROJECT_DIRECTORY/code/src/model_checker/theory_lib/bimodal/test/test_bimodal.py

4. To see the most detailed output with full traceback:
pytest -vv PROJECT_DIRECTORY/code/src/model_checker/theory_lib/bimodal/test/test_bimodal.py

5. To see test progress in real-time:
pytest -v PROJECT_DIRECTORY/code/src/model_checker/theory_lib/bimodal/test/test_bimodal.py --capture=no
"""

import pytest

from model_checker import (
    ModelConstraints,
    Syntax,
    run_test,
)
from model_checker.theory_lib.bimodal import (
    BimodalStructure,
    BimodalProposition,
    BimodalSemantics,
    bimodal_operators,
)
from model_checker.theory_lib.bimodal.examples import countermodel_examples, theorem_examples
from model_checker.utils.context import isolated_z3_context

# Combine both example sets for testing, excluding known solver timeout cases
# NOTE: MF_MODAL_FUTURE_TH is NOT excluded here. It tests the BX axiom "Box A -> Box(G A)",
# which IS valid in the paper's task semantics: proved over the unrestricted frame class by
# the Lean theorem `modal_future_valid` (Metalogic/Soundness.lean:373), with
# `no_witnessFamily_of_MF` (Metalogic/Decidability/WitnessFamily/Examples.lean:275)
# additionally proving that no witness-family certificate at any segment lengths refutes it.
# `MF_MODAL_FUTURE_TH_settings`' `expectation: False` (examples.py) already encodes the
# correct verdict (no countermodel; a genuine theorem) and was never itself wrong. What the
# now-retired window-and-abundance encoding got wrong was its own search: it reported a
# spurious countermodel at N=1, M=2, an artifact of that encoding's bounded-window boundary
# vacuity (its own `ForAllTime` docstring recorded that G(p) evaluated at t = M-1 is
# vacuously true there), not a real axiom failure -- so the entry's earlier presence in this
# set was itself a mis-filing (a wrong-verdict exclusion mislabeled as a timeout, not an
# actual timeout). Under the certificate encoding this example runs the pure-Python
# re-checker like every other example and is expected to decide `match`. See
# `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` for the full proof and
# citation table. The related BM_TH_5 tests the valid formula "Box A -> Future(Box A)"
# (paper's TF) and remains excluded below pending Phase 17's re-activation pass.
# NOTE: BX7_LINEAR_U_TH, BX7P_LINEAR_S_TH previously used N=4, M=5 under the retired
# window encoding and were computationally expensive there; re-measured under the
# certificate encoding's back/mid/fwd segment lengths in Phase 17.
# NOTE: BM_TH_1, BM_TH_2 are validated theorems (Box->Future/Past perpetuity principles,
# derived from MF+MT+TR -- see their own comments in examples.py). Their max_time=30s budget
# is retained from the retired encoding's exhaustive-search cost and re-measured in Phase 17.
KNOWN_TIMEOUT_EXAMPLES = {
    "TN_CM_1",              # (Previously timed out; re-assessed in Phase 17)
    "TN_CM_2",              # future A, future B -> future(A/\B): countermodel search times out even at 15s
    "BM_CM_3",              # Diamond A -> future A: finds countermodel in isolation but Z3 state non-determinism
                            # causes failures in the full suite (sometimes 10-15s, sometimes <5s)
    "MD_TH_2",
    "BM_TH_1", "BM_TH_2",  # Perpetuity theorems: valid; too slow under the retired encoding for CI
    "BX7_LINEAR_U_TH",      # BX7 Until linearity: N=4, M=5 under the retired encoding - computationally expensive
    "BX7P_LINEAR_S_TH",     # BX7' Since linearity: N=4, M=5 under the retired encoding - computationally expensive
    # NOTE (corrected -- the sentence below was accurate for the Box scope fix +
    # capped_skolem_abundance_constraint era but is now false for two of the three named
    # examples): BM_CM_2 still reliably finds its countermodel with no open issue. BM_CM_1 is
    # tracked in UNSTABLE_EXAMPLES below (a heavy-tailed Future/all_future solve distribution).
    # BM_CM_4 regressed to a deterministic solve-cost failure after commit f9cc081e added the
    # Skolemized Seriality + Interpolation frame axioms, and is now ALSO tracked in
    # UNSTABLE_EXAMPLES below -- see BM_CM_4_settings' comment in examples.py for the full
    # measured history. All three remain included in the test suite (collected, not removed via
    # this KNOWN_TIMEOUT_EXAMPLES set), just with their real current status recorded below
    # rather than here. Both UNSTABLE_EXAMPLES entries name the retired encoding's own Z3
    # cost profile and are re-assessed against the certificate encoding in Phase 19.
}

# `unstable`-marked examples, kept collected and observable rather than removed from
# collection (KNOWN_TIMEOUT_EXAMPLES's job). See code/pyproject.toml's `unstable`
# marker registration and TESTING_GUIDE.md section 8.9 for the full policy. Each
# entry here must satisfy all four strict entry criteria, recorded explicitly below:
#
# BM_CM_1 (test_example_cases[BM_CM_1-example_case7]):
#
# (1) WHAT FAILS AND WHY -- a heavy-tailed Z3 solve distribution on the Future/
#     all_future quantifier family. Median ~7-8s, decided draws measured up to
#     47.78s, one documented draw undecided at 600s (see BM_CM_1_settings' comment
#     in examples.py), and the real CI failure landed at 60.94s against the 60s
#     max_time budget -- a near-budget draw tipping over, not a new failure mode.
#
# (2) DEMONSTRABLY NOT SEMANTIC -- the genuine countermodel is found on every
#     decided draw: 7/7 in this round's independent seed sweep, corroborated by
#     the settings comment's own prior 7-seed history. The failure mode is always
#     a budget overrun reported as `model_found == False` (this test's assertion
#     below), never a changed semantic conclusion.
#
# (3) GENUINE FIX ATTEMPTED AND ITS FAILURE RECORDED -- three closed encoding
#     avenues, cross-referenced at operators.py's `_fresh_bound_int` docstring:
#     z3.FreshInt substitution (regresses even non-aliased single-instance
#     formulas), explicit ForAllTime/ExistsTime pattern/trigger hints (rejected
#     by Z3 at construction or provably inert), and finite unrolling of
#     ForAllTime/ExistsTime over the statically-known time domain (helps 5 of 7
#     seeds, but 2 of 7 regress from deciding to undecided -- inconclusive-to-
#     negative on net). `max_time` re-tuning is explicitly ruled out by
#     BM_CM_1_settings' own standing verdict: no budget closes this tail.
#
# (4) EXIT CRITERION -- verbatim and unambiguous: the marker comes off when
#     EITHER 20 consecutive unstable-watch runs record zero failures (nightly
#     cadence, ~3 weeks), OR a genuine encoding fix collapses the tail across a
#     >= 20-seed sweep with no undecided draw at max_time = 60. A single green
#     CI run never qualifies.
#
# BM_CM_4 (test_example_cases[BM_CM_4-example_case9]):
#
# (1) WHAT FAILS AND WHY -- a solve-cost regression, not a run-to-run nondeterminism. Commit
#     f9cc081e added build_seriality_constraint/build_interpolation_constraint (Skolemized
#     Seriality + Interpolation frame axioms) to build_frame_constraints; its own commit message
#     already recorded BM_CM_4 regressing from a 4.07s decided `match` to `inconclusive` at
#     120s+. An isolation table (source: the f9cc081e-era regression baseline) shows a
#     monotonic, reproducible pattern -- `neither` 3.10s < `seriality_only` 9.27s ~
#     `interpolation_only` 6.33s < `both` undecided -- confirming Z3's default (unpinned)
#     parameters deterministically fail to decide within budget only when both axioms are
#     present together, not solver flakiness. A dedicated 25-seed pinned-seed sweep (this
#     marking's own diagnosis round) found the SAME deterministic-per-draw character extends
#     across pinned `smt`/`sat.random_seed` values too: 2/25 seeds (7, 17) at a 40s probe budget
#     produce an undecided draw against the real, committed construction -- a genuine, if
#     narrower than BM_CM_1's, heavy-tailed distribution, not a single pathological default
#     draw.
#
# (2) DEMONSTRABLY NOT SEMANTIC -- every decided draw returns the expected `match` with
#     `model_found: True`. The 25-seed pinned sweep found zero non-`match` decided draws (23/25
#     decided `match`, decided-time range 0.24s-26.46s); the failure mode is always a budget
#     overrun reported as `model_found == False`, never a changed semantic conclusion. This is
#     precisely the showing this entry could not previously make (BM_CM_4 was untracked and had
#     no decided-draw evidence on record) and now can.
#
# (3) GENUINE FIX ATTEMPTED AND ITS FAILURE RECORDED -- an alpha-rename of the two axioms' Z3
#     symbol identifiers (serial_succ/serial_pred/serial_w/serial_x and
#     interp_witness/interp_w/interp_v/interp_d1/interp_d2, logic byte-for-byte unchanged) was
#     tested as a candidate fix, motivated by Z3 MBQI/E-matching's documented sensitivity to
#     incidental symbol identity. A 3-5-probe sample at Z3's default parameters looked
#     promising (fast, decided `match` every time, including at the bound-var-counter states
#     [0, 17, 30] test_bound_var_counter_isolation.py parametrizes). A required >= 20-seed sweep
#     (25 pinned seeds, 40s probe budget) REJECTED it: the renamed construction produced 5/25
#     undecided draws -- MORE than the unmodified construction's 2/25 at the identical seeds and
#     budget. The rename does not eliminate the tail; it relocates it, and on this sample
#     relocates more of it into the tail than it removes. It was therefore never landed (`git
#     diff` on core.py is empty). `max_time` re-tuning is explicitly ruled out: BM_CM_4_settings
#     already documents one recalibration (30 -> 120) that did not close the tail, and widening
#     further would only hide the same undecided-draw rate rather than closing it.
#
# (4) EXIT CRITERION -- verbatim and unambiguous, following the BM_CM_1 entry's convention: the
#     marker comes off when EITHER 20 consecutive unstable-watch runs record zero failures
#     (nightly cadence, ~3 weeks), OR a genuine encoding fix collapses the tail across a
#     >= 20-seed sweep with no undecided draw at max_time = 120. A single green CI run never
#     qualifies.
#
# See TESTING_GUIDE.md section 8.9 for the general policy (entry/exit criteria,
# review cadence, promotion path, escalation rule) this marking follows.
UNSTABLE_EXAMPLES = {"BM_CM_1", "BM_CM_4"}

test_examples = {k: v for k, v in {**countermodel_examples, **theorem_examples}.items()
                 if k not in KNOWN_TIMEOUT_EXAMPLES}

# pytest.param with the same (name, case) positional values reproduces the
# auto-generated ids a bare `.items()` view would have produced -- no explicit
# `ids=` is passed, so node IDs are unchanged from before this restructuring
# (verified by a --collect-only diff; see the implementation summary).
test_example_params = [
    pytest.param(
        name, case,
        marks=[pytest.mark.unstable] if name in UNSTABLE_EXAMPLES else [],
    )
    for name, case in test_examples.items()
]

@pytest.mark.parametrize("example_name, example_case", test_example_params)
def test_example_cases(example_name, example_case):
    """Test each example case from test_example_range."""
    with isolated_z3_context():
        result = run_test(
            example_case,
            BimodalSemantics,
            BimodalProposition,
            bimodal_operators,
            Syntax,
            ModelConstraints,
            BimodalStructure,
        )
    assert result, f"Test failed for example: {example_name}"


if __name__ == '__main__':
    import pytest
    pytest.main([__file__, '-v'])
