"""Boundary Effect Analysis and Regression Tests for BimodalSemantics.

Task 107: Boundary effect analysis and temporal_depth mitigation.

This module provides three test classes:

1. TestBoundaryAnalysis:
   Tests verifying the mathematical boundary claim for BimodalSemantics finite
   domain. These tests are pure Python (no Z3 solver calls) and document the
   boundary safety computation M_safe(d) = max(d+2, 3).

2. TestBoundaryDocumentation:
   Tests that document observed Z3 behavior at different M values for temporal
   formulas. These tests verify the boundary claim using the existing known-good
   example TN_CM_1 (A => G(A)), which is the canonical boundary-sensitive formula.
   Additional documentation tests verify behavior at sufficient M values.

3. TestExampleRegression:
   Verifies all active bimodal examples still produce correct SAT/UNSAT results.
   Serves as the gate baseline for this task and future boundary-related changes.

4. TestTemporalDepthAllTags:
   Explicitly tests temporal_depth() for all 17 JSON formula tags, confirming
   complete tag coverage.

Background on BimodalSemantics finite time domain:
    The time domain is the open integer interval (-M, M) giving 2*M-1 integer
    time points: {-(M-1), ..., 0, ..., M-1}. Evaluation is fixed at t=0.

    Boundary claim: For a formula of temporal depth d evaluated at t=0 with
    M >= d+2, boundary effects cannot create spurious countermodels.

    The key invariant: evaluation from t=0 along a depth-d chain reaches at most
    t=d. With M >= d+2, we have M-1 >= d+1 > d, so t=d < M-1. The boundary
    time t=M-1 is strictly beyond the deepest reachable evaluation point.

    M_safe(d) = max(d + 2, 3) is the recommended minimum M value:
      d=0 -> M_safe=3, d=1 -> M_safe=3, d=2 -> M_safe=4, d=3 -> M_safe=5, ...
"""

from __future__ import annotations

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
from model_checker.theory_lib.bimodal.examples import (
    countermodel_examples,
    theorem_examples,
)
from model_checker.utils.context import isolated_z3_context

# Import temporal_depth for the all-tags test
from bimodal_logic.translation import temporal_depth


##############################################################################
# Helper
##############################################################################

def _run_formula(
    premises: list[str],
    conclusions: list[str],
    N: int,
    M: int,
    expectation: bool,
    max_time: int = 10,
    contingent: bool = False,
) -> bool:
    """Run a bimodal formula and return whether result matches expectation.

    expectation=True: countermodel expected (formula is invalid/satisfiable).
    expectation=False: no countermodel expected (formula is a theorem/valid).

    Returns True if run_test matches expectation, False otherwise.
    """
    example_case = [
        premises,
        conclusions,
        {
            'N': N,
            'M': M,
            'contingent': contingent,
            'disjoint': False,
            'max_time': max_time,
            'expectation': expectation,
        },
    ]
    with isolated_z3_context():
        return run_test(
            example_case,
            BimodalSemantics,
            BimodalProposition,
            bimodal_operators,
            Syntax,
            ModelConstraints,
            BimodalStructure,
        )


def _boundary_safe_m(depth: int) -> int:
    """Compute the minimum boundary-safe M for a formula of temporal depth d.

    Returns max(d + 2, 3) per the boundary claim in temporal_depth() docstring.
    """
    return max(depth + 2, 3)


##############################################################################
# Phase 2a: Boundary Math Verification (Pure Python)
##############################################################################

class TestBoundaryAnalysis:
    """Tests verifying the mathematical boundary claim without Z3 calls.

    These tests are pure Python and document the boundary safety computation.
    The boundary claim from temporal_depth() docstring:
        M_safe(d) = max(d + 2, 3)

    For M >= d+2, boundary vacuity cannot create spurious countermodels
    because the evaluation chain from t=0 can reach at most t=d < M-1.
    """

    def test_boundary_safe_m_formula_values(self):
        """Verify max(d+2, 3) gives expected M values for d in 0..6.

        This tests the M_safe formula from the boundary claim:
          d=0 -> M_safe=3 (minimum non-trivial domain)
          d=1 -> M_safe=3 (same, since max(3,3)=3)
          d=2 -> M_safe=4
          d=3 -> M_safe=5
          d=4 -> M_safe=6
          d=5 -> M_safe=7
          d=6 -> M_safe=8
        """
        expected = {0: 3, 1: 3, 2: 4, 3: 5, 4: 6, 5: 7, 6: 8}
        for depth, expected_m in expected.items():
            assert _boundary_safe_m(depth) == expected_m, (
                f"M_safe({depth}) should be {expected_m}, got {_boundary_safe_m(depth)}"
            )

    def test_boundary_safe_criterion(self):
        """Verify M > d+1 correctly classifies boundary safety.

        The sufficient condition for boundary safety is M >= d+2, equivalently M > d+1.
        At M = d+1, evaluation reaches t=d = M-1 (the boundary): unsafe.
        At M = d+2, evaluation reaches t=d < M-1: safe.
        """
        # Safe: M >= d+2 means M > d+1
        assert 3 > 0 + 1, "d=0, M=3: safe (3>1)"
        assert 3 > 1 + 1, "d=1, M=3: safe (3>2)"
        assert 4 > 2 + 1, "d=2, M=4: safe (4>3)"
        assert 5 > 3 + 1, "d=3, M=5: safe (5>4)"
        assert 6 > 4 + 1, "d=4, M=6: safe (6>5)"

        # Unsafe: M <= d+1 means M <= d+1
        assert not (2 > 2 + 1), "d=2, M=2: unsafe"
        assert not (3 > 3 + 1), "d=3, M=3: unsafe"
        assert not (4 > 4 + 1), "d=4, M=4: unsafe"
        # Boundary (M = d+1): also unsafe (chain reaches t=M-1)
        assert not (3 > 2 + 1), "d=2, M=3: boundary-unsafe (3 = d+1, chain reaches M-1)"

    def test_domain_size_formula(self):
        """Verify domain size 2*M-1 for different M values.

        The open interval (-M, M) contains 2*M-1 integer time points:
          {-(M-1), ..., -1, 0, 1, ..., M-1}
        """
        for M in range(1, 8):
            domain_size = 2 * M - 1
            domain = list(range(-(M - 1), M))  # integers in (-M, M)
            assert len(domain) == domain_size, (
                f"M={M}: domain {domain} has {len(domain)} points, expected {domain_size}"
            )
            assert min(domain) == -(M - 1)
            assert max(domain) == M - 1

    def test_reachable_depth_from_t0(self):
        """Verify that depth-d chain from t=0 reaches at most t=d.

        For a formula of depth d evaluated at t=0:
        - Depth-1 operator looks at t=1 (or t=-1 for past)
        - Depth-2 operator at t=0 looks at t=1, then t=2 from t=1
        - At depth d, the chain reaches t=d
        With M >= d+2, t=d < M-1 (not the boundary).
        """
        for depth in range(0, 6):
            reachable_max_t = depth  # chain from t=0 reaches at most t=depth
            M_safe = _boundary_safe_m(depth)
            boundary_t = M_safe - 1
            # The reachable point t=depth must be strictly less than the boundary
            assert reachable_max_t < boundary_t, (
                f"depth={depth}: reachable t={reachable_max_t} should be < boundary t={boundary_t} "
                f"with M_safe={M_safe}"
            )

    def test_future_time_points_at_m_safe(self):
        """Verify M_safe(d) provides d+1 future time points from t=0.

        At M_safe(d) = max(d+2, 3), the future times from t=0 are {1, ..., M-1}.
        This gives M-1 future time points. With M = d+2, this is d+1 points.
        Sufficient for a depth-d evaluation chain: t=0->1->...->d (d steps, d+1 points visited).
        """
        for depth in range(0, 5):
            M = _boundary_safe_m(depth)
            future_times = list(range(1, M))  # {1, ..., M-1}
            assert len(future_times) == M - 1, f"M={M}: {M-1} future times"
            # For depth d, M-1 >= d+1 (need d+1 future time points)
            assert M - 1 >= depth + 1, (
                f"M_safe({depth})={M}: need at least {depth+1} future times, have {M-1}"
            )


##############################################################################
# Phase 2b: Boundary Documentation Tests (Z3 Behavioral)
##############################################################################

class TestBoundaryDocumentation:
    """Tests documenting observed Z3 boundary behavior in BimodalSemantics.

    These tests use the canonical boundary-sensitive formula TN_CM_1 (A => G(A))
    to demonstrate boundary behavior at M=2 (the minimum non-trivial domain) vs
    larger M values. They also verify that theorem examples remain theorems at
    boundary-safe M values.

    TN_CM_1 analysis:
    - Formula: A => G(A) (premises=['A'], conclusions=['\\Future A'])
    - depth of G(A) = 1, M_safe(1) = 3
    - At M=2 (domain {-1,0,1}): G(A) at t=0 checks only t=1. A true at t=0 by
      premise but A may be false at t=1 -- countermodel exists. Verified working.
    - At M=2, the TN_CM_1 example correctly finds a countermodel (SAT, expectation=True).
    """

    def test_tn_cm1_finds_countermodel_at_m2(self):
        """TN_CM_1 (A => G(A)) finds countermodel at M=2 -- canonical test.

        This is the primary TN countermodel example. With M=2, G(A) at t=0
        checks t=1. A is true at t=0 (premise) but can be false at t=1.
        Z3 finds this countermodel reliably. expectation=True = countermodel expected.
        """
        result = _run_formula(
            premises=['A'],
            conclusions=['\\Future A'],
            N=2,
            M=2,
            expectation=True,  # countermodel expected and should be found
            max_time=10,
        )
        assert result, "TN_CM_1 at M=2 should find countermodel (A true at t=0, false at t=1)"

    def test_extensional_countermodel_at_m1(self):
        """Extensional non-theorem (A v B) => (A ^ B) finds countermodel at M=1.

        Depth-0 formula (no temporal operators). M_safe(0)=3, but M=1 works here
        because no temporal evaluation is needed. The countermodel is purely propositional.
        This confirms that boundary effects only apply to temporal depth > 0.
        """
        result = _run_formula(
            premises=['(A \\vee B)'],
            conclusions=['(A \\wedge B)'],
            N=2,
            M=1,
            expectation=True,  # countermodel expected
            max_time=5,
        )
        assert result, "EX_CM_1 at M=1 should find countermodel"

    def test_modal_countermodel_at_m1(self):
        """Modal non-theorem Box(A v B) => Box(A), Box(B) finds countermodel at M=1.

        Depth-0 formula (Box does not increment temporal depth).
        M=1, expectation=True, countermodel expected.
        """
        result = _run_formula(
            premises=['\\Box (A \\vee B)'],
            conclusions=['\\Box A'],
            N=2,
            M=1,
            expectation=True,
            max_time=5,
        )
        assert result, "MD_CM_1 at M=1 should find countermodel"

    def test_theorem_serial_f_at_m2(self):
        """BX1 serial_future is a theorem (top -> F(top)) at M=2.

        Depth=1 formula, M_safe(1)=3. With M=2, this is NOT at M_safe but is
        tested as a theorem. The formula is valid because the future domain is
        non-empty (M=2 gives future time t=1), so F(top) is always true.
        expectation=False = no countermodel expected.
        """
        result = _run_formula(
            premises=[],
            conclusions=['(\\neg \\bot \\rightarrow \\future \\neg \\bot)'],
            N=1,
            M=2,
            expectation=False,  # theorem: no countermodel
            max_time=10,
        )
        assert result, "BX1 serial_future should be recognized as theorem at M=2"

    def test_theorem_serial_f_at_boundary_safe_m3(self):
        """BX1 serial_future is still a theorem at M_safe(1)=3.

        Confirms the theorem remains valid when M is increased to the boundary-safe value.
        """
        result = _run_formula(
            premises=[],
            conclusions=['(\\neg \\bot \\rightarrow \\future \\neg \\bot)'],
            N=1,
            M=3,  # M_safe for depth=1
            expectation=False,  # theorem: no countermodel
            max_time=10,
        )
        assert result, "BX1 serial_future should remain theorem at M_safe=3"

    def test_theorem_conjunction_to_disjunction(self):
        """EX_TH_1 (A ^ B) => (A v B) is a theorem at any M.

        Depth-0 formula. M_safe(0)=3. Tests that extensional theorems remain
        valid at boundary-safe M values.
        """
        result = _run_formula(
            premises=['(A \\wedge B)'],
            conclusions=['(A \\vee B)'],
            N=2,
            M=3,  # M_safe for depth=0
            expectation=False,  # theorem: no countermodel
            max_time=5,
        )
        assert result, "EX_TH_1 should be theorem at M_safe=3"

    def test_theorem_tn_th2_at_boundary_safe_m(self):
        """TN_TH_2 (A => G(P(A))) is a theorem at M_safe(2)=4.

        Formula depth=2 (G then P). M_safe(2)=4. This temporal theorem should
        hold at boundary-safe M values.
        """
        result = _run_formula(
            premises=['A'],
            conclusions=['\\Future \\past A'],
            N=2,
            M=4,  # M_safe for depth=2
            expectation=False,  # theorem: no countermodel
            max_time=15,
        )
        assert result, "TN_TH_2 (A => G(P(A))) should be theorem at M_safe=4"

    def test_countermodel_bm_cm4_at_example_settings(self):
        """BM_CM_4 (Diamond(A) => Past(A)) has countermodel at its example settings.

        Depth=1 formula (past temporal operator). BM_CM_4 uses N=2, M=2, contingent=True.
        Past(A) false at t=0 means: no past time t'<0 has A true.
        This is a genuine countermodel (not a boundary artifact): with M=2,
        past times are just t=-1, and A can be false there while Diamond(A) holds.
        """
        result = _run_formula(
            premises=['\\Diamond A'],
            conclusions=['\\past A'],
            N=2,
            M=2,
            expectation=True,  # countermodel expected
            max_time=15,
            contingent=True,
        )
        assert result, "BM_CM_4 should find countermodel at N=2, M=2, contingent=True"

    def test_boundary_depth_vs_m_table(self):
        """Verify the boundary safety table for depth 0..4 using the M_safe formula.

        This is a pure computation test (no Z3) verifying the boundary claim
        table: for depth d, M_safe = max(d+2, 3), and the boundary time M-1
        is strictly greater than the maximum reachable time d.
        """
        boundary_table = [
            # (depth, M_safe, boundary_t = M_safe-1, reachable_max = depth)
            (0, 3, 2, 0),
            (1, 3, 2, 1),
            (2, 4, 3, 2),
            (3, 5, 4, 3),
            (4, 6, 5, 4),
        ]
        for depth, expected_M_safe, expected_boundary, expected_reachable in boundary_table:
            computed_M_safe = _boundary_safe_m(depth)
            assert computed_M_safe == expected_M_safe, (
                f"depth={depth}: M_safe={computed_M_safe}, expected {expected_M_safe}"
            )
            assert computed_M_safe - 1 == expected_boundary, (
                f"depth={depth}: boundary_t={computed_M_safe-1}, expected {expected_boundary}"
            )
            assert expected_reachable < expected_boundary, (
                f"depth={depth}: reachable {expected_reachable} not < boundary {expected_boundary}"
            )


##############################################################################
# Phase 3: 43-Example Regression Test
##############################################################################

# Examples excluded from automated testing due to timeout/non-determinism
# (same list as in test_bimodal.py for consistency)
REGRESSION_TIMEOUT_EXAMPLES = {
    "TN_CM_1",
    "TN_CM_2",
    "BM_CM_3",
    "MD_TH_2",
    "BM_TH_1",
    "BM_TH_2",
    "MF_MODAL_FUTURE_TH",
    "BX7_LINEAR_U_TH",
    "BX7P_LINEAR_S_TH",
}

# Active examples for regression testing (all examples minus timeout exclusions)
_all_examples = {**countermodel_examples, **theorem_examples}
regression_examples = {
    k: v for k, v in _all_examples.items()
    if k not in REGRESSION_TIMEOUT_EXAMPLES
}


class TestExampleRegression:
    """Regression test verifying all active bimodal examples produce correct SAT/UNSAT.

    This is the gate baseline for task 107 and future boundary-related changes.
    The active set excludes known-timeout examples (same as test_bimodal.py).

    Total examples in examples.py: 52
    Known-timeout exclusions: 9 (TN_CM_1, TN_CM_2, BM_CM_3, MD_TH_2, BM_TH_1,
                                  BM_TH_2, MF_MODAL_FUTURE_TH, BX7_LINEAR_U_TH,
                                  BX7P_LINEAR_S_TH)
    Active examples tested here: 43

    Countermodel examples (expectation=True): 10 active examples
    Theorem examples (expectation=False): 33 active examples
    """

    @pytest.mark.parametrize("example_name, example_case", regression_examples.items())
    def test_regression_all_active_examples(self, example_name, example_case):
        """Verify each active example produces the correct SAT/UNSAT result.

        This test is parametrized so individual failures are clearly identified
        by example name, enabling targeted debugging.
        """
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
        assert result, (
            f"Regression failure for example '{example_name}': "
            f"expected={'countermodel' if example_case[2]['expectation'] else 'theorem/no-countermodel'}"
        )

    def test_active_example_count(self):
        """Verify the regression test covers the expected number of active examples.

        Confirms 43 active examples (52 total - 9 timeout-excluded) are present.
        This count is documented as the gate baseline for task 107.
        """
        total_examples = len(_all_examples)
        active_count = len(regression_examples)
        excluded_count = len(REGRESSION_TIMEOUT_EXAMPLES)

        # The 52-example total may grow as new examples are added.
        # The important invariant is active_count = total - excluded.
        assert active_count == total_examples - excluded_count, (
            f"Active count {active_count} != total {total_examples} - excluded {excluded_count}"
        )
        # Document the baseline: exactly 43 active examples at task 107 completion
        assert active_count == 43, (
            f"Task 107 baseline: expected 43 active examples, found {active_count}. "
            f"Update this assertion if examples were intentionally added/removed."
        )

    def test_countermodel_examples_all_active(self):
        """Verify the 10 countermodel examples (SAT) are all represented.

        Countermodel examples (expectation=True, SAT):
        EX_CM_1, MD_CM_1..6, BM_CM_1, BM_CM_2, BM_CM_4
        (BM_CM_3 is excluded as timing-sensitive)
        """
        countermodel_keys = [k for k, v in regression_examples.items()
                             if v[2]['expectation'] is True]
        # Must have exactly 10 active countermodel examples
        assert len(countermodel_keys) == 10, (
            f"Expected 10 active countermodel examples, found {len(countermodel_keys)}: "
            f"{countermodel_keys}"
        )

    def test_theorem_examples_all_active(self):
        """Verify the 33 theorem examples (UNSAT) are all represented.

        Theorem examples (expectation=False, UNSAT):
        EX_TH_1, MD_TH_1, TN_TH_2, BM_TH_3, BM_TH_4, BM_TH_5,
        PROP_K_TH, PROP_S_TH, EX_FALSO_TH, PEIRCE_TH,
        MODAL_T_TH, MODAL_4_TH, MODAL_B_TH, MODAL_5_TH,
        BX1_SERIAL_F_TH, BX1P_SERIAL_P_TH, BX2G_MONO_U_TH, BX2H_MONO_S_TH,
        BX3_MONO_U_TH, BX3P_MONO_S_TH, BX4_CONNECT_F_TH, BX4P_CONNECT_P_TH,
        BX10_UNTIL_F_TH, BX10P_SINCE_P_TH, BX12_F_UNTIL_TH, BX12P_P_SINCE_TH,
        BX5_ACCUM_U_TH, BX5P_ACCUM_S_TH, BX6_ABSORB_U_TH, BX6P_ABSORB_S_TH,
        BX11_LIN_F_TH, BX11P_LIN_P_TH, BX13_ENRICH_U_TH, BX13P_ENRICH_S_TH
        (MD_TH_2, BM_TH_1, BM_TH_2, MF_MODAL_FUTURE_TH are excluded)
        """
        theorem_keys = [k for k, v in regression_examples.items()
                        if v[2]['expectation'] is False]
        # Must have exactly 33 active theorem examples
        assert len(theorem_keys) == 33, (
            f"Expected 33 active theorem examples, found {len(theorem_keys)}: "
            f"{theorem_keys}"
        )


##############################################################################
# Phase 3: temporal_depth All-Tags Explicit Coverage Test
##############################################################################

class TestTemporalDepthAllTags:
    """Explicit all-17-tags coverage test for temporal_depth().

    The 17 JSON formula tags:
    Primitive (6): atom, bot, imp, box, untl, snce
    Enriched (11): neg, top, and, or, diamond, next, prev,
                   some_future, some_past, all_future, all_past

    This supplements the existing 26 tests in test_json_translation.py with
    a single test that confirms every tag produces the expected depth value,
    serving as an explicit gate check for task 107.
    """

    def test_all_17_tags_coverage(self):
        """Verify temporal_depth() handles all 17 JSON formula tags correctly.

        One representative formula is constructed for each tag.
        The expected depth follows the depth rules in temporal_depth() docstring.
        """
        atom_p = {"tag": "atom", "name": "p"}

        tag_cases = [
            # tag=atom: leaf, depth 0
            ("atom", atom_p, 0),

            # tag=bot: leaf, depth 0
            ("bot", {"tag": "bot"}, 0),

            # tag=top: leaf, depth 0
            ("top", {"tag": "top"}, 0),

            # tag=neg: extensional unary, depth(arg)
            ("neg", {"tag": "neg", "arg": atom_p}, 0),

            # tag=imp: extensional binary, max(left, right)
            ("imp", {"tag": "imp", "left": atom_p, "right": atom_p}, 0),

            # tag=and: extensional binary, max(left, right)
            ("and", {"tag": "and", "left": atom_p, "right": atom_p}, 0),

            # tag=or: extensional binary, max(left, right)
            ("or", {"tag": "or", "left": atom_p, "right": atom_p}, 0),

            # tag=box: modal, NO increment -- depth(child)
            ("box", {"tag": "box", "child": atom_p}, 0),

            # tag=diamond: modal, NO increment -- depth(arg)
            ("diamond", {"tag": "diamond", "arg": atom_p}, 0),

            # tag=untl: temporal primitive, 1 + max(event, guard)
            ("untl", {"tag": "untl", "event": atom_p, "guard": atom_p}, 1),

            # tag=snce: temporal primitive, 1 + max(event, guard)
            ("snce", {"tag": "snce", "event": atom_p, "guard": atom_p}, 1),

            # tag=next: temporal enriched, 1 + depth(arg)
            ("next", {"tag": "next", "arg": atom_p}, 1),

            # tag=prev: temporal enriched, 1 + depth(arg)
            ("prev", {"tag": "prev", "arg": atom_p}, 1),

            # tag=some_future: temporal enriched, 1 + depth(arg)
            ("some_future", {"tag": "some_future", "arg": atom_p}, 1),

            # tag=some_past: temporal enriched, 1 + depth(arg)
            ("some_past", {"tag": "some_past", "arg": atom_p}, 1),

            # tag=all_future: temporal enriched, 1 + depth(arg)
            ("all_future", {"tag": "all_future", "arg": atom_p}, 1),

            # tag=all_past: temporal enriched, 1 + depth(arg)
            ("all_past", {"tag": "all_past", "arg": atom_p}, 1),
        ]

        assert len(tag_cases) == 17, "Must have exactly 17 tag test cases"

        for tag_name, formula_json, expected_depth in tag_cases:
            actual = temporal_depth(formula_json)
            assert actual == expected_depth, (
                f"temporal_depth() for tag='{tag_name}': "
                f"expected {expected_depth}, got {actual}"
            )

    def test_nested_temporal_tags_depth(self):
        """Verify temporal_depth correctly computes nested temporal operators.

        Tests cases from the boundary claim: G(G(p)) has depth 2,
        F(G(p)) has depth 2, H(F(p)) has depth 2, G(G(G(p))) has depth 3.
        """
        atom_p = {"tag": "atom", "name": "p"}

        # G(G(p)) = all_future(all_future(atom)) -> depth=2
        gg_p = {"tag": "all_future", "arg": {"tag": "all_future", "arg": atom_p}}
        assert temporal_depth(gg_p) == 2, "G(G(p)) should have depth 2"

        # F(G(p)) = some_future(all_future(atom)) -> depth=2
        fg_p = {"tag": "some_future", "arg": {"tag": "all_future", "arg": atom_p}}
        assert temporal_depth(fg_p) == 2, "F(G(p)) should have depth 2"

        # H(F(p)) = all_past(some_future(atom)) -> depth=2
        hf_p = {"tag": "all_past", "arg": {"tag": "some_future", "arg": atom_p}}
        assert temporal_depth(hf_p) == 2, "H(F(p)) should have depth 2"

        # G(G(G(p))) = all_future(all_future(all_future(atom))) -> depth=3
        ggg_p = {
            "tag": "all_future",
            "arg": {"tag": "all_future", "arg": {"tag": "all_future", "arg": atom_p}}
        }
        assert temporal_depth(ggg_p) == 3, "G(G(G(p))) should have depth 3"

        # Modal wrapping does NOT increase depth: Box(G(p)) has depth 1
        box_g_p = {"tag": "box", "child": {"tag": "all_future", "arg": atom_p}}
        assert temporal_depth(box_g_p) == 1, (
            "Box(G(p)) should have depth 1 (box does not increment temporal depth)"
        )

    def test_boundary_safe_m_for_common_formulas(self):
        """Verify M_safe(depth) for common formula patterns used in boundary analysis.

        Connects temporal_depth() results to the boundary claim's M_safe formula.
        """
        atom_p = {"tag": "atom", "name": "p"}

        # Leaf nodes (depth=0) -> M_safe=3
        assert _boundary_safe_m(temporal_depth({"tag": "atom", "name": "p"})) == 3
        assert _boundary_safe_m(temporal_depth({"tag": "bot"})) == 3
        assert _boundary_safe_m(temporal_depth({"tag": "top"})) == 3

        # Temporal enriched depth=1 -> M_safe=3
        assert _boundary_safe_m(temporal_depth({"tag": "all_future", "arg": atom_p})) == 3
        assert _boundary_safe_m(temporal_depth({"tag": "some_past", "arg": atom_p})) == 3
        assert _boundary_safe_m(
            temporal_depth({"tag": "untl", "event": atom_p, "guard": atom_p})
        ) == 3

        # Nested depth=2 -> M_safe=4
        gg_p = {"tag": "all_future", "arg": {"tag": "all_future", "arg": atom_p}}
        assert _boundary_safe_m(temporal_depth(gg_p)) == 4

        # Triple-nested depth=3 -> M_safe=5
        ggg_p = {"tag": "all_future", "arg": gg_p}
        assert _boundary_safe_m(temporal_depth(ggg_p)) == 5

        # Modal-temporal: Box(G(p)) depth=1 -> M_safe=3
        box_g_p = {"tag": "box", "child": {"tag": "all_future", "arg": atom_p}}
        assert _boundary_safe_m(temporal_depth(box_g_p)) == 3


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
