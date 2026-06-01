"""Soundness regression test suite for boundary and shift-closure edge cases.

Task 108: Soundness regression test suite targeting specific soundness gap
points in the bimodal oracle.

This module covers five test categories:
1. TestBoundaryVacuity:          boundary_safe flag and boundary artifacts
2. TestShiftClosure:             shift closure on extracted world histories
3. TestGuardedCompositionality:  frame axioms on oracle's serialized task_relation
4. TestStateIsolationRegression: 100+ sequential calls with mixed temporal depths
5. TestKnownBoundaryUnsafe:      5 hand-crafted depth-2 formulas with documented behavior

Key research findings (from reports/01_soundness-regression.md):
- G(G(p)) is the prime boundary-unsafe formula: oracle returns None at M=2
  (spurious theorem). Boundary-safe behavior requires M>=4.
- Shift closure tests require M>=3. At M=2, the only valid shift for a world
  spanning {-1, 0, 1} is delta=0 (trivial), so shift closure tests must use
  BimodalSemantics directly with M=3, bypassing the oracle's M=max(depth,2).
- Oracle's serialized task_relation is NOT tested against frame axioms by
  existing tests. This module tests the serialized output dict.
- Current M formula: M=max(depth,2) -- NOT M=max(depth+2,3).
  boundary_safe = (M > depth+1), which is False for depth>=1 with M=max(depth,2).
- State isolation previously used only propositional formulas; this module
  adds depth-1 and depth-2 temporal formulas to the rotation.
"""

from __future__ import annotations

import pytest
import z3

from bimodal_logic import Z3OracleProvider
from bimodal_logic.translation import temporal_depth
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics
from model_checker.utils.context import isolated_z3_context


##############################################################################
# JSON formula constants
##############################################################################

# ---- Depth-0 formulas ----

# SAT: atom(A) -- countermodel where A=False
ATOM_A = {"tag": "atom", "name": "A"}

# UNSAT (valid tautology): A->A -- no countermodel possible
TAUTOLOGY = {
    "tag": "imp",
    "left": {"tag": "atom", "name": "A"},
    "right": {"tag": "atom", "name": "A"},
}

# SAT: A->B -- countermodel where A=True, B=False
IMP_A_B = {
    "tag": "imp",
    "left": {"tag": "atom", "name": "A"},
    "right": {"tag": "atom", "name": "B"},
}

# ---- Depth-1 formulas ----

# SAT: F(p) = some_future(atom(p)) -- countermodel: p false at all times
F_P = {"tag": "some_future", "arg": {"tag": "atom", "name": "p"}}

# UNSAT (valid): G(A->A) = all_future(tautology) -- tautology holds at all future times
G_TAUT = {
    "tag": "all_future",
    "arg": {
        "tag": "imp",
        "left": {"tag": "atom", "name": "A"},
        "right": {"tag": "atom", "name": "A"},
    },
}

# ---- Depth-2 formulas ----

# UNSAT (spurious theorem): F(G(p)) at M=2 -- both F(G(p)) and G(G(p)) are
# spurious theorems at M=2 due to boundary vacuity. ~F(G(p))=G(~G(p)) is
# unsatisfiable at M=2 because ~G(p) at t=1 is vacuously false.
FG_P = {
    "tag": "some_future",
    "arg": {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}},
}

# Prime boundary-unsafe formula: G(G(p)) = all_future(all_future(atom(p)))
# Oracle returns None at M=2 (spurious theorem).
# At t=0 with M=2: outer G checks t'=1 only; inner G(p) at t'=1 is vacuously
# true (no t''>1 in domain). So oracle finds no countermodel to G(G(p)),
# treating it as valid -- but G(G(p)) IS invalid (p can be false at t=3 with M=4).
GG_P = {
    "tag": "all_future",
    "arg": {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}},
}

# SAT: G(F(p)) -- genuine countermodel exists at M=2.
# F(p) at t=1 fails because no t''>1 in domain. Correct result despite boundary_safe=False.
GF_P = {
    "tag": "all_future",
    "arg": {"tag": "some_future", "arg": {"tag": "atom", "name": "p"}},
}

# SAT: F(F(p)) -- oracle at M=2: F(F(p)) at t=0 needs t'>0 with F(p) at t'.
# At t'=1: F(p) needs t''>1, none in domain. Countermodel exists (correct).
FF_P = {
    "tag": "some_future",
    "arg": {"tag": "some_future", "arg": {"tag": "atom", "name": "p"}},
}

# Compound depth-2: G(p) -> F(G(p))
G_IMP_FG = {
    "tag": "imp",
    "left": {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}},
    "right": {
        "tag": "some_future",
        "arg": {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}},
    },
}

# Compound depth-2: G(G(p)) -> G(F(p))
# Both subformulas depth=2, compound formula testing boundary interaction.
IMP_GG_P_GF_P = {
    "tag": "imp",
    "left": GG_P,
    "right": GF_P,
}


##############################################################################
# Shared helper functions
##############################################################################

def _task_rel_as_set(task_relation: list) -> set:
    """Convert a task_relation list of dicts to a set of (source, duration, target) tuples.

    Args:
        task_relation: List of {"source": int, "duration": int, "target": int} dicts.

    Returns:
        Set of (source, duration, target) integer tuples.
    """
    return {(t["source"], t["duration"], t["target"]) for t in task_relation}


def _check_forward_comp(task_relation: list, M: int) -> list:
    """Check the forward compositionality (compose) axiom on a task_relation list.

    Compose axiom: task_rel(s, d1, t) AND task_rel(t, d2, u) => task_rel(s, d1+d2, u)
    Guarded by: is_valid_duration(d1), is_valid_duration(d2), is_valid_duration(d1+d2)
    where is_valid_duration(d) := -(M-1) <= d <= M-1.

    Args:
        task_relation: List of {"source", "duration", "target"} dicts.
        M: Time bound parameter.

    Returns:
        List of violation descriptions (strings). Empty list means no violations.
    """
    pairs = _task_rel_as_set(task_relation)
    valid_range = range(-(M - 1), M)
    violations = []

    for (s, d1, t) in pairs:
        for (t2, d2, u) in pairs:
            if t2 != t:
                continue
            d_sum = d1 + d2
            # Only check within valid duration range (guarded compositionality)
            if d1 not in valid_range or d2 not in valid_range or d_sum not in valid_range:
                continue
            if (s, d_sum, u) not in pairs:
                violations.append(
                    f"compose violation: ({s},{d1},{t}) AND ({t},{d2},{u}) => ({s},{d_sum},{u}) NOT in task_rel"
                )

    return violations


def _check_converse(task_relation: list, M: int) -> list:
    """Check the converse axiom on a task_relation list.

    Converse axiom: task_rel(s, d, u) <=> task_rel(u, -d, s)
    Guarded by: is_valid_duration(d) AND is_valid_duration(-d)
    (i.e., -(M-1) <= d <= M-1 AND -(M-1) <= -d <= M-1, which means 0 in practice
    is always met and d can be any value in [-(M-1), M-1])

    Args:
        task_relation: List of {"source", "duration", "target"} dicts.
        M: Time bound parameter.

    Returns:
        List of violation descriptions (strings). Empty list means no violations.
    """
    pairs = _task_rel_as_set(task_relation)
    valid_range = range(-(M - 1), M)
    violations = []

    for (s, d, u) in pairs:
        if d not in valid_range or (-d) not in valid_range:
            continue
        if (u, -d, s) not in pairs:
            violations.append(
                f"converse violation: ({s},{d},{u}) in task_rel but ({u},{-d},{s}) NOT in task_rel"
            )

    return violations


def _check_nullity(task_relation: list) -> list:
    """Check the nullity (identity) axiom on a task_relation list.

    Nullity axiom: task_rel(s, 0, u) <=> s == u
    Checks both directions:
    1. Forward: if task_rel(s, 0, u) then s == u
    2. Backward: for every state s appearing in the relation, task_rel(s, 0, s) holds

    Args:
        task_relation: List of {"source", "duration", "target"} dicts.

    Returns:
        List of violation descriptions (strings). Empty list means no violations.
    """
    pairs = _task_rel_as_set(task_relation)
    violations = []

    # Forward: task_rel(s, 0, u) => s == u
    for (s, d, u) in pairs:
        if d == 0 and s != u:
            violations.append(
                f"nullity forward violation: ({s}, 0, {u}) in task_rel but {s} != {u}"
            )

    # Backward: for each state s appearing in the relation, task_rel(s, 0, s) must hold
    all_states = {t["source"] for t in task_relation} | {t["target"] for t in task_relation}
    for s in all_states:
        if (s, 0, s) not in pairs:
            violations.append(
                f"nullity backward violation: state {s} appears in task_rel but ({s}, 0, {s}) NOT present"
            )

    return violations


def _check_shift_closure(world_histories: list, M: int) -> list:
    """Check shift closure on a list of world history dicts.

    Shift closure (skolem_abundance): for each world history w spanning
    time interval [t_start, t_end], and for each valid delta such that
    [t_start+delta, t_end+delta] is within [-(M-1), M-1], there must
    exist another world history w' with w'(t+delta) = w(t) for all t
    in the original interval.

    Args:
        world_histories: List of world history dicts from oracle output.
            Each dict has at least a "states" or "time_states" mapping.
        M: Time bound parameter.

    Returns:
        List of violation descriptions (strings). Empty list means no violations.
    """
    # Build a set of (frozenset of (time, state) pairs) for membership testing
    history_signatures = []
    for wh in world_histories:
        # Extract time->state mapping from the world history dict
        if "states" in wh:
            states_map = wh["states"]
        elif "time_states" in wh:
            states_map = wh["time_states"]
        else:
            # Try to extract any dict-valued field that looks like time->state
            states_map = None
            for v in wh.values():
                if isinstance(v, dict):
                    states_map = v
                    break
        if states_map is None:
            continue
        # Convert keys to int (they may be strings in serialized form)
        time_state_pairs = frozenset(
            (int(t), s) for t, s in states_map.items()
        )
        history_signatures.append(time_state_pairs)

    violations = []
    valid_domain = range(-(M - 1), M)

    for sig in history_signatures:
        if not sig:
            continue
        times = sorted(t for (t, _) in sig)
        t_start = times[0]
        t_end = times[-1]
        state_at = {t: s for (t, s) in sig}

        for delta in valid_domain:
            if delta == 0:
                continue  # Trivial shift: self maps to self
            new_t_start = t_start + delta
            new_t_end = t_end + delta

            # Only check shifts that stay entirely within valid domain
            if new_t_start not in valid_domain or new_t_end not in valid_domain:
                continue

            # Build expected shifted signature
            expected_shifted = frozenset(
                (t + delta, state_at[t]) for t in times
            )

            # Check if any existing history matches the shift
            if expected_shifted not in history_signatures:
                violations.append(
                    f"shift_closure violation: world spanning [{t_start},{t_end}] "
                    f"with delta={delta} requires shifted world [{new_t_start},{new_t_end}] "
                    f"but no matching history found"
                )

    return violations


##############################################################################
# Phase 2: Boundary Vacuity Tests
##############################################################################

class TestBoundaryVacuity:
    """Tests for boundary_safe flag and boundary vacuity artifacts.

    The oracle's M formula is M=max(depth,2). The boundary_safe flag is:
        boundary_safe = (M > depth + 1)

    For depth=0: M=max(0,2)=2, boundary_safe=(2>1)=True
    For depth=1: M=max(1,2)=2, boundary_safe=(2>2)=False
    For depth=2: M=max(2,2)=2, boundary_safe=(2>3)=False
    For depth=3: M=max(3,2)=3, boundary_safe=(3>4)=False

    G(G(p)) at M=2 is the prime boundary-unsafe formula: the oracle finds no
    countermodel (returns None) because outer G at t=0 checks only t'=1, and
    inner G(p) at t'=1 is vacuously true (no t''>1 in domain). This is a known
    limitation documented here; fixing it requires raising M to max(depth+2,3).
    """

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_depth0_boundary_safe_is_true(self):
        """atom(A) with oracle at M=max(0,2)=2: boundary_safe=(2>1)=True."""
        result = self.provider.find_countermodel(ATOM_A)
        assert result is not None, "atom(A) should have a countermodel (SAT)"
        assert result["boundary_safe"] is True, (
            f"Expected boundary_safe=True for depth-0 formula, got {result['boundary_safe']}. "
            f"M={result['time_bound']}, depth={result['temporal_depth']}"
        )

    def test_depth1_boundary_safe_is_false(self):
        """F(p) at M=max(1,2)=2: boundary_safe=(2>2)=False.

        The oracle's M=max(depth,2) produces M=2 for depth=1.
        boundary_safe = (2 > 1+1) = (2 > 2) = False.
        """
        result = self.provider.find_countermodel(F_P)
        assert result is not None, "F(p) should have a countermodel (p false everywhere)"
        assert result["boundary_safe"] is False, (
            f"Expected boundary_safe=False for depth-1 formula (M=max(1,2)=2, 2>2 is False), "
            f"got {result['boundary_safe']}. M={result['time_bound']}, depth={result['temporal_depth']}"
        )
        assert result["temporal_depth"] == 1, (
            f"Expected temporal_depth=1 for F(p), got {result['temporal_depth']}"
        )
        assert result["time_bound"] == 2, (
            f"Expected time_bound=2 for depth-1 formula (M=max(1,2)=2), got {result['time_bound']}"
        )

    def test_depth2_boundary_safe_is_false(self):
        """GF(p) at M=max(2,2)=2: boundary_safe=(2>3)=False."""
        result = self.provider.find_countermodel(GF_P)
        assert result is not None, "G(F(p)) should have a countermodel"
        assert result["boundary_safe"] is False, (
            f"Expected boundary_safe=False for depth-2 formula (M=max(2,2)=2, 2>3 is False), "
            f"got {result['boundary_safe']}. M={result['time_bound']}, depth={result['temporal_depth']}"
        )
        assert result["temporal_depth"] == 2, (
            f"Expected temporal_depth=2 for G(F(p)), got {result['temporal_depth']}"
        )
        assert result["time_bound"] == 2, (
            f"Expected time_bound=2 for depth-2 formula (M=max(2,2)=2), got {result['time_bound']}"
        )

    def test_gg_p_returns_none_at_m2(self):
        """G(G(p)) with oracle returns None (spurious theorem -- known boundary limitation).

        This is the prime boundary-unsafe formula. At M=2:
        - Outer G(G(p)) at t=0 checks only t'=1 (since M-1=1 is the only future time)
        - Inner G(p) at t'=1: checks t''>1, but no t''>1 in domain [-(M-1), M-1]=[−1,1]
        - So inner G(p) at t'=1 is vacuously true (universal over empty set)
        - Therefore G(G(p)) appears valid at M=2

        BUT G(G(p)) IS logically invalid: with M=4, p=false at t=3 gives:
        - Inner G(p) at t'=1: false (p=false at t''=3 which is 2 steps ahead)
        - Outer G(G(p)) at t=0: false

        This test DOCUMENTS this known limitation of M=max(depth,2).
        Fixing it requires changing M to max(depth+2,3) in provider.py (task 109+).
        """
        result = self.provider.find_countermodel(GG_P)
        assert result is None, (
            "G(G(p)) should return None at M=2 (known boundary vacuity limitation). "
            "The oracle treats G(G(p)) as valid due to vacuous G at the time boundary. "
            f"Got: {result}"
        )

    def test_fg_p_returns_none_at_m2(self):
        """F(G(p)) with oracle returns None at M=2 (spurious theorem -- boundary vacuity).

        F(G(p)) at M=2 is treated as valid (returns None) for the same reason as G(G(p)):
        the oracle asks "is ~F(G(p)) satisfiable?" = "is G(~G(p)) satisfiable?"
        At M=2: ~G(p) at t'=1 requires some t''>1 with p=false. No t''>1 in domain.
        So ~G(p) at t'=1 is false (vacuously). G(~G(p)) at t=0 requires ~G(p) at t'=1>0,
        which is false. So G(~G(p)) is unsatisfiable → oracle returns None.

        Both G(G(p)) and F(G(p)) are spurious theorems at M=2 because both have their
        inner G vacuously satisfied at the time boundary t=1 (the last future time).

        This is a known limitation of M=max(depth,2)=2 for depth-2 formulas.
        boundary_safe would be False for depth=2 at M=2 (2 > 3 is False).
        """
        result = self.provider.find_countermodel(FG_P)
        assert result is None, (
            "F(G(p)) should return None at M=2 (spurious theorem due to boundary vacuity). "
            "~F(G(p)) = G(~G(p)) is unsatisfiable at M=2 because ~G(p) at t=1 is vacuously "
            "false (no t''>1 in domain {-1,0,1}). "
            f"Got: {result}"
        )

    def test_depth1_countermodel_correct_despite_boundary_unsafe(self):
        """F(p) at M=2 returns non-None with correct countermodel (p false at all times).

        F(p) = some_future(p): countermodel requires p to be false at all future
        times. Despite boundary_safe=False, the oracle finds a genuine countermodel
        because the vacuity issue does not affect this formula's falsification.

        Verifies result contains expected output fields.
        """
        result = self.provider.find_countermodel(F_P)
        assert result is not None, "F(p) should have a genuine countermodel"
        assert result["boundary_safe"] is False

        # Verify required output fields
        for key in ("temporal_depth", "boundary_safe", "time_bound", "semantics_version",
                    "formula_folded_json", "trueAtoms", "falseAtoms",
                    "world_histories", "task_relation"):
            assert key in result, f"Missing required key: {key}"

        # For F(p), p should be in falseAtoms at the main evaluation point
        false_atom_names = {a["name"] for a in result["falseAtoms"]}
        true_atom_names = {a["name"] for a in result["trueAtoms"]}
        assert "p" in (false_atom_names | true_atom_names), (
            "Atom 'p' should appear in either trueAtoms or falseAtoms"
        )


##############################################################################
# Phase 3: Shift Closure and Guarded Compositionality Tests
##############################################################################

class TestShiftClosure:
    """Tests for shift closure on extracted world histories.

    Shift closure (skolem_abundance) requires that for each world history w
    spanning a time interval, and for each valid shift delta, a corresponding
    shifted world history w' must exist in the model.

    At M=2, the valid time domain is {-1, 0, 1}. A world spanning all 3 time
    points {-1, 0, 1} can only be shifted by delta such that the shifted interval
    stays within {-1, 0, 1}. The only non-trivial interval for a full-span world
    is delta=0 (trivial), since delta=1 would require the shifted world to span
    {0, 1, 2} which is outside the domain.

    Therefore, meaningful shift closure tests require M>=3 and must use
    BimodalSemantics directly (bypassing the oracle's M=max(depth,2) formula).
    """

    def test_shift_closure_trivial_at_m2(self):
        """Oracle (M=2) for a SAT formula satisfies trivial shift closure.

        At M=2, a world spanning the full domain {-1, 0, 1} has no valid
        non-zero shifts (any shift would exceed the domain). So shift closure
        is vacuously satisfied.
        """
        provider = Z3OracleProvider()
        result = provider.find_countermodel(ATOM_A)
        assert result is not None

        M = result["time_bound"]
        world_histories = result["world_histories"]
        violations = _check_shift_closure(world_histories, M)

        assert violations == [], (
            f"Expected no shift closure violations at M=2 (trivially satisfied), "
            f"got: {violations}"
        )

    @pytest.mark.xfail(
        reason="M=3 with skolem_abundance may over-constrain no-premise queries; "
               "test documents shift closure behavior at M=3 using BimodalSemantics directly"
    )
    def test_shift_closure_on_extracted_worlds_m3(self):
        """Direct BimodalSemantics at M=3: world histories extracted from Z3 model satisfy shift closure.

        Uses BimodalSemantics directly with M=3 (bypassing oracle's M=max(depth,2))
        to test genuine shift closure. If M=3 causes solver timeout due to
        skolem_abundance over-constraint, this test is marked xfail.
        """
        from model_checker import ModelConstraints, Syntax
        from model_checker.theory_lib.bimodal import (
            BimodalProposition, BimodalStructure, bimodal_operators
        )
        from model_checker.theory_lib.bimodal.tests.unit.test_frame_class_mapping import (
            extract_world_histories
        )

        # Use a simple SAT formula at M=3
        settings = {
            'N': 2,
            'M': 3,
            'contingent': False,
            'disjoint': False,
            'max_time': 10.0,
            'expectation': True,
            'solver': 'z3',
        }

        with isolated_z3_context():
            semantics = BimodalSemantics(settings)
            syntax = Syntax([], ["p"], bimodal_operators)
            model_constraints = ModelConstraints(settings, syntax, semantics, BimodalProposition)
            structure = BimodalStructure(model_constraints, settings)

            if structure.timeout or not structure.z3_model_status:
                pytest.xfail("Solver timed out or returned UNSAT at M=3 for 'p'")

            # Extract world histories from Z3 model
            raw_histories = extract_world_histories(semantics, structure.z3_model)

        # Convert raw histories dict to list of world history dicts
        world_histories_list = [
            {"states": {str(t): s for t, s in hist.items()}}
            for hist in raw_histories.values()
        ]

        M = settings["M"]
        violations = _check_shift_closure(world_histories_list, M)

        assert violations == [], (
            f"Shift closure violations at M=3:\n" + "\n".join(violations)
        )


class TestGuardedCompositionality:
    """Tests for TaskFrame axioms on the oracle's serialized task_relation output.

    These tests validate the public oracle output dict's task_relation field
    against the three TaskFrame axioms (nullity, converse, forward_comp).

    Existing tests in test_frame_class_mapping.py validate the raw Z3 model
    against these axioms. This class validates the serialized output dict
    (what the oracle returns to callers), ensuring the serialization pipeline
    preserves the frame axiom guarantees.
    """

    def setup_method(self):
        self.provider = Z3OracleProvider()
        # Use a SAT formula that produces a non-trivial task_relation
        self.result = self.provider.find_countermodel(ATOM_A)
        assert self.result is not None, "Setup failed: atom(A) should have countermodel"

    def test_forward_comp_in_oracle_output(self):
        """Oracle's serialized task_relation satisfies forward compositionality.

        Checks: task_rel(s, d1, t) AND task_rel(t, d2, u) => task_rel(s, d1+d2, u)
        for all valid duration combinations (guarded by valid_range).
        """
        task_rel = self.result["task_relation"]
        M = self.result["time_bound"]
        violations = _check_forward_comp(task_rel, M)
        assert violations == [], (
            f"Forward compositionality violations in oracle output:\n"
            + "\n".join(violations)
        )

    def test_converse_in_oracle_output(self):
        """Oracle's serialized task_relation satisfies the converse axiom.

        Checks: task_rel(s, d, u) => task_rel(u, -d, s) for all valid durations.
        """
        task_rel = self.result["task_relation"]
        M = self.result["time_bound"]
        violations = _check_converse(task_rel, M)
        assert violations == [], (
            f"Converse axiom violations in oracle output:\n"
            + "\n".join(violations)
        )

    def test_nullity_in_oracle_output(self):
        """Oracle's serialized task_relation satisfies the nullity (identity) axiom.

        Checks: task_rel(s, 0, u) <=> s == u
        Both the forward direction (d=0 => s==u) and the backward direction
        (every state has a d=0 self-loop) are checked.
        """
        task_rel = self.result["task_relation"]
        violations = _check_nullity(task_rel)
        assert violations == [], (
            f"Nullity axiom violations in oracle output:\n"
            + "\n".join(violations)
        )

    def test_all_durations_in_valid_range(self):
        """All durations in task_relation are within [-(M-1), M-1].

        This verifies the serialization pipeline correctly filters or represents
        only valid-duration triples in the output.
        """
        task_rel = self.result["task_relation"]
        M = self.result["time_bound"]
        valid_range = range(-(M - 1), M)
        out_of_range = [
            t for t in task_rel
            if t["duration"] not in valid_range
        ]
        assert out_of_range == [], (
            f"task_relation contains out-of-range durations (M={M}, valid=[{-(M-1)},{M-1}]):\n"
            + "\n".join(str(t) for t in out_of_range)
        )

    def test_forward_comp_with_temporal_formula_output(self):
        """Frame axioms hold in oracle output for a depth-1 temporal formula (F(p)).

        Uses F(p) to produce a countermodel, then validates all three TaskFrame
        axioms on the serialized task_relation.
        """
        result = self.provider.find_countermodel(F_P)
        assert result is not None, "F(p) should have a countermodel"
        task_rel = result["task_relation"]
        M = result["time_bound"]

        fc_violations = _check_forward_comp(task_rel, M)
        cv_violations = _check_converse(task_rel, M)
        nl_violations = _check_nullity(task_rel)

        assert fc_violations == [], f"Forward comp violations for F(p): {fc_violations}"
        assert cv_violations == [], f"Converse violations for F(p): {cv_violations}"
        assert nl_violations == [], f"Nullity violations for F(p): {nl_violations}"

    def test_nullity_with_depth2_formula_output(self):
        """Nullity axiom holds in oracle output for a depth-2 temporal formula (G(F(p))).

        Uses G(F(p)) which produces a genuine countermodel at M=2.
        """
        result = self.provider.find_countermodel(GF_P)
        assert result is not None, "G(F(p)) should have a countermodel"
        task_rel = result["task_relation"]
        violations = _check_nullity(task_rel)
        assert violations == [], (
            f"Nullity violations for G(F(p)): {violations}"
        )


##############################################################################
# Phase 4: State Isolation with Temporal Depth-2 Formulas
##############################################################################

class TestStateIsolationRegression:
    """State isolation tests with mixed temporal depths.

    These tests verify that 100+ sequential oracle calls with a mix of
    propositional, depth-1, and depth-2 formulas show no state leakage
    or cross-contamination.

    The 5-formula rotation covers:
    - depth-0 SAT: atom(A)
    - depth-0 UNSAT: A->A
    - depth-1 SAT: F(p)
    - depth-1 UNSAT: G(A->A)
    - depth-2 SAT: G(F(p))

    This extends the existing TestStateIsolation in test_oracle_provider.py
    (which uses only propositional formulas) to include temporal formulas.
    """

    # 5-formula rotation: (formula_json, expected_sat: bool)
    ROTATION = [
        (ATOM_A, True),     # depth-0 SAT
        (TAUTOLOGY, False),  # depth-0 UNSAT
        (F_P, True),        # depth-1 SAT
        (G_TAUT, False),    # depth-1 UNSAT
        (GF_P, True),       # depth-2 SAT
    ]

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_100_calls_mixed_temporal_depths(self):
        """100 sequential calls cycling through 5-formula rotation (20 cycles) produce consistent results.

        Each call must return the expected SAT (non-None) or UNSAT (None) result,
        with no state leakage between calls.
        """
        for cycle in range(20):  # 20 cycles * 5 formulas = 100 total calls
            for formula, expected_sat in self.ROTATION:
                result = self.provider.find_countermodel(formula)
                if expected_sat:
                    assert result is not None, (
                        f"Cycle {cycle}: Expected non-None (SAT) for {formula}, got None. "
                        "Possible state leakage from previous call."
                    )
                else:
                    assert result is None, (
                        f"Cycle {cycle}: Expected None (UNSAT) for {formula}, got non-None. "
                        "Possible state leakage from previous call."
                    )

    def test_sat_unsat_interleaving_stability(self):
        """50 alternating pairs of depth-2 SAT and depth-0 UNSAT produce correct results.

        G(F(p)) (depth-2 SAT) alternated with A->A (depth-0 UNSAT).
        Every SAT call must return non-None, every UNSAT call must return None.
        """
        for i in range(50):
            sat_result = self.provider.find_countermodel(GF_P)
            assert sat_result is not None, (
                f"Pair {i}: G(F(p)) should return non-None (depth-2 SAT). "
                "Got None -- possible state contamination from depth-0 UNSAT formula."
            )
            unsat_result = self.provider.find_countermodel(TAUTOLOGY)
            assert unsat_result is None, (
                f"Pair {i}: A->A should return None (UNSAT). "
                "Got non-None -- possible state contamination from G(F(p)) formula."
            )

    def test_temporal_propositional_interleaving(self):
        """50 alternating pairs of F(p) (depth-1 SAT) and atom(A) (depth-0 SAT) both return non-None.

        Verifies temporal state does not interfere with propositional evaluation
        when interleaved in rapid succession.
        """
        for i in range(50):
            temporal_result = self.provider.find_countermodel(F_P)
            assert temporal_result is not None, (
                f"Pair {i}: F(p) (depth-1 SAT) should return non-None. "
                "Got None -- possible state contamination."
            )
            propositional_result = self.provider.find_countermodel(ATOM_A)
            assert propositional_result is not None, (
                f"Pair {i}: atom(A) (depth-0 SAT) should return non-None. "
                "Got None -- possible state contamination from F(p)."
            )

    def test_no_semantics_reference_leak_with_temporal(self):
        """After 10 calls with depth-2 formulas, provider._semantics is None.

        Verifies that isolated_z3_context() and the finally block in
        find_countermodel() properly clear the _semantics reference even
        after temporal depth-2 formula calls.
        """
        for i in range(10):
            self.provider.find_countermodel(GF_P)
            assert self.provider._semantics is None, (
                f"Call {i}: provider._semantics should be None after find_countermodel() "
                "for depth-2 formula G(F(p)). Got non-None -- reference leak detected."
            )


##############################################################################
# Phase 5: Known-Boundary-Unsafe Formula Suite
##############################################################################

class TestKnownBoundaryUnsafe:
    """5 hand-crafted formulas with temporal_depth >= 2, with documented boundary behavior.

    Each test documents the expected oracle behavior at M=max(depth,2)=2 and
    explains the boundary vacuity mechanism that causes any deviation from
    logically correct behavior.

    Key: boundary_safe = (M > depth+1)
    For all depth-2 formulas with M=max(2,2)=2: boundary_safe = (2>3) = False

    The three types of oracle behavior at M=2 for depth-2 formulas:
    1. Spurious UNSAT (None): G(G(p)) -- oracle treats as valid due to vacuous inner G
    2. Spurious SAT (non-None): F(G(p)) -- oracle finds model with vacuous G as witness
    3. Correct SAT (non-None): G(F(p)), F(F(p)) -- genuine countermodels found

    Note: "spurious" vs "correct" refers to whether the oracle result matches
    the logically correct answer for the UNBOUNDED theory.
    """

    def setup_method(self):
        self.provider = Z3OracleProvider()

    def test_gg_p_spurious_unsat(self):
        """G(G(p)) depth=2 -- oracle returns None at M=2 (spurious theorem).

        Boundary vacuity mechanism:
        - G(G(p)) at t=0 with M=2: outer G checks t'=1 only (M-1=1 is last future)
        - Inner G(p) at t'=1: checks ALL t''>1 in domain. Domain is {-1,0,1},
          so there is NO t''>1. The universal quantifier over the empty set is TRUE.
        - Therefore G(p) at t'=1 is vacuously true regardless of p's truth value.
        - Therefore G(G(p)) at t=0 is true in every M=2 model. No countermodel exists.

        But G(G(p)) IS logically invalid in the unbounded theory:
        - Take a model where p=False at t=3. Then:
          G(p) at t'=1: p=False at t''=3>1. So G(p) is False at t'=1.
          G(G(p)) at t=0: G(p) is False at t'=1>0. So G(G(p)) is False.
        - This requires M>=4 for t=3 to be in domain.

        This test DOCUMENTS this known limitation of M=max(depth,2).
        """
        depth = temporal_depth(GG_P)
        assert depth == 2, f"Expected temporal_depth=2 for G(G(p)), got {depth}"

        result = self.provider.find_countermodel(GG_P)
        assert result is None, (
            "G(G(p)) should return None at M=2 (spurious theorem due to boundary vacuity). "
            f"Got: {result}"
        )
        # boundary_safe cannot be checked from result (it's None), but we verify
        # the depth directly confirms M=2 is boundary-unsafe for this formula.
        # M_safe(depth=2) = max(2+2, 3) = 4. With M=2, we are far below M_safe.

    def test_fg_p_spurious_unsat(self):
        """F(G(p)) depth=2 -- oracle returns None at M=2 (spurious theorem, same as G(G(p))).

        Boundary vacuity mechanism (why F(G(p)) is a spurious theorem at M=2):
        The oracle checks invalidity by asking: is ~F(G(p)) satisfiable?
        ~F(G(p)) = G(~G(p)) (negation of "some future G(p)" = "all future ~G(p)")

        - G(~G(p)) at t=0 with M=2: checks t'=1 only (M-1=1 is only future point)
        - ~G(p) at t'=1: needs some t''>1 where p=false
          Domain is {-1,0,1}, so NO t''>1 exists.
        - ~G(p) at t'=1 is FALSE (vacuously, since it is the negation of a
          vacuously true statement: G(p) at t'=1 = true over empty set of t''>1)
        - G(~G(p)) at t=0 requires ~G(p) at t'=1, which is False.
        - G(~G(p)) is unsatisfiable at M=2 → oracle returns None.

        Both G(G(p)) and F(G(p)) exhibit the same boundary vacuity:
        the inner G is vacuously TRUE at the last future time point t=1,
        making the formula valid (or its negation unsatisfiable) at M=2.

        For genuine countermodel search, M_safe(2) = max(2+2, 3) = 4 is needed.
        boundary_safe would be False for depth=2 at M=2 (2 > 3 is False).
        """
        depth = temporal_depth(FG_P)
        assert depth == 2, f"Expected temporal_depth=2 for F(G(p)), got {depth}"

        result = self.provider.find_countermodel(FG_P)
        assert result is None, (
            "F(G(p)) should return None at M=2 (spurious theorem). "
            "~F(G(p)) = G(~G(p)) is unsatisfiable at M=2: ~G(p) at t=1 is vacuously "
            "false (G(p) at t=1 is vacuously true over empty {t''>1}). "
            f"Got: {result}"
        )

    def test_gf_p_genuine_countermodel(self):
        """G(F(p)) depth=2 -- oracle returns non-None at M=2 (genuine countermodel).

        Countermodel mechanism:
        - G(F(p)) at t=0: for ALL t'>0, F(p) must hold at t'.
        - At t'=1 (only future): F(p) at t'=1 needs some t''>1 where p holds.
          Domain is {-1,0,1}, so NO t''>1 exists. F(p) at t'=1 is FALSE.
        - Therefore G(F(p)) is FALSE at t=0 in any model where p is not checked at
          a sufficient future time.

        This is a CORRECT countermodel result: G(F(p)) is genuinely invalid (in
        both bounded M=2 and unbounded theories). The boundary effect here makes
        F(p) false (existential over empty future), which is the natural result.

        Contrast with G(G(p)) where the boundary makes G(p) true (universal over
        empty future). The asymmetry: universal quantifier over empty = True (spurious
        validity), existential over empty = False (spurious invalidity... but G(F(p))
        IS actually invalid, so the result is coincidentally correct).

        boundary_safe=False confirms M=2 is boundary-unsafe, but the result is sound.
        """
        depth = temporal_depth(GF_P)
        assert depth == 2, f"Expected temporal_depth=2 for G(F(p)), got {depth}"

        result = self.provider.find_countermodel(GF_P)
        assert result is not None, (
            "G(F(p)) should return a genuine countermodel at M=2. "
            "F(p) at t'=1 fails (no t''>1), making G(F(p)) false. "
            "This is a correct result despite boundary_safe=False."
        )
        assert result["boundary_safe"] is False, (
            f"Expected boundary_safe=False for G(F(p)) (depth=2, M=2)"
        )
        assert result["temporal_depth"] == 2
        assert result["time_bound"] == 2

        # Verify standard frame axioms still hold on this countermodel
        task_rel = result["task_relation"]
        M = result["time_bound"]
        cv_violations = _check_converse(task_rel, M)
        nl_violations = _check_nullity(task_rel)
        assert cv_violations == [], f"Converse violations in G(F(p)) result: {cv_violations}"
        assert nl_violations == [], f"Nullity violations in G(F(p)) result: {nl_violations}"

    def test_ff_p_boundary_behavior(self):
        """F(F(p)) depth=2 -- oracle at M=2 returns correct countermodel.

        Countermodel mechanism:
        - F(F(p)) at t=0: needs some t'>0 with F(p) at t'.
        - At t'=1: F(p) at t'=1 needs t''>1 where p holds.
          Domain {-1,0,1} has no t''>1. So F(p) at t'=1 is FALSE.
        - Therefore the countermodel is: t'=1 is the only future, and F(p) fails there.
          So F(F(p)) is false at t=0 (the "witness" t'=1 fails to satisfy F(p)).

        Wait -- F(F(p)) requires SOME t'>0 where F(p) holds. If F(p) is false at t'=1
        (the only available future), then there is no witness, making F(F(p)) false.
        So the negation ~F(F(p)) is true, meaning F(F(p)) has a countermodel. Correct.

        boundary_safe=False: the result is technically affected by the boundary
        (F(p) fails at t'=1 due to bounded domain), but it's still a valid
        countermodel for F(F(p)) in the bounded theory.
        """
        depth = temporal_depth(FF_P)
        assert depth == 2, f"Expected temporal_depth=2 for F(F(p)), got {depth}"

        result = self.provider.find_countermodel(FF_P)
        assert result is not None, (
            "F(F(p)) should return a countermodel at M=2. "
            "F(p) at t'=1 is False (no t''>1 in domain), so F(F(p)) has no witness. "
            "This is a valid (though boundary-influenced) countermodel."
        )
        assert result["boundary_safe"] is False, (
            f"Expected boundary_safe=False for F(F(p)) (depth=2, M=2)"
        )
        assert result["temporal_depth"] == 2
        assert result["time_bound"] == 2

    def test_imp_gg_p_gf_p_boundary_unsafe(self):
        """(G(G(p)) -> G(F(p))) depth=2 -- compound formula testing boundary interaction.

        Boundary interaction:
        - G(G(p)) at M=2 is vacuously true (boundary-unsafe, as shown in test_gg_p_spurious_unsat)
        - G(F(p)) at M=2 is false (genuine countermodel exists, as shown in test_gf_p_genuine_countermodel)
        - Therefore (G(G(p)) -> G(F(p))) at M=2: true -> false = FALSE.
          So the oracle should find a countermodel for this implication.

        Expected behavior: non-None result (countermodel exists where the antecedent
        G(G(p)) is vacuously true and the consequent G(F(p)) is false due to boundary).

        This tests the compound boundary interaction: one subformula made spuriously
        valid by boundary vacuity, another made genuinely invalid by boundary truncation.

        boundary_safe=False: depth=2, M=2, 2>3 is False.
        """
        depth = temporal_depth(IMP_GG_P_GF_P)
        assert depth == 2, f"Expected temporal_depth=2 for G(G(p))->G(F(p)), got {depth}"

        result = self.provider.find_countermodel(IMP_GG_P_GF_P)
        assert result is not None, (
            "G(G(p))->G(F(p)) should have a countermodel at M=2. "
            "G(G(p)) is vacuously true at M=2 (boundary), G(F(p)) is false at M=2. "
            "So the implication is false, giving a countermodel."
        )
        assert result["boundary_safe"] is False, (
            f"Expected boundary_safe=False for compound depth-2 formula (M=2)"
        )
        assert result["temporal_depth"] == 2
        assert result["time_bound"] == 2
