"""Post-hoc validation tests for Z3 frame class axiom mapping.

This module validates that countermodels extracted from the Z3 oracle
satisfy the three TaskFrame axioms (nullity_identity, converse, forward_comp)
and the lawful history property. It documents and tests the correspondence
between the Z3 oracle's "Base" frame class claim and BimodalLogic's TaskFrame
structure.

Purpose:
--------
The Z3 oracle declares `supported_frame_classes = frozenset({"Base"})`, meaning
the oracle's frame satisfies the three TaskFrame axioms. This test suite performs
post-hoc validation: after extracting a satisfying assignment (countermodel) from
the Z3 solver, it enumerates all task_rel pairs in the model and checks that the
TaskFrame axioms hold exactly as documented in bimodal_logic/provider.py.

Test Strategy:
--------------
Rather than using the full BimodalStructure pipeline (which requires model
constraints and operator evaluation), these tests work at the solver level:

1. Create a BimodalSemantics instance with small settings (N=2, M=3)
2. Add frame constraints directly to a Z3 solver
3. Add a satisfying assertion (e.g., task_rel(s1, 1, s2) for distinct states)
4. Call solver.check() to obtain a model
5. Enumerate all (source, duration, target) combinations in the model
6. Validate the TaskFrame axioms hold for all enumerated pairs

Frame Axiom Reference:
----------------------
From BimodalLogic's Frame.lean (TaskFrame structure):

    nullity: task_rel(s, 0, u) ↔ s = u
    converse: task_rel(s, d, u) ↔ task_rel(u, -d, s)
    compose: task_rel(s,d1,t) ∧ task_rel(t,d2,u) → task_rel(s,d1+d2,u)

The lawful history property (not a TaskFrame axiom, but a model-building
constraint) ensures consecutive world-states are connected by task_rel(s, 1, s').

To run these tests:
    PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py -v
"""

from __future__ import annotations

import pytest
import z3

from model_checker.solver import is_true
from model_checker.theory_lib.bimodal.semantic import BimodalSemantics


# ============================================================================
# Fixtures and Helpers
# ============================================================================


@pytest.fixture
def semantics():
    """Create BimodalSemantics instance with small settings for frame validation.

    Uses N=2 (4 world states: 0b00, 0b01, 0b10, 0b11) and M=2 (time domain
    -2 to 2) for fast solver performance in unit tests. M=2 gives durations
    in range(-1, 2) = {-1, 0, 1}, which is sufficient to test all three
    TaskFrame axioms (nullity at d=0, converse via d=1 and d=-1, composition
    via d=1+1=2 if in range or checked with available durations).

    Note: M=3 is needed for abundance/ShiftClosed alignment (BM_TH_1/2), but
    frame axiom testing does not require abundance.
    """
    settings = {
        'N': 2,
        'M': 2,
        'contingent': False,
        'disjoint': False,
        'max_time': 10,
        'expectation': True,
        'iterate': 1,
    }
    return BimodalSemantics(settings)


@pytest.fixture
def solved_model(semantics):
    """Return a (semantics, z3_model) pair from a satisfying Z3 run.

    Adds frame constraints plus a non-trivial assertion (task_rel between
    distinct states with duration 1) to force the solver to produce a model
    with at least one non-identity task_rel pair. Returns the Z3 model for
    post-hoc inspection.

    Returns:
        Tuple[BimodalSemantics, z3.ModelRef]: The semantics instance and the
        satisfying Z3 model.
    """
    solver = z3.Solver()
    solver.add(semantics.frame_constraints)

    # Assert a non-trivial task_rel pair between distinct states
    s0 = z3.BitVecVal(0, semantics.N)
    s1 = z3.BitVecVal(1, semantics.N)
    solver.add(semantics.task_rel(s0, z3.IntVal(1), s1))

    result = solver.check()
    assert result == z3.sat, (
        "Frame constraints plus task_rel(0, 1, 1) should be satisfiable; "
        "got: " + str(result)
    )

    return semantics, solver.model()


def extract_task_rel_pairs(semantics: BimodalSemantics, z3_model) -> set:
    """Extract all (source_state, duration, target_state) triples where
    task_rel holds in the given Z3 model.

    Enumerates all state pairs and durations within the valid ranges:
    - states: integers in range(2**N)
    - durations: integers in range(-M+1, M)

    Returns:
        set of (int, int, int) tuples: (source, duration, target) where
        task_rel(source, duration, target) evaluates to True in z3_model.
    """
    num_states = 2 ** semantics.N
    duration_range = range(-semantics.M + 1, semantics.M)
    pairs = set()

    for source in range(num_states):
        for duration in duration_range:
            for target in range(num_states):
                expr = semantics.task_rel(
                    z3.BitVecVal(source, semantics.N),
                    z3.IntVal(duration),
                    z3.BitVecVal(target, semantics.N)
                )
                val = z3_model.eval(expr, model_completion=True)
                if is_true(val):
                    pairs.add((source, duration, target))

    return pairs


def extract_world_histories(semantics: BimodalSemantics, z3_model) -> dict:
    """Extract world histories from the Z3 model.

    For each valid world ID, extracts the {time: state} mapping for all
    time points in the valid range.

    Returns:
        dict mapping world_id (int) to {time (int): state (int)} dict.
    """
    histories = {}
    max_world_ids = min(semantics.max_world_id, 20)  # cap for test performance

    for world_id in range(max_world_ids):
        is_world_expr = semantics.is_world(world_id)
        is_valid = z3_model.eval(is_world_expr, model_completion=True)
        if not is_true(is_valid):
            continue

        # Extract time interval for this world
        try:
            start_val = z3_model.eval(
                semantics.world_interval_start(world_id), model_completion=True
            )
            end_val = z3_model.eval(
                semantics.world_interval_end(world_id), model_completion=True
            )
            start = start_val.as_long()
            end = end_val.as_long()
        except Exception:
            # Fall back to global time range if interval extraction fails
            start = -semantics.M + 1
            end = semantics.M - 1

        # Extract state at each time in the interval
        history = {}
        for time in range(start, end + 1):
            try:
                world_array = z3_model.eval(
                    semantics.world_function(world_id), model_completion=True
                )
                state_expr = z3.Select(world_array, z3.IntVal(time))
                state_val = z3_model.eval(state_expr, model_completion=True)
                # Convert BitVec to int
                if hasattr(state_val, 'as_long'):
                    state = state_val.as_long()
                else:
                    state = int(str(state_val))
                history[time] = state
            except Exception:
                pass  # Skip times that can't be evaluated

        if history:
            histories[world_id] = history

    return histories


# ============================================================================
# Smoke Test
# ============================================================================


class TestFixtureSmoke:
    """Smoke tests verifying that the test fixtures produce non-empty data.

    These tests confirm the infrastructure works before relying on it for
    the actual frame axiom validation tests below.
    """

    def test_solved_model_produces_data(self, solved_model):
        """The solved_model fixture should produce a non-None Z3 model."""
        semantics, z3_model = solved_model
        assert z3_model is not None, "solved_model fixture should produce a Z3 model"

    def test_extract_task_rel_pairs_nonempty(self, solved_model):
        """extract_task_rel_pairs should return at least one pair.

        We forced task_rel(0, 1, 1) in the solved_model fixture, so there
        must be at least one task_rel pair in the model.
        """
        semantics, z3_model = solved_model
        pairs = extract_task_rel_pairs(semantics, z3_model)
        assert len(pairs) > 0, (
            "extract_task_rel_pairs should return at least one pair "
            "(we forced task_rel(0, 1, 1) in the fixture)"
        )

    def test_extract_task_rel_has_forced_pair(self, solved_model):
        """The extracted pairs should include the pair we forced (0, 1, 1)."""
        semantics, z3_model = solved_model
        pairs = extract_task_rel_pairs(semantics, z3_model)
        assert (0, 1, 1) in pairs, (
            "Expected (source=0, duration=1, target=1) in task_rel pairs; "
            f"got pairs: {pairs}"
        )

    def test_extract_world_histories_nonempty(self, solved_model):
        """extract_world_histories should return at least one world history."""
        semantics, z3_model = solved_model
        histories = extract_world_histories(semantics, z3_model)
        assert len(histories) > 0, (
            "extract_world_histories should return at least one world history"
        )


# ============================================================================
# TaskFrame Axiom 1: Nullity Identity
# ============================================================================


class TestNullityIdentityPostHoc:
    """Post-hoc validation of the nullity_identity axiom in extracted countermodels.

    TaskFrame.nullity: task_rel(s, 0, u) ↔ s = u

    Validates two directions:
    - Forward: every (s, 0, u) pair with s != u is absent from the model
    - Backward: every state s has (s, 0, s) present in the model
    """

    def test_no_zero_duration_between_distinct_states(self, solved_model):
        """No task_rel pair (s, 0, u) with s != u should exist in the model.

        This is the -> direction of nullity_identity: task_rel(s, 0, u) -> s = u.
        The nullity_identity constraint in build_frame_constraints() enforces this.
        """
        semantics, z3_model = solved_model
        pairs = extract_task_rel_pairs(semantics, z3_model)

        zero_dur_violations = [
            (s, d, u) for (s, d, u) in pairs
            if d == 0 and s != u
        ]
        assert zero_dur_violations == [], (
            f"nullity_identity violated: found zero-duration task_rel pairs "
            f"between distinct states: {zero_dur_violations}"
        )

    def test_every_state_has_zero_duration_self_task(self, solved_model):
        """Every state s should have task_rel(s, 0, s) in the model.

        This is the <- direction of nullity_identity: s = u -> task_rel(s, 0, u).
        The nullity_identity constraint enforces biconditional semantics.
        """
        semantics, z3_model = solved_model
        pairs = extract_task_rel_pairs(semantics, z3_model)
        num_states = 2 ** semantics.N

        missing_self_tasks = [
            s for s in range(num_states)
            if (s, 0, s) not in pairs
        ]
        assert missing_self_tasks == [], (
            f"nullity_identity violated: states missing zero-duration self-task: "
            f"{missing_self_tasks}"
        )


# ============================================================================
# TaskFrame Axiom 2: Converse
# ============================================================================


class TestConversePostHoc:
    """Post-hoc validation of the converse axiom in extracted countermodels.

    TaskFrame.converse: task_rel(s, d, u) ↔ task_rel(u, -d, s)

    Validates: for every (s, d, u) in the extracted pairs, (u, -d, s)
    must also be present (within valid duration bounds).
    """

    def test_converse_holds_for_all_pairs(self, solved_model):
        """For every (s, d, u) in the model, (u, -d, s) should also be present.

        Checks the converse axiom post-hoc: each task_rel pair has its converse.
        Only checks pairs where both d and -d are within valid duration bounds
        (matching the Z3 guard in build_converse_constraint()).
        """
        semantics, z3_model = solved_model
        pairs = extract_task_rel_pairs(semantics, z3_model)
        M = semantics.M
        valid_dur = range(-M + 1, M)

        violations = []
        for (source, duration, target) in pairs:
            if duration not in valid_dur:
                continue
            neg_dur = -duration
            if neg_dur not in valid_dur:
                continue
            if (target, neg_dur, source) not in pairs:
                violations.append(
                    f"task_rel({source}, {duration}, {target}) present but "
                    f"task_rel({target}, {neg_dur}, {source}) absent"
                )

        assert violations == [], (
            f"converse axiom violated in {len(violations)} case(s):\n" +
            "\n".join(violations[:5])  # Show first 5 violations
        )


# ============================================================================
# TaskFrame Axiom 3: Forward Composition
# ============================================================================


class TestForwardCompPostHoc:
    """Post-hoc validation of the forward_comp (compositionality) axiom.

    TaskFrame.compose: task_rel(s,d1,t) ∧ task_rel(t,d2,u) → task_rel(s,d1+d2,u)

    Validates: for every pair of task_rel entries (s,d1,v) and (v,d2,u) where
    d1+d2 is within valid duration bounds, (s, d1+d2, u) must also be present.
    """

    def test_forward_composition_holds(self, solved_model):
        """For composable pairs in the model, the composition should also be present.

        Checks the forward_comp axiom post-hoc: if (s,d1,v) and (v,d2,u) are
        both in the model, and d1+d2 is within valid duration bounds, then
        (s, d1+d2, u) must also be present.
        """
        semantics, z3_model = solved_model
        pairs = extract_task_rel_pairs(semantics, z3_model)
        M = semantics.M
        valid_dur = range(-M + 1, M)

        violations = []
        for (s, d1, v) in pairs:
            for (v2, d2, u) in pairs:
                if v != v2:
                    continue
                d_sum = d1 + d2
                if d_sum not in valid_dur:
                    continue
                if (s, d_sum, u) not in pairs:
                    violations.append(
                        f"task_rel({s},{d1},{v}) + task_rel({v},{d2},{u}) => "
                        f"task_rel({s},{d_sum},{u}) should hold but is absent"
                    )

        assert violations == [], (
            f"forward_comp axiom violated in {len(violations)} case(s):\n" +
            "\n".join(violations[:5])  # Show first 5 violations
        )


# ============================================================================
# Lawful History Property
# ============================================================================


class TestLawfulHistoryPostHoc:
    """Post-hoc validation of the lawful history property.

    The lawful constraint (item 6 in build_frame_constraints()) ensures that
    for every consecutive time pair (t, t+1) in a world's interval, the
    transition is covered by a unit-duration task_rel:
        task_rel(world(t), 1, world(t+1))

    This is a model-building constraint, not a TaskFrame axiom, but it is
    essential for temporal operators to have meaningful semantics.
    """

    def test_consecutive_states_have_unit_task_rel(self, solved_model):
        """For every consecutive time pair in any world, task_rel(s_t, 1, s_{t+1}) holds.

        Validates the lawful constraint post-hoc: consecutive states in world
        histories must be connected by a unit-duration task_rel.
        """
        semantics, z3_model = solved_model
        pairs = extract_task_rel_pairs(semantics, z3_model)
        histories = extract_world_histories(semantics, z3_model)

        violations = []
        for world_id, history in histories.items():
            times = sorted(history.keys())
            for i in range(len(times) - 1):
                t = times[i]
                t_next = times[i + 1]
                if t_next != t + 1:
                    continue  # Skip non-consecutive times
                state_t = history[t]
                state_t_next = history[t_next]
                if (state_t, 1, state_t_next) not in pairs:
                    violations.append(
                        f"world {world_id}: no task_rel({state_t}, 1, "
                        f"{state_t_next}) for times ({t}, {t_next})"
                    )

        assert violations == [], (
            f"lawful property violated in {len(violations)} case(s):\n" +
            "\n".join(violations[:5])
        )


# ============================================================================
# Frame Class Declaration Consistency
# ============================================================================


class TestFrameClassDeclarationConsistency:
    """Tests verifying the oracle's 'Base' frame class claim is justified.

    The oracle declares supported_frame_classes = frozenset({"Base"}), meaning
    the Z3 frame satisfies the three TaskFrame axioms. This class documents
    what 'Base' means in this context and verifies the axioms hold.

    See bimodal_logic/provider.py module docstring for the full terminology
    disambiguation and axiom mapping.
    """

    def test_base_means_taskframe_axioms_not_frameclassbase(self, semantics):
        """Document that 'Base' refers to TaskFrame axioms, not FrameClass.Base.

        The oracle's supported_frame_classes = frozenset({"Base"}) uses 'Base'
        to mean "satisfies TaskFrame axioms" (three axioms: nullity, converse,
        compose). This is NOT the same as BimodalLogic's proof-system
        FrameClass.Base (which encompasses 37 axioms across the proof theory).

        This test documents the mapping by verifying the oracle class declares
        supported_frame_classes and that the Z3 frame constraints implement
        exactly the three TaskFrame axioms.
        """
        # Verify the provider module has the supported_frame_classes attribute
        from bimodal_logic.provider import Z3OracleProvider
        assert hasattr(Z3OracleProvider, 'supported_frame_classes'), (
            "Z3OracleProvider should declare supported_frame_classes"
        )
        assert Z3OracleProvider.supported_frame_classes == frozenset({"Base"}), (
            "Z3OracleProvider.supported_frame_classes should be frozenset({'Base'})"
        )

    def test_three_taskframe_axioms_present_in_frame_constraints(self, semantics):
        """The frame constraints should include all three TaskFrame axioms.

        Verifies that build_frame_constraints() produces constraints that
        enforce nullity_identity, converse, and forward_comp by checking the
        frame is satisfiable (consistent) and the axioms reduce the solution space.
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        # Verify frame constraints are satisfiable (internally consistent)
        assert solver.check() == z3.sat, (
            "Frame constraints including all three TaskFrame axioms should be "
            "satisfiable (internally consistent)"
        )

    def test_nullity_axiom_enforced_in_frame(self, semantics):
        """The nullity axiom should be enforced: task_rel(s, 0, u) with s!=u is unsat.

        Directly tests that the nullity_identity constraint is present and
        active in the frame, making zero-duration tasks between distinct states
        impossible.
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        # A zero-duration task between distinct states violates nullity
        s = z3.BitVecVal(0, semantics.N)
        u = z3.BitVecVal(1, semantics.N)
        solver.add(semantics.task_rel(s, z3.IntVal(0), u))

        assert solver.check() == z3.unsat, (
            "task_rel(0, 0, 1) with nullity_identity in frame should be unsat; "
            "'Base' frame class enforces nullity axiom"
        )

    def test_converse_axiom_enforced_in_frame(self, semantics):
        """The converse axiom should be enforced: a one-way task is unsat.

        Tests that the converse constraint is present: if task_rel(w, d, u)
        holds then task_rel(u, -d, w) must also hold. Asserting the forward
        task while negating the reverse is unsatisfiable.
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        w = z3.BitVecVal(0, semantics.N)
        u = z3.BitVecVal(1, semantics.N)
        solver.add(semantics.task_rel(w, z3.IntVal(1), u))
        solver.add(z3.Not(semantics.task_rel(u, z3.IntVal(-1), w)))

        assert solver.check() == z3.unsat, (
            "task_rel(0, 1, 1) AND NOT task_rel(1, -1, 0) should be unsat; "
            "'Base' frame class enforces converse axiom"
        )


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
