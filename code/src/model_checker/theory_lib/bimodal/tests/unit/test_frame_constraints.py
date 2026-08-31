"""Tests for frame constraints in BimodalSemantics.

Tests verify correctness of five frame constraint builder methods:
  1. build_nullity_identity_constraint() -- task_rel(w, 0, u) <-> w == u
  2. build_converse_constraint() -- task_rel(w, d, u) <-> task_rel(u, -d, w)
  3. build_forward_comp_constraint() -- compositionality of sequential tasks
     (the <- half; also known as Compositionality's forward direction)
  4. build_seriality_constraint() -- every world state has a successor and
     a predecessor at every valid non-negative duration
  5. build_interpolation_constraint() -- the -> half of Compositionality:
     if task_rel(w, d1+d2, v) then an intermediate state exists at d1/d2

Each class tests a constraint individually and also verifies interactions
with the existing 'lawful' constraint. Seriality and Interpolation use the
Skolemized encoding (one top-level ForAll, existential eliminated by a
witness function) -- the nested ForAll/Exists reading is a measured
regression on BM_TH_3/BM_TH_4 at M=2 and is never used.

ProofChecker Alignment: These constraints correspond to TaskFrame axioms
and the Compositional typeclass from Frame.lean (lines 68-114).

To run these tests:
  pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py -v
"""

import pytest
import z3

from model_checker.theory_lib.bimodal.semantic import BimodalSemantics


@pytest.fixture
def semantics():
    """Create BimodalSemantics instance for testing frame constraints.

    Uses N=2 (4 world states) and M=2 (time domain -2 to 2) for a compact
    but representative solver environment. N=2 is sufficient to distinguish
    distinct states (s1 != s2) and test compositionality.
    """
    settings = {
        'N': 2,
        'M': 2,
        'contingent': False,
        'disjoint': False,
        'max_time': 1,
        'expectation': True,
        'iterate': 1,
    }
    return BimodalSemantics(settings)


@pytest.fixture
def semantics_m3():
    """Create BimodalSemantics instance with M=3 (time domain -3 to 3).

    TestInterpolation needs a decomposition d1=d2=1 (sum=2) to remain within
    is_valid_duration's guard; M=2's window (-2, 2) excludes duration 2
    entirely (valid durations are only {-1, 0, 1}), which would make
    build_interpolation_constraint's premise vacuously false for any
    non-trivial (both d1, d2 nonzero) decomposition. M=3 widens the window
    to {-2, -1, 0, 1, 2}, admitting d1=d2=1.

    Sets temporal_depth=0 to skip capped_skolem_abundance_constraint.
    Verified independently (both against this task's new builders and
    against the pre-existing, unmodified tree at the commit before this
    task's Phase 4) that checking bare frame_constraints satisfiability at
    M=3 with the abundance constraint active and no problem-specific
    ground terms to seed MBQI instantiation is already pathological
    (60s+, pre-existing, unrelated to Seriality/Interpolation) --
    temporal_depth=0 sidesteps that pre-existing issue and is not a
    workaround for anything this task's constraints introduce. With
    temporal_depth=0, the same positive/negative Interpolation checks
    below resolve in well under a second.
    """
    settings = {
        'N': 2,
        'M': 3,
        'contingent': False,
        'disjoint': False,
        'max_time': 1,
        'expectation': True,
        'iterate': 1,
        'temporal_depth': 0,
    }
    return BimodalSemantics(settings)


class TestNullityIdentity:
    """Tests for the nullity_identity constraint: task_rel(w, 0, u) <-> w == u.

    The nullity_identity constraint enforces that zero-duration tasks relate
    a state only to itself (and always do so).
    """

    def test_zero_duration_self_task(self, semantics):
        """task_rel(s, 0, s) should hold given frame constraints (satisfiable)."""
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        s = z3.BitVecVal(1, semantics.N)
        solver.add(semantics.task_rel(s, z3.IntVal(0), s))

        assert solver.check() == z3.sat, (
            "task_rel(s, 0, s) should be satisfiable given nullity_identity constraint"
        )

    def test_zero_duration_different_states_unsat(self, semantics):
        """task_rel(s1, 0, s2) with s1 != s2 should be unsatisfiable.

        The nullity_identity constraint forces task_rel(w, 0, u) -> w == u,
        so any zero-duration task between distinct states is unsatisfiable.
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        s1 = z3.BitVecVal(1, semantics.N)
        s2 = z3.BitVecVal(2, semantics.N)
        solver.add(semantics.task_rel(s1, z3.IntVal(0), s2))

        assert solver.check() == z3.unsat, (
            "task_rel(s1, 0, s2) with s1 != s2 should be unsatisfiable "
            "given nullity_identity constraint"
        )


class TestConverse:
    """Tests for the converse constraint: task_rel(w, d, u) <-> task_rel(u, -d, w).

    The converse constraint enforces time reversal symmetry: going from w to u
    in duration d is equivalent to going from u to w in duration -d.
    """

    def test_converse_symmetry(self, semantics):
        """task_rel(w, d, u) together with task_rel(u, -d, w) should be satisfiable.

        Verifies the forward direction: if we add task_rel(w, 1, u) as an
        assumption, we can also add task_rel(u, -1, w) and remain consistent
        (the converse constraint enforces this).
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        w = z3.BitVecVal(0, semantics.N)
        u = z3.BitVecVal(1, semantics.N)

        # Both forward and reverse tasks should be simultaneously satisfiable
        solver.add(semantics.task_rel(w, z3.IntVal(1), u))
        solver.add(semantics.task_rel(u, z3.IntVal(-1), w))

        assert solver.check() == z3.sat, (
            "task_rel(w, 1, u) AND task_rel(u, -1, w) should be jointly satisfiable"
        )

    def test_converse_exclusion(self, semantics):
        """task_rel(w, d, u) AND NOT task_rel(u, -d, w) should be unsatisfiable.

        The converse constraint is bidirectional, so the presence of
        task_rel(w, d, u) forces task_rel(u, -d, w) to hold. Negating
        the converse while asserting the forward task is a contradiction.
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        w = z3.BitVecVal(0, semantics.N)
        u = z3.BitVecVal(1, semantics.N)

        solver.add(semantics.task_rel(w, z3.IntVal(1), u))
        solver.add(z3.Not(semantics.task_rel(u, z3.IntVal(-1), w)))

        assert solver.check() == z3.unsat, (
            "task_rel(w, 1, u) AND NOT task_rel(u, -1, w) should be unsatisfiable "
            "given converse constraint"
        )


class TestForwardComp:
    """Tests for the forward_comp (compositionality) constraint.

    The compositionality constraint enforces that sequential tasks compose:
    if task_rel(w, d1, v) and task_rel(v, d2, u) then task_rel(w, d1+d2, u).
    """

    def test_composition_exists(self, semantics):
        """Given task_rel(w,d1,v) and task_rel(v,d2,u), task_rel(w,d1+d2,u) holds.

        Verifies the composition is satisfiable when the two component tasks exist.
        The forward_comp constraint ensures the composed task is derivable.
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        w = z3.BitVecVal(0, semantics.N)
        v = z3.BitVecVal(1, semantics.N)
        u = z3.BitVecVal(2, semantics.N)

        # Assert both component tasks
        solver.add(semantics.task_rel(w, z3.IntVal(1), v))
        solver.add(semantics.task_rel(v, z3.IntVal(1), u))

        # The composed task should also hold
        solver.add(semantics.task_rel(w, z3.IntVal(2), u))

        assert solver.check() == z3.sat, (
            "task_rel(w, 1, v) AND task_rel(v, 1, u) AND task_rel(w, 2, u) "
            "should be jointly satisfiable via forward_comp"
        )

    def test_composition_chain(self, semantics):
        """Derive task_rel(s0, 2, s2) from two unit-duration tasks via lawful.

        The lawful constraint establishes unit-duration tasks for consecutive
        world states. The forward_comp constraint then derives the composed
        two-step task relation.
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        # Use concrete state values for a 2-bit domain
        s0 = z3.BitVecVal(0, semantics.N)
        s1 = z3.BitVecVal(1, semantics.N)
        s2 = z3.BitVecVal(2, semantics.N)

        # Assert two unit-duration steps (consistent with lawful constraint)
        solver.add(semantics.task_rel(s0, z3.IntVal(1), s1))
        solver.add(semantics.task_rel(s1, z3.IntVal(1), s2))

        # The two-step composition should exist
        solver.add(semantics.task_rel(s0, z3.IntVal(2), s2))

        assert solver.check() == z3.sat, (
            "task_rel chain s0->1->s1->1->s2 together with task_rel(s0, 2, s2) "
            "should be jointly satisfiable via forward_comp"
        )


class TestFrameConstraintsJointSatisfiability:
    """Guards against a jointly-UNSAT frame once Seriality and Interpolation
    are added to build_frame_constraints().

    This must be checked before any other per-axiom test: if the full frame
    constraint set (including the two new axioms) were UNSAT, every other
    test in this module and in test_frame_class_mapping.py would pass
    vacuously (an UNSAT solver.add() + solver.check() reports unsat for any
    additional assertion, positive or negative alike).
    """

    def test_frame_constraints_jointly_satisfiable(self, semantics):
        """semantics.frame_constraints should be satisfiable with no
        additional problem-specific assertions."""
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        assert solver.check() == z3.sat, (
            "frame_constraints (including Seriality and Interpolation) should "
            "be jointly satisfiable with no additional assertions -- an unsat "
            "result here would make every other frame-constraint test pass "
            "vacuously"
        )


class TestSeriality:
    """Tests for the seriality constraint: every world state has a
    successor and a predecessor at every valid non-negative duration.

    build_seriality_constraint() is Skolemized: one top-level
    ForAll([w, x]), two Skolem functions (serial_succ, serial_pred), no
    nested Exists.
    """

    def test_successor_and_predecessor_exist(self, semantics):
        """For a concrete world state and a valid non-negative duration,
        both a successor and a predecessor should be derivable
        (satisfiable) -- exercising Seriality's positive case."""
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        w = z3.BitVecVal(0, semantics.N)
        x = z3.IntVal(1)
        succ = z3.BitVec('test_serial_succ', semantics.N)
        pred = z3.BitVec('test_serial_pred', semantics.N)

        solver.add(semantics.task_rel(w, x, succ))
        solver.add(semantics.task_rel(pred, x, w))

        assert solver.check() == z3.sat, (
            "A successor and a predecessor for task_rel(w, 1, _) and "
            "task_rel(_, 1, w) should be jointly satisfiable given Seriality"
        )

    def test_no_successor_unsat(self, semantics):
        """Asserting that NO successor exists for a concrete (w, x) inside
        Seriality's guard should be unsatisfiable.

        Seriality's ForAll([w, x]) guarantees a successor for every world
        state w at every valid non-negative duration x, so negating "some u
        with task_rel(w, x, u)" for all u in the (small, N=2) state space is
        a contradiction.
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        w = z3.BitVecVal(0, semantics.N)
        x = z3.IntVal(1)
        num_states = 2 ** semantics.N
        for u in range(num_states):
            solver.add(z3.Not(semantics.task_rel(w, x, z3.BitVecVal(u, semantics.N))))

        assert solver.check() == z3.unsat, (
            "Denying every possible successor of task_rel(w, 1, _) over the "
            "full (finite) state space should be unsatisfiable given Seriality"
        )


class TestInterpolation:
    """Tests for the interpolation constraint: the -> half of
    Compositionality -- if task_rel(w, d1+d2, v) holds under the duration
    guards, an intermediate state u exists with task_rel(w, d1, u) and
    task_rel(u, d2, v).

    build_interpolation_constraint() is Skolemized: one top-level
    ForAll([w, v, d1, d2]), one Skolem witness function, no nested Exists
    (the nested reading is a measured BM_TH_3/BM_TH_4 regression at M=2).
    """

    def test_intermediate_state_exists(self, semantics_m3):
        """Given task_rel(w, 2, v) under valid duration guards (d1=d2=1),
        an intermediate state u with task_rel(w,1,u) and task_rel(u,1,v)
        should be derivable (satisfiable) -- Interpolation's positive case.

        Uses the semantics_m3 fixture (M=3) so that d1=d2=1 (sum=2) is
        within is_valid_duration's guard; M=2's window excludes duration 2.
        """
        semantics = semantics_m3
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        w = z3.BitVecVal(0, semantics.N)
        v = z3.BitVecVal(1, semantics.N)
        solver.add(semantics.task_rel(w, z3.IntVal(2), v))

        # Interpolation guarantees SOME intermediate state; assert the
        # disjunction over the (small, N=2) state space is satisfiable.
        num_states = 2 ** semantics.N
        candidates = [
            z3.And(
                semantics.task_rel(w, z3.IntVal(1), z3.BitVecVal(u, semantics.N)),
                semantics.task_rel(z3.BitVecVal(u, semantics.N), z3.IntVal(1), v)
            )
            for u in range(num_states)
        ]
        solver.add(z3.Or(*candidates))

        assert solver.check() == z3.sat, (
            "task_rel(w, 2, v) together with 'some intermediate state at "
            "d1=1, d2=1' should be jointly satisfiable given Interpolation"
        )

    def test_no_intermediate_state_unsat(self, semantics_m3):
        """Asserting task_rel(w, 2, v) while denying every possible
        intermediate state (over the full, small state space) at d1=d2=1
        should be unsatisfiable given Interpolation.

        Uses the semantics_m3 fixture (M=3); see test_intermediate_state_exists
        for why M=2's guard window would make this vacuous.
        """
        semantics = semantics_m3
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        w = z3.BitVecVal(0, semantics.N)
        v = z3.BitVecVal(1, semantics.N)
        solver.add(semantics.task_rel(w, z3.IntVal(2), v))

        num_states = 2 ** semantics.N
        for u in range(num_states):
            u_bv = z3.BitVecVal(u, semantics.N)
            solver.add(
                z3.Not(
                    z3.And(
                        semantics.task_rel(w, z3.IntVal(1), u_bv),
                        semantics.task_rel(u_bv, z3.IntVal(1), v)
                    )
                )
            )

        assert solver.check() == z3.unsat, (
            "task_rel(w, 2, v) together with 'no intermediate state exists "
            "at d1=1, d2=1' should be unsatisfiable given Interpolation"
        )


class TestConstraintInteractions:
    """Tests verifying that the new frame constraints are mutually consistent
    and consistent with the existing lawful constraint.

    If any combination yields unsat with no added problem-specific assertions,
    that indicates an inconsistency in the frame axioms themselves.
    """

    def test_lawful_plus_nullity(self, semantics):
        """The lawful and nullity_identity constraints should be jointly satisfiable.

        Verifies that adding nullity_identity to the frame does not make the
        frame itself inconsistent with the lawful evolution constraint.
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        # No additional assertions -- just check the frame constraints themselves
        # are satisfiable with both lawful and nullity_identity active
        assert solver.check() == z3.sat, (
            "Frame constraints including lawful and nullity_identity should be satisfiable"
        )

    def test_all_constraints_consistent(self, semantics):
        """All five frame axioms plus lawful should be jointly satisfiable.

        Verifies the complete set of frame constraints (lawful + nullity_identity
        + converse + forward_comp + seriality + interpolation) does not create
        an inconsistency.

        This is a smoke test for the entire frame axiom system.
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        # The frame_constraints list includes lawful, nullity_identity,
        # converse, forward_comp, seriality, and interpolation -- simply
        # check they are satisfiable
        assert solver.check() == z3.sat, (
            "All frame constraints (lawful + nullity_identity + converse + "
            "forward_comp + seriality + interpolation) should be jointly "
            "satisfiable"
        )


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
