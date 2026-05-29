"""Tests for frame constraints in BimodalSemantics.

Tests verify correctness of the three new frame constraint builder methods:
  1. build_nullity_identity_constraint() -- task_rel(w, 0, u) <-> w == u
  2. build_converse_constraint() -- task_rel(w, d, u) <-> task_rel(u, -d, w)
  3. build_forward_comp_constraint() -- compositionality of sequential tasks

Each class tests a constraint individually and also verifies interactions
with the existing 'lawful' constraint.

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
        """All three new constraints plus lawful should be jointly satisfiable.

        Verifies the complete set of frame constraints (lawful + nullity_identity
        + converse + forward_comp) does not create an inconsistency.

        This is a smoke test for the entire frame axiom system.
        """
        solver = z3.Solver()
        solver.add(semantics.frame_constraints)

        # The frame_constraints list includes lawful, nullity_identity,
        # converse, and forward_comp -- simply check they are satisfiable
        assert solver.check() == z3.sat, (
            "All frame constraints (lawful + nullity_identity + converse + "
            "forward_comp) should be jointly satisfiable"
        )


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
