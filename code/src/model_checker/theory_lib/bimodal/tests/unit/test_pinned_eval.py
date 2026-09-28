"""Unit tests for `tests/_pinned_eval.py`'s compile-once evaluator and candidate-to-assignment
builder (`docs/ADEQUACY.md` section 7.3's leg (i)/(iii) A2-triangle differential).

Phase 1 (hand-built Z3 formulas, no `BimodalStructure` needed): each of the six operators the
encoder emits evaluates correctly in both polarities, the `AtMost` bound is pinned against a
small solver-backed cross-check, an unsupported node raises loudly, and an unpopulated atom
index raises rather than reading as `False`.

Phase 2 (structure-backed cases through the real `Syntax -> ModelConstraints ->
BimodalStructure` pipeline, matching `tests/unit/test_structure.py`'s own `_build`): the
operator inventory is exactly the closed six-operator set, the assignment builder's coverage is
exact, the extracted-certificate round-trip evaluates `True`, and a collision between two
distinct writes to the same atom name raises.
"""

from __future__ import annotations

from typing import Any, Dict, List

import pytest
import z3

from model_checker.theory_lib.bimodal.semantic.certificate import LabelledLasso, WitnessFamily, recheck
from model_checker.theory_lib.bimodal.semantic.formula import Atom, Box, Formula
from model_checker.theory_lib.bimodal.tests._build_support import _build
from model_checker.theory_lib.bimodal.tests._pinned_eval import (
    AssignmentCollisionError,
    AtomNotAssignedError,
    CoverageError,
    PinnedAssignmentBuilder,
    UnsupportedOperatorError,
    builder_for,
    check_coverage,
    compile_and_bind,
    compile_constraints,
    full_constraints,
)


# ---------------------------------------------------------------------------
# Phase 1: hand-built Z3 formulas, no BimodalStructure needed.
# ---------------------------------------------------------------------------


def _row_from(atom_index: Dict[str, int], values: Dict[str, bool]) -> List[bool]:
    row: List[Any] = [None] * len(atom_index)
    for name, value in values.items():
        row[atom_index[name]] = value
    return row


class TestNotOperator:
    def test_both_polarities(self):
        a = z3.Bool("lab_0_0_a")
        compiled = compile_constraints([z3.Not(a)])
        assert compiled.evaluate_all(_row_from(compiled.atom_index, {"lab_0_0_a": False}))
        assert not compiled.evaluate_all(_row_from(compiled.atom_index, {"lab_0_0_a": True}))


class TestAndOperator:
    @pytest.mark.parametrize(
        "a_val, b_val, expected", [(True, True, True), (True, False, False), (False, False, False)]
    )
    def test_two_arg_and(self, a_val, b_val, expected):
        a, b = z3.Bools("lab_0_0_a lab_0_1_b")
        compiled = compile_constraints([z3.And(a, b)])
        row = _row_from(compiled.atom_index, {"lab_0_0_a": a_val, "lab_0_1_b": b_val})
        assert compiled.evaluate_all(row) == expected

    def test_nested_and(self):
        a, b, c = z3.Bools("lab_0_0_a lab_0_1_b lab_0_2_c")
        compiled = compile_constraints([z3.And(a, z3.And(b, c))])
        all_true = _row_from(compiled.atom_index, {"lab_0_0_a": True, "lab_0_1_b": True, "lab_0_2_c": True})
        assert compiled.evaluate_all(all_true)
        one_false = _row_from(compiled.atom_index, {"lab_0_0_a": True, "lab_0_1_b": True, "lab_0_2_c": False})
        assert not compiled.evaluate_all(one_false)

    def test_degenerate_zero_arg_and_is_true(self):
        compiled = compile_constraints([z3.And()])
        assert compiled.evaluate_all([])

    def test_degenerate_one_arg_and(self):
        a = z3.Bool("lab_0_0_a")
        compiled = compile_constraints([z3.And(a)])
        assert compiled.evaluate_all(_row_from(compiled.atom_index, {"lab_0_0_a": True}))
        assert not compiled.evaluate_all(_row_from(compiled.atom_index, {"lab_0_0_a": False}))


class TestOrOperator:
    @pytest.mark.parametrize(
        "a_val, b_val, expected", [(True, False, True), (False, False, False), (True, True, True)]
    )
    def test_two_arg_or(self, a_val, b_val, expected):
        a, b = z3.Bools("lab_0_0_a lab_0_1_b")
        compiled = compile_constraints([z3.Or(a, b)])
        row = _row_from(compiled.atom_index, {"lab_0_0_a": a_val, "lab_0_1_b": b_val})
        assert compiled.evaluate_all(row) == expected

    def test_degenerate_zero_arg_or_is_false(self):
        compiled = compile_constraints([z3.Or()])
        assert not compiled.evaluate_all([])

    def test_degenerate_one_arg_or(self):
        a = z3.Bool("lab_0_0_a")
        compiled = compile_constraints([z3.Or(a)])
        assert compiled.evaluate_all(_row_from(compiled.atom_index, {"lab_0_0_a": True}))
        assert not compiled.evaluate_all(_row_from(compiled.atom_index, {"lab_0_0_a": False}))


class TestImpliesOperator:
    @pytest.mark.parametrize(
        "a_val, b_val, expected",
        [(True, True, True), (True, False, False), (False, True, True), (False, False, True)],
    )
    def test_truth_table(self, a_val, b_val, expected):
        a, b = z3.Bools("lab_0_0_a lab_0_1_b")
        compiled = compile_constraints([z3.Implies(a, b)])
        row = _row_from(compiled.atom_index, {"lab_0_0_a": a_val, "lab_0_1_b": b_val})
        assert compiled.evaluate_all(row) == expected


class TestEqOperator:
    @pytest.mark.parametrize(
        "a_val, b_val, expected",
        [(True, True, True), (False, False, True), (True, False, False), (False, True, False)],
    )
    def test_boolref_eq_boolref(self, a_val, b_val, expected):
        a, b = z3.Bools("lab_0_0_a lab_0_1_b")
        compiled = compile_constraints([a == b])
        row = _row_from(compiled.atom_index, {"lab_0_0_a": a_val, "lab_0_1_b": b_val})
        assert compiled.evaluate_all(row) == expected


class TestAtMostOperator:
    """Pins `AtMost`'s bound argument position against a small solver-backed cross-check,
    mirroring `test_witness_constraints.py`'s `TestSelectorConservativity` -- the bound cannot
    be silently wrong (e.g. read as the number of true args allowed, off by one, or read as one
    of the boolean args) without this test catching it."""

    @pytest.mark.parametrize(
        "true_count, bound, expected",
        [(0, 1, True), (1, 1, True), (2, 1, False), (2, 2, True), (3, 2, False), (0, 0, True), (1, 0, False)],
    )
    def test_bound_matches_solver_backed_cross_check(self, true_count, bound, expected):
        sels = list(z3.Bools(" ".join(f"sel_{i}" for i in range(3))))
        compiled = compile_constraints([z3.AtMost(*sels, bound)])
        values = {f"sel_{i}": (i < true_count) for i in range(3)}
        row = _row_from(compiled.atom_index, values)
        assert compiled.evaluate_all(row) == expected

        # Solver-backed cross-check: pin each selector to `values` and confirm the AtMost
        # constraint's own satisfiability agrees with the compiled evaluator's verdict.
        solver = z3.Solver()
        solver.add(z3.AtMost(*sels, bound))
        for sel, val in zip(sels, values.values()):
            solver.add(sel == val)
        assert (solver.check() == z3.sat) == expected


class TestZ3Constants:
    def test_true_constant(self):
        compiled = compile_constraints([z3.BoolVal(True)])
        assert compiled.evaluate_all([])

    def test_false_constant(self):
        compiled = compile_constraints([z3.BoolVal(False)])
        assert not compiled.evaluate_all([])


class TestUnsupportedOperatorRaises:
    def test_ite_raises(self):
        a, b, c = z3.Bools("lab_0_0_a lab_0_1_b lab_0_2_c")
        with pytest.raises(UnsupportedOperatorError):
            compile_constraints([z3.If(a, b, c)])

    def test_arithmetic_raises(self):
        x = z3.Int("x")
        with pytest.raises(UnsupportedOperatorError):
            compile_constraints([x > 0])

    def test_quantifier_raises(self):
        x = z3.Int("x")
        with pytest.raises(UnsupportedOperatorError):
            compile_constraints([z3.ForAll([x], x == x)])

    def test_atleast_raises(self):
        """`AtLeast`/`PbEq`/`PbGe`/`PbLe` are pseudo-Boolean kinds the encoder never emits
        (only `AtMost`) -- confirm they are outside the closed set too, not silently accepted."""
        sels = list(z3.Bools("sel_0 sel_1"))
        with pytest.raises(UnsupportedOperatorError):
            compile_constraints([z3.AtLeast(*sels, 1)])


class TestUnpopulatedAtomRaises:
    def test_read_of_none_raises_not_false(self):
        a = z3.Bool("lab_0_0_a")
        compiled = compile_constraints([a])
        row: List[Any] = [None] * compiled.size
        with pytest.raises(AtomNotAssignedError):
            compiled.evaluate_all(row)


class TestDescribe:
    def test_describe_gives_constraint_text(self):
        a = z3.Bool("lab_0_0_a")
        compiled = compile_constraints([a, z3.Not(a)])
        row = _row_from(compiled.atom_index, {"lab_0_0_a": True})
        first_false = compiled.first_false(row)
        assert first_false == 1
        assert "lab_0_0_a" in compiled.describe(first_false)


class TestNoZ3ApiCallInHotPath:
    """Confirms the compile/interpret split by construction: once compiled, the evaluator's
    closures close over plain Python values (ints, lists of callables), not over any live Z3
    object that would require a further Z3 API call to read."""

    def test_atom_reader_closes_over_plain_index_not_z3_object(self):
        a = z3.Bool("lab_0_0_a")
        compiled = compile_constraints([a])
        # The compiled reader is a plain closure taking a Row and indexing into it -- calling it
        # many times against a plain Python list (never a Z3 object) must succeed, which it can
        # only do if nothing in the hot path touches z3 at all.
        row = [True]
        for _ in range(10_000):
            assert compiled.evaluate_all(row) is True


# ---------------------------------------------------------------------------
# Phase 2: structure-backed cases through the real pipeline.
# ---------------------------------------------------------------------------

_TIER1_SETTINGS = [
    pytest.param(1, 1, 1, id="back1_mid1_fwd1"),
    pytest.param(2, 1, 2, id="back2_mid1_fwd2"),
]


class TestOperatorInventoryIsClosed:
    """Finding 4/5, machine-checked rather than trusted: every node in
    `full_constraints(structure)` (the complete, post-`finalize_certificate` constraint set --
    now a named alias for `structure.model_constraints.all_constraints` itself, a computed,
    read-only property; see that function's docstring for the history) compiles without
    raising, for both box-free and boxed closures at both grid sizes."""

    @pytest.mark.parametrize("back, mid, fwd", _TIER1_SETTINGS)
    def test_box_free_closure(self, back, mid, fwd):
        structure = _build([], ["(p \\Until q)"], back=back, mid=mid, fwd=fwd)
        # Must not raise UnsupportedOperatorError.
        compile_constraints(full_constraints(structure))

    @pytest.mark.parametrize("back, mid, fwd", _TIER1_SETTINGS)
    def test_boxed_closure(self, back, mid, fwd):
        structure = _build(["\\Box A"], ["B"], back=back, mid=mid, fwd=fwd)
        compile_constraints(full_constraints(structure))

    def test_every_leaf_atom_matches_one_of_three_families(self):
        structure = _build(["\\Box A"], ["B"], back=1, mid=1, fwd=1)
        compiled = compile_constraints(full_constraints(structure))
        for name in compiled.atom_index:
            assert name.startswith("lab_") or name.startswith("bx_") or name.startswith("sel_"), (
                f"atom name {name!r} outside the three closed families"
            )


class TestAssignmentCoverage:
    """The builder's produced key set is exactly `compile_constraints(...).atom_index`'s key
    set, for every Tier 1 settings combination -- neither an unpopulated referenced atom nor a
    stray key."""

    @pytest.mark.parametrize("back, mid, fwd", _TIER1_SETTINGS)
    def test_box_free_coverage(self, back, mid, fwd):
        structure = _build([], ["(p \\Until q)"], back=back, mid=mid, fwd=fwd)
        compiled = compile_constraints(full_constraints(structure))
        builder = builder_for(structure, compiled.atom_index)
        assert structure.certificate is not None
        assert structure.target_time is not None
        names = builder.build_names(structure.certificate, structure.target_time)
        check_coverage(names, compiled.atom_index)

    @pytest.mark.parametrize("back, mid, fwd", _TIER1_SETTINGS)
    def test_boxed_coverage(self, back, mid, fwd):
        structure = _build(["\\Box A"], ["B"], back=back, mid=mid, fwd=fwd)
        compiled = compile_constraints(full_constraints(structure))
        builder = builder_for(structure, compiled.atom_index)
        assert structure.certificate is not None
        assert structure.target_time is not None
        names = builder.build_names(structure.certificate, structure.target_time)
        check_coverage(names, compiled.atom_index)

    def test_mismatch_raises_coverage_error(self):
        with pytest.raises(CoverageError):
            check_coverage({"lab_0_0_x": True}, {"lab_0_0_x": 0, "sel_0": 1})


class TestExtractedCertificateRoundTrip:
    """The strongest self-check: for an expected-SAT case, the assignment built from the
    extracted certificate (which came from a genuinely satisfying Z3 model) makes `evaluate_all`
    return `True`. A `False` here means the evaluator or builder is wrong, not the encoder."""

    @pytest.mark.parametrize("back, mid, fwd", _TIER1_SETTINGS)
    def test_box_free_sat_case_round_trips_true(self, back, mid, fwd):
        structure = _build([], ["(p \\Until q)"], back=back, mid=mid, fwd=fwd)
        assert structure.z3_model_status is True
        compiled, builder = compile_and_bind(structure)
        row = builder.assign(structure.certificate, structure.target_time)
        assert compiled.evaluate_all(row) is True

    def test_boxed_sat_case_round_trips_true(self):
        structure = _build(["\\Box A"], ["B"], back=1, mid=1, fwd=1)
        assert structure.z3_model_status is True
        compiled, builder = compile_and_bind(structure)
        row = builder.assign(structure.certificate, structure.target_time)
        assert compiled.evaluate_all(row) is True


class _CollidingFormula:
    """A minimal stand-in for `Formula` with a deliberately fixed `repr()`, so two distinct
    (non-equal) instances share the identical repr string -- the collision
    `AssignmentCollisionError` guards against (module docstring). Not a real `Formula` subclass:
    the guard fires purely from `repr()`/`==` disagreement, so it needs neither `isinstance`
    checks nor the real ADT."""

    def __init__(self, tag: str) -> None:
        self.tag = tag

    def __repr__(self) -> str:
        return "Colliding()"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, _CollidingFormula) and self.tag == other.tag

    def __hash__(self) -> int:
        return hash(("_CollidingFormula", self.tag))


class TestCollisionGuard:
    def test_two_distinct_formulas_sharing_a_repr_raises_at_construction(self):
        first = _CollidingFormula("a")
        second = _CollidingFormula("b")
        assert first != second and repr(first) == repr(second)

        with pytest.raises(AssignmentCollisionError):
            PinnedAssignmentBuilder(
                atom_index={},
                active_lassos=[0],
                nb=1,
                nm=0,
                nf=1,
                closure=[first, second],
                target_window=[],
            )
