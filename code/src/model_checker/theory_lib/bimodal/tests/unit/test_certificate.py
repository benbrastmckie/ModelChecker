"""Unit tests for `LabelledLasso`/`WitnessFamily` and the certificate wire-format writer.

Mirrors `FormalSystem.Metalogic.Decidability.WitnessFamily.Basic`'s `LabelledLasso`/
`WitnessFamily` (`~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/WitnessFamily/
Basic.lean`) and the decoding scheme of `Periodic.unrollOf`
(`~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/BiLasso/Periodic.lean`): strictly
negative positions read `back` cyclically, `[0, len(mid))` reads `mid` directly, and positions at
or past `len(mid)` read `fwd` cyclically.

The wire format is documented in `~/Projects/BimodalLogic/BimodalTools/README.md`'s "Certificate
re-verification protocol" and restated in `tests/fixtures/certificates/README.md`; this module's
`test_matches_existing_fixture_shape` cross-checks the writer against that corpus directly.
"""

from __future__ import annotations

import json

import pytest

from model_checker.theory_lib.bimodal.semantic.certificate import (
    LabelledLasso,
    WitnessFamily,
)
from model_checker.theory_lib.bimodal.semantic.formula import Atom, Box, from_json, to_json

P = Atom("p")
Q = Atom("q")
BOX_P = Box(P)


class TestLabelledLassoConstruction:
    def test_back_must_be_non_empty(self):
        with pytest.raises(ValueError, match="back"):
            LabelledLasso(back=(), mid=(), fwd=(frozenset({P}),))

    def test_fwd_must_be_non_empty(self):
        with pytest.raises(ValueError, match="fwd"):
            LabelledLasso(back=(frozenset({P}),), mid=(), fwd=())

    def test_mid_may_be_empty(self):
        lasso = LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset(),))
        assert lasso.nm == 0


class TestLabelledLassoDecoding:
    """back=[{p}], mid=[{}, {q}], fwd=[{p,q}, {}] -- nb=1, nm=2, nf=2."""

    def lasso(self) -> LabelledLasso:
        return LabelledLasso(
            back=(frozenset({P}),),
            mid=(frozenset(), frozenset({Q})),
            fwd=(frozenset({P, Q}), frozenset()),
        )

    def test_mid_positions_read_directly(self):
        lasso = self.lasso()
        assert lasso.label(0) == frozenset()
        assert lasso.label(1) == frozenset({Q})

    def test_negative_positions_read_back_cyclically(self):
        lasso = self.lasso()
        for t in (-1, -2, -3, -10):
            assert lasso.label(t) == frozenset({P})

    def test_far_forward_positions_read_fwd_cyclically(self):
        lasso = self.lasso()
        # fwd starts at index nm=2: t=2 -> fwd[0], t=3 -> fwd[1], t=4 -> fwd[0], ...
        assert lasso.label(2) == frozenset({P, Q})
        assert lasso.label(3) == frozenset()
        assert lasso.label(4) == frozenset({P, Q})
        assert lasso.label(101) == lasso.label(3)  # (101 - 2) % 2 == 1 == (3 - 2) % 2

    def test_decoding_over_two_periods_each_side(self):
        lasso = self.lasso()
        # Two back periods (nb=1): t=-1, -2 both read back[0].
        assert lasso.label(-1) == lasso.label(-2) == frozenset({P})
        # Two fwd periods (nf=2): t in {2,4} read fwd[0]; t in {3,5} read fwd[1].
        assert lasso.label(2) == lasso.label(4)
        assert lasso.label(3) == lasso.label(5)


class TestLabelledLassoAllLabels:
    def test_all_labels_unions_every_segment(self):
        lasso = LabelledLasso(
            back=(frozenset({P}),),
            mid=(frozenset({Q}),),
            fwd=(frozenset({BOX_P}),),
        )
        assert lasso.all_labels() == frozenset({P, Q, BOX_P})


class TestWitnessFamilyConstruction:
    def test_lassos_must_be_non_empty(self):
        with pytest.raises(ValueError, match="lassos"):
            WitnessFamily(bx={}, lassos=())

    def test_main_is_the_first_lasso(self):
        main = LabelledLasso((frozenset(),), (), (frozenset(),))
        other = LabelledLasso((frozenset({P}),), (), (frozenset({P}),))
        family = WitnessFamily(bx={}, lassos=(main, other))
        assert family.main is main

    def test_bx_of_defaults_to_false_for_unlisted_formulas(self):
        family = WitnessFamily(bx={BOX_P: True}, lassos=(LabelledLasso((frozenset(),), (), (frozenset(),)),))
        assert family.bx_of(BOX_P) is True
        assert family.bx_of(Box(Q)) is False


class TestLabelsConfinedToClosure:
    """Mirrors `LabelledLasso.label_sub`: every label must be a subset of the certificate's
    closure. This is a caller-side obligation (the closure depends on premises/conclusions/bx,
    which `LabelledLasso` does not itself hold), checked here via `all_labels()`."""

    def test_all_labels_are_within_the_closure_of_the_target(self):
        from model_checker.theory_lib.bimodal.semantic.formula import closure_of

        lasso = LabelledLasso(
            back=(frozenset({BOX_P}),),
            mid=(),
            fwd=(frozenset({BOX_P, P}),),
        )
        family = WitnessFamily(bx={P: True}, lassos=(lasso,))
        premises = [BOX_P]
        conclusions = [Q]
        context_closure = closure_of(premises + conclusions + list(family.bx.keys()))
        full_closure = context_closure | family.main.all_labels()
        assert family.main.all_labels() <= full_closure

    def test_a_label_outside_the_closure_is_detectable(self):
        from model_checker.theory_lib.bimodal.semantic.formula import closure_of

        # BOX_P never appears in premises/conclusions/bx, only in the label -- so it is only
        # "in the closure" once the labels themselves are folded in, exactly as
        # test_certificate_fixtures.py's Certificate.closure does.
        lasso = LabelledLasso(back=(frozenset({BOX_P}),), mid=(), fwd=(frozenset(),))
        premises = [Q]
        conclusions = []
        narrow_closure = closure_of(premises + conclusions)
        assert not (lasso.all_labels() <= narrow_closure)


class TestWitnessFamilyToJson:
    def build_family(self) -> WitnessFamily:
        lasso = LabelledLasso(
            back=(frozenset({P, BOX_P}),),
            mid=(),
            fwd=(frozenset({P, BOX_P}),),
        )
        return WitnessFamily(bx={P: True}, lassos=(lasso,))

    def test_shape_has_required_top_level_keys(self):
        family = self.build_family()
        wire = family.to_json(premises=[BOX_P], conclusions=[Q], target_time=0)
        assert set(wire.keys()) == {"target", "bx", "lassos"}
        assert set(wire["target"].keys()) == {"premises", "conclusions", "time"}

    def test_target_time_is_always_explicit_even_when_zero(self):
        family = self.build_family()
        wire = family.to_json(premises=[], conclusions=[], target_time=0)
        assert wire["target"]["time"] == 0
        assert "time" in wire["target"]

    def test_bx_is_sparse_pairs_of_formula_and_bool(self):
        family = self.build_family()
        wire = family.to_json(premises=[], conclusions=[], target_time=0)
        assert wire["bx"] == [[to_json(P), True]]

    def test_lassos_serialize_back_mid_fwd(self):
        family = self.build_family()
        wire = family.to_json(premises=[], conclusions=[], target_time=0)
        assert len(wire["lassos"]) == 1
        lasso_wire = wire["lassos"][0]
        assert set(lasso_wire.keys()) == {"back", "mid", "fwd"}
        assert lasso_wire["mid"] == []
        assert len(lasso_wire["back"]) == 1
        assert len(lasso_wire["fwd"]) == 1
        decoded_back_label = {from_json(f) for f in lasso_wire["back"][0]}
        assert decoded_back_label == {P, BOX_P}

    def test_json_round_trips_through_stdlib_json(self):
        family = self.build_family()
        wire = family.to_json(premises=[BOX_P], conclusions=[Q], target_time=0)
        text = json.dumps(wire)
        reparsed = json.loads(text)
        assert reparsed == wire

    def test_matches_existing_fixture_shape(self):
        """Cross-check against the pre-existing fixture corpus: our writer's output, once
        decoded back through `from_json`, denotes the same certificate as the fixture."""
        fixtures_dir = (
            __import__("pathlib").Path(__file__).parent.parent / "fixtures" / "certificates"
        )
        with open(fixtures_dir / "01_positive_box.json") as f:
            raw = json.load(f)

        premises = [from_json(f) for f in raw["target"]["premises"]]
        conclusions = [from_json(f) for f in raw["target"]["conclusions"]]
        target_time = raw["target"]["time"]
        bx = {from_json(f): b for f, b in raw["bx"]}
        lassos = tuple(
            LabelledLasso(
                back=tuple(frozenset(from_json(f) for f in label) for label in lasso_raw["back"]),
                mid=tuple(frozenset(from_json(f) for f in label) for label in lasso_raw.get("mid", [])),
                fwd=tuple(frozenset(from_json(f) for f in label) for label in lasso_raw["fwd"]),
            )
            for lasso_raw in raw["lassos"]
        )
        family = WitnessFamily(bx=bx, lassos=lassos)
        wire = family.to_json(premises=premises, conclusions=conclusions, target_time=target_time)

        # Re-decode our own output and confirm it denotes the identical family/target.
        assert wire["target"]["time"] == raw["target"]["time"]
        assert {from_json(f) for f in [p for p in wire["target"]["premises"]]} == set(premises)
        assert {from_json(f) for f in [c for c in wire["target"]["conclusions"]]} == set(conclusions)
        rebuilt_bx = {from_json(f): b for f, b in wire["bx"]}
        assert rebuilt_bx == bx


# ---------------------------------------------------------------------------
# Phase 4: pure-Python re-checker of the four conditions
# ---------------------------------------------------------------------------
#
# `recheck` mirrors the exact Lean predicates in
# `~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/WitnessFamily/Predicates.lean`
# (`LocalCoherentLab`, `FulfillingLab`, `BoxFaithful`, `Target`) and the proved window collapses
# in `Decide.lean` (`coherent_iff_window:335`, `fulfil_iff_window:743`, `mem_all_iff_window:809,
# 883`) -- restated in this repo's own `tests/fixtures/certificates/README.md` and
# `docs/ADEQUACY.md`. The positive fixture below is a direct port of
# `Metalogic/Decidability/WitnessFamily/Examples.lean`'s `posFamily` (T3, report 02 section 3),
# and the negative fixtures reuse the existing checker-independent fixture corpus at
# `tests/fixtures/certificates/`.

import pathlib

from model_checker.theory_lib.bimodal.semantic.certificate import recheck
from model_checker.theory_lib.bimodal.semantic.formula import Bot, Imp, Snce, Untl

_FIXTURES_DIR = pathlib.Path(__file__).parent.parent / "fixtures" / "certificates"

TOP = Imp(Bot(), Bot())


def _some_future(phi):
    return Untl(guard=TOP, event=phi)


def _some_past(phi):
    return Snce(guard=TOP, event=phi)


def _neg(phi):
    return Imp(phi, Bot())


def _and(phi, psi):
    return Imp(Imp(phi, _neg(psi)), Bot())


def _or(phi, psi):
    return Imp(_neg(phi), psi)


def _load_fixture(name: str):
    """Load a wire-format fixture into (family, premises, conclusions, target_time)."""
    with open(_FIXTURES_DIR / name) as f:
        raw = json.load(f)
    premises = [from_json(f) for f in raw["target"].get("premises", [])]
    conclusions = [from_json(f) for f in raw["target"].get("conclusions", [])]
    target_time = raw["target"]["time"]
    bx = {from_json(f): b for f, b in raw.get("bx", [])}
    lassos = tuple(
        LabelledLasso(
            back=tuple(frozenset(from_json(f) for f in label) for label in lasso_raw["back"]),
            mid=tuple(frozenset(from_json(f) for f in label) for label in lasso_raw.get("mid", [])),
            fwd=tuple(frozenset(from_json(f) for f in label) for label in lasso_raw["fwd"]),
        )
        for lasso_raw in raw["lassos"]
    )
    family = WitnessFamily(bx=bx, lassos=lassos)
    return family, premises, conclusions, target_time


class TestRecheckPositiveT3Fixture:
    """A direct port of `Examples.lean`'s `posFamily`: `p` occurs exactly once along the single
    history, certifying `□(p ∨ Fp ∨ Pp) ∧ □(p → ¬Pp)` satisfiable (report 02 section 3, T3)."""

    def build(self):
        p = Atom("p")
        fp = _some_future(p)
        pp = _some_past(p)
        occurs = _or(p, _or(fp, pp))
        once = Imp(p, _neg(pp))
        phi_pos = _and(Box(occurs), Box(once))

        lab_back = frozenset({TOP, _neg(p), fp, _or(fp, pp), _neg(pp), occurs, Box(occurs), once, Box(once), phi_pos})
        lab_mid = frozenset({p, TOP, _neg(fp), _neg(pp), occurs, Box(occurs), once, Box(once), phi_pos})
        lab_fwd = frozenset({TOP, _neg(p), pp, _neg(fp), _or(fp, pp), occurs, Box(occurs), once, Box(once), phi_pos})

        lasso = LabelledLasso(back=(lab_back,), mid=(lab_mid,), fwd=(lab_fwd,))
        family = WitnessFamily(bx={occurs: True, once: True}, lassos=(lasso,))
        return family, [phi_pos], [], 0

    def test_countermodel(self):
        family, premises, conclusions, target_time = self.build()
        verdict = recheck(family, premises, conclusions, target_time)
        assert verdict == {"status": "countermodel", "time": 0}


class TestRecheckInfinitePostponementFixture:
    """`02_infinite_postponement.json`: locally coherent but the `until` obligation is deferred
    forever -- fulfilment must reject it (a checker that tested only local coherence would not)."""

    def test_rejected_fulfilling(self):
        family, premises, conclusions, target_time = _load_fixture("02_infinite_postponement.json")
        verdict = recheck(family, premises, conclusions, target_time)
        assert verdict["status"] == "rejected"
        assert verdict["failed"][0]["condition"] == "fulfilling"
        assert verdict["failed"][0]["lasso"] == 0
        assert verdict["failed"][0]["position"] == -2


class TestRecheckBoxUnfaithfulFixture:
    def test_rejected_box_faithful(self):
        family, premises, conclusions, target_time = _load_fixture("03_box_unfaithful.json")
        verdict = recheck(family, premises, conclusions, target_time)
        assert verdict["status"] == "rejected"
        assert verdict["failed"][0]["condition"] == "box_faithful"


class TestRecheckWindowDiscriminatorFixture:
    """`04_window_discriminator_coherence.json`: the violation sits in the outer band
    `[-2*nb, -nb)`, reachable only by the proved wide window, not the one-period window."""

    def test_rejected_local_coherent_at_outer_band_position(self):
        family, premises, conclusions, target_time = _load_fixture(
            "04_window_discriminator_coherence.json"
        )
        verdict = recheck(family, premises, conclusions, target_time)
        assert verdict["status"] == "rejected"
        assert verdict["failed"][0]["condition"] == "local_coherent"
        assert verdict["failed"][0]["position"] == -2

    def test_the_wide_window_is_load_bearing_not_cosmetic(self):
        """Directly exercises the window-bound helpers: the wide window strictly contains the
        one-period window on both sides, and the violating position (-2) is only in the wide
        one -- so a re-checker using the narrow window would (wrongly) accept this fixture."""
        from model_checker.theory_lib.bimodal.semantic.certificate import (
            _box_window,
            _coherence_window,
        )

        family, _, _, _ = _load_fixture("04_window_discriminator_coherence.json")
        lasso = family.main
        wide = _coherence_window(lasso)
        narrow = _box_window(lasso)  # the one-period window, reused here as "the narrow one"
        assert wide.start < narrow.start and wide.stop > narrow.stop
        assert -2 in wide
        assert -2 not in narrow


class TestRecheckTargetFailure:
    def test_rejected_target_when_premise_absent(self):
        p, q = Atom("p"), Atom("q")
        # q is in the closure (it's a conclusion), so this is a genuine target failure, not a
        # structural one: the label carries q but never p, so the premise p is absent at t=0.
        lasso = LabelledLasso(back=(frozenset({q}),), mid=(), fwd=(frozenset({q}),))
        family = WitnessFamily(bx={}, lassos=(lasso,))
        verdict = recheck(family, premises=[p], conclusions=[q], target_time=0)
        assert verdict["status"] == "rejected"
        assert verdict["failed"][0]["condition"] == "target"

    def test_rejected_target_when_conclusion_present(self):
        p = Atom("p")
        lasso = LabelledLasso(back=(frozenset({p}),), mid=(), fwd=(frozenset({p}),))
        family = WitnessFamily(bx={}, lassos=(lasso,))
        verdict = recheck(family, premises=[], conclusions=[p], target_time=0)
        assert verdict["status"] == "rejected"
        assert verdict["failed"][0]["condition"] == "target"


class TestRecheckStructuralFailure:
    def test_rejected_structural_when_a_label_formula_is_outside_the_closure(self):
        p, q, r = Atom("p"), Atom("q"), Atom("r")
        # r never appears in premises/conclusions, so it is outside closure_of([Box(p), q]).
        lasso = LabelledLasso(back=(frozenset({r}),), mid=(), fwd=(frozenset({r}),))
        family = WitnessFamily(bx={}, lassos=(lasso,))
        verdict = recheck(family, premises=[Box(p)], conclusions=[q], target_time=0)
        assert verdict["status"] == "rejected"
        assert verdict["failed"][0]["condition"] == "structural"

    def test_bx_key_outside_the_closure_is_not_a_structural_violation(self):
        """`WitnessFamily.bx : Formula -> Bool` is Lean-side a total, unrestricted function;
        `LocalCoherentLab`'s box clause only *applies* when `Box(chi)` is itself in the closure
        (`Formula.box χ ∈ closureOf (Γ ++ Del) -> ...`), so a `bx` entry for a `chi` whose
        `Box(chi)` never occurs in the closure is simply irrelevant, not a precondition failure
        -- unlike a label, which `LabelledLasso.label_sub` requires to be a closure subset by
        construction. This is intentionally *not* the mirror of the label-outside-closure test
        above."""
        p, q, r = Atom("p"), Atom("q"), Atom("r")
        lasso = LabelledLasso(back=(frozenset(),), mid=(), fwd=(frozenset(),))
        family = WitnessFamily(bx={r: True}, lassos=(lasso,))
        verdict = recheck(family, premises=[Box(p)], conclusions=[q], target_time=0)
        assert verdict["status"] != "error"
        # (whatever the verdict, it must not be a structural rejection over the stray bx key)
        if verdict["status"] == "rejected":
            assert verdict["failed"][0]["condition"] != "structural"


class TestRecheckLocalCoherentFailure:
    def test_rejected_local_coherent_when_bot_is_labelled(self):
        # Bot() is trivially in closure_of([Bot()]), so this exercises the local-coherence
        # "bot never labelled" clause rather than the structural label-outside-closure check.
        lasso = LabelledLasso(back=(frozenset({Bot()}),), mid=(), fwd=(frozenset({Bot()}),))
        family = WitnessFamily(bx={}, lassos=(lasso,))
        verdict = recheck(family, premises=[Bot()], conclusions=[], target_time=0)
        assert verdict["status"] == "rejected"
        assert verdict["failed"][0]["condition"] == "local_coherent"

    def test_rejected_local_coherent_when_box_clause_disagrees_with_guess(self):
        p = Atom("p")
        boxed = Box(p)
        # bx says Box(p) is false, but the label carries Box(p) anyway: violates the
        # `box χ ∈ label ↔ bx χ` biconditional.
        lasso = LabelledLasso(back=(frozenset({boxed}),), mid=(), fwd=(frozenset({boxed}),))
        family = WitnessFamily(bx={p: False}, lassos=(lasso,))
        verdict = recheck(family, premises=[boxed], conclusions=[], target_time=0)
        assert verdict["status"] == "rejected"
        assert verdict["failed"][0]["condition"] == "local_coherent"
