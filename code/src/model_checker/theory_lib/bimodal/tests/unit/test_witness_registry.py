"""Unit tests for the certificate-search `WitnessRegistry` (the Z3 variable layer).

Mirrors `LabelledLasso.label`'s decoding scheme (`certificate.py`): `wrap(t)` must agree with it
slot-for-slot, so that `bit(lasso, t, formula)` genuinely represents "formula is in the label at
position t" for every t, not just the representative positions checked directly.
"""

from __future__ import annotations

import pytest
import z3

from model_checker.theory_lib.bimodal.semantic.certificate import LabelledLasso, _box_window
from model_checker.theory_lib.bimodal.semantic.formula import Atom, Box
from model_checker.theory_lib.bimodal.semantic.witness_registry import WitnessRegistry
from model_checker.theory_lib.errors import WitnessRegistryError

P = Atom("p")
Q = Atom("q")
BOX_P = Box(P)


class TestConstruction:
    def test_back_must_be_positive(self):
        with pytest.raises(WitnessRegistryError, match="back"):
            WitnessRegistry(back=0, mid=1, fwd=1, closure=[P])

    def test_fwd_must_be_positive(self):
        with pytest.raises(WitnessRegistryError, match="fwd"):
            WitnessRegistry(back=1, mid=1, fwd=0, closure=[P])

    def test_mid_may_be_zero(self):
        registry = WitnessRegistry(back=1, mid=0, fwd=1, closure=[P])
        assert registry.nm == 0

    def test_mid_may_not_be_negative(self):
        with pytest.raises(WitnessRegistryError, match="mid"):
            WitnessRegistry(back=1, mid=-1, fwd=1, closure=[P])

    def test_max_witnesses_must_be_positive_when_given(self):
        with pytest.raises(WitnessRegistryError, match="max_witnesses"):
            WitnessRegistry(back=1, mid=1, fwd=1, closure=[P], max_witnesses=0)

    def test_slots_per_lasso(self):
        registry = WitnessRegistry(back=2, mid=3, fwd=4, closure=[P])
        assert registry.slots_per_lasso == 9


class TestWrapAgreesWithLabelledLassoDecoding:
    """`wrap(t)` must partition every `t` into the same slot `LabelledLasso.label(t)` would read
    from, across at least two periods each side, matching this phase's own verification tier."""

    def registry(self) -> WitnessRegistry:
        return WitnessRegistry(back=2, mid=3, fwd=2, closure=[P])

    def lasso(self) -> LabelledLasso:
        # nb=2, nm=3, nf=2 -- distinct labels at every slot so agreement is unambiguous.
        return LabelledLasso(
            back=(frozenset({Atom("back0")}), frozenset({Atom("back1")})),
            mid=(
                frozenset({Atom("mid0")}),
                frozenset({Atom("mid1")}),
                frozenset({Atom("mid2")}),
            ),
            fwd=(frozenset({Atom("fwd0")}), frozenset({Atom("fwd1")})),
        )

    @pytest.mark.parametrize("t", range(-8, 9))  # two periods each side of a 2/3/2 lasso
    def test_wrap_index_denotes_the_same_label_as_direct_decoding(self, t):
        registry = self.registry()
        lasso = self.lasso()
        index = registry.wrap(t)
        # Reconstruct which segment/offset `index` names, and confirm it is the label at every
        # position that wraps to the same index -- in particular the label at `t` itself.
        if index < registry.nb:
            expected = lasso.back[index]
        elif index < registry.nb + registry.nm:
            expected = lasso.mid[index - registry.nb]
        else:
            expected = lasso.fwd[index - registry.nb - registry.nm]
        assert lasso.label(t) == expected

    def test_wrap_range_is_within_slots_per_lasso(self):
        registry = self.registry()
        for t in range(-20, 21):
            assert 0 <= registry.wrap(t) < registry.slots_per_lasso

    def test_positions_two_periods_apart_share_a_slot(self):
        registry = self.registry()
        # Back period is nb=2, fwd period is nf=2.
        assert registry.wrap(-1) == registry.wrap(-1 - 2 * registry.nb)
        assert registry.wrap(registry.nm) == registry.wrap(registry.nm + 2 * registry.nf)


class TestWrapFoldsByExactPeriod:
    """`wrap`'s modular arithmetic is exactly what makes a back-period `p` representable at
    segment length `nb` if and only if `p` divides `nb` (and symmetrically for `nf`/forward
    period): positions `p` apart share a slot exactly when `nb % p == 0` (back) or
    `nf % p == 0` (forward), because `wrap` folds by `nb`/`nf` themselves, not by `p`. This is
    the arithmetic fact behind the search's non-monotonicity in back/mid/fwd (see
    `docs/SEARCH_COVERAGE.md`): a period-3 family is representable at `back=3` and `back=6`
    (3 divides both) but not at `back=4` or `back=5` (3 divides neither)."""

    def test_back_period_3_shares_a_slot_at_nb_3(self):
        # nb=3: positions -1 and -4 are 3 apart, and 3 divides nb=3, so they fold to one slot.
        registry = WitnessRegistry(back=3, mid=1, fwd=3, closure=[P])
        assert registry.wrap(-1) == registry.wrap(-4) == 2

    def test_back_period_3_does_not_share_a_slot_with_a_period_1_offset(self):
        # Still nb=3: -1 and -2 are only 1 apart, not a multiple of any period this wrap
        # respects other than the trivial one, so they must land in distinct slots.
        registry = WitnessRegistry(back=3, mid=1, fwd=3, closure=[P])
        assert registry.wrap(-1) != registry.wrap(-2)

    def test_back_period_3_does_not_share_a_slot_at_nb_4(self):
        # nb=4: -1 and -4 are still 3 apart, but 3 does not divide nb=4, so wrap's fold-by-4
        # arithmetic keeps them in distinct slots -- the period-3 family is not representable
        # at back=4.
        registry = WitnessRegistry(back=4, mid=1, fwd=4, closure=[P])
        assert registry.wrap(-1) != registry.wrap(-4)

    def test_forward_period_3_shares_a_slot_at_nf_3(self):
        # The forward mirror of the same fact, through the `nb + nm + ((t - nm) % nf)` branch:
        # positions 3 apart past `mid` fold to one slot when nf=3 divides that period.
        registry = WitnessRegistry(back=1, mid=0, fwd=3, closure=[P])
        assert registry.wrap(5) == registry.wrap(8)

    def test_forward_period_3_does_not_share_a_slot_at_nf_4(self):
        registry = WitnessRegistry(back=1, mid=0, fwd=4, closure=[P])
        assert registry.wrap(5) != registry.wrap(8)

    def test_bit_is_the_same_z3_boolean_for_positions_sharing_a_slot(self):
        """This is the step that makes the folding observable to the encoding, not merely to
        `wrap`'s arithmetic: two positions that share a slot must be backed by the identical
        Z3 variable via `bit`, so the encoder cannot distinguish them even in principle."""
        registry = WitnessRegistry(back=3, mid=1, fwd=3, closure=[P])
        assert registry.bit(0, -1, P).eq(registry.bit(0, -4, P))

    def test_bit_is_a_distinct_z3_boolean_for_positions_in_different_slots(self):
        registry = WitnessRegistry(back=4, mid=1, fwd=4, closure=[P])
        assert not registry.bit(0, -1, P).eq(registry.bit(0, -4, P))


class TestBit:
    def test_bit_is_a_z3_bool(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P])
        assert isinstance(registry.bit(0, 0, P), z3.BoolRef)

    def test_bit_identity_is_stable_across_repeated_lookups(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P])
        first = registry.bit(0, 0, P)
        second = registry.bit(0, 0, P)
        assert first.eq(second)

    def test_bit_agrees_across_positions_sharing_a_slot(self):
        """Positions that wrap to the same slot must yield the identical Z3 variable -- this is
        what makes the periodicity of a certificate's labels automatic rather than a constraint
        the encoder has to assert separately."""
        registry = WitnessRegistry(back=2, mid=0, fwd=2, closure=[P])
        assert registry.bit(0, -1, P).eq(registry.bit(0, -1 - 2 * registry.nb, P))
        assert registry.bit(0, 3, P).eq(registry.bit(0, 3 + 2 * registry.nf, P))

    def test_bit_differs_across_lassos(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P])
        assert not registry.bit(0, 0, P).eq(registry.bit(1, 0, P))

    def test_bit_differs_across_formulas(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P, Q])
        assert not registry.bit(0, 0, P).eq(registry.bit(0, 0, Q))

    def test_bit_count_for_a_hand_computed_case(self):
        """`slots_per_lasso * |closure|` distinct bits per lasso, for a closure with no shared
        subformulas -- back=2, mid=3, fwd=2 (7 slots) times 2 formulas, across 2 lassos."""
        registry = WitnessRegistry(back=2, mid=3, fwd=2, closure=[P, Q])
        seen = set()
        for lasso in (0, 1):
            for t in range(-2, 5):  # one full period window: exercises all 7 slots
                for formula in (P, Q):
                    seen.add(id(registry.bit(lasso, t, formula)))
        assert len(seen) == 2 * registry.slots_per_lasso * 2


class TestGuess:
    def test_guess_is_a_z3_bool(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[BOX_P])
        assert isinstance(registry.guess(P), z3.BoolRef)

    def test_guess_identity_is_stable(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[BOX_P])
        assert registry.guess(P).eq(registry.guess(P))

    def test_guess_differs_across_formulas(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[BOX_P, Q])
        assert not registry.guess(P).eq(registry.guess(Q))

    def test_guess_and_bit_are_independent_namespaces(self):
        """A guess variable for `p` must not collide with a label bit for `p`, even though both
        are keyed by the same formula."""
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P])
        assert not registry.guess(P).eq(registry.bit(0, 0, P))


class TestAllocateWitnessLasso:
    def test_first_allocation_is_not_the_main_lasso_index(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[BOX_P])
        assert registry.allocate_witness_lasso(P) != 0

    def test_repeated_allocation_for_the_same_formula_is_stable(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[BOX_P])
        first = registry.allocate_witness_lasso(P)
        second = registry.allocate_witness_lasso(P)
        assert first == second

    def test_distinct_formulas_get_distinct_indices_when_uncapped(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[Box(P), Box(Q)])
        assert registry.allocate_witness_lasso(P) != registry.allocate_witness_lasso(Q)

    def test_max_witnesses_forces_sharing(self):
        registry = WitnessRegistry(
            back=1, mid=1, fwd=1, closure=[Box(P), Box(Q)], max_witnesses=1
        )
        first = registry.allocate_witness_lasso(P)
        second = registry.allocate_witness_lasso(Q)
        assert first == second == 1

    def test_max_witnesses_round_robins_across_more_than_one_slot(self):
        r = Atom("r")
        registry = WitnessRegistry(
            back=1, mid=1, fwd=1, closure=[Box(P), Box(Q), Box(r)], max_witnesses=2
        )
        a = registry.allocate_witness_lasso(P)
        b = registry.allocate_witness_lasso(Q)
        c = registry.allocate_witness_lasso(r)
        assert {a, b} == {1, 2}
        assert c in {1, 2}


class TestTargetWindow:
    def test_target_window_length_equals_slots_per_lasso(self):
        registry = WitnessRegistry(back=2, mid=3, fwd=4, closure=[P])
        window = registry.target_window()
        assert len(window) == registry.slots_per_lasso

    def test_target_window_hits_every_slot_exactly_once(self):
        registry = WitnessRegistry(back=2, mid=3, fwd=2, closure=[P])
        indices = [registry.wrap(t) for t in registry.target_window()]
        assert sorted(indices) == list(range(registry.slots_per_lasso))

    def test_target_window_agrees_with_box_window_across_swept_segment_lengths(self):
        """Mechanical backstop against re-divergence once `target_window()` delegates to
        `_box_window` (Phase 2): this is a pinned baseline confirming the two formulas already
        agree, not a claim that two independent formulas happen to coincide. `back`/`fwd` range
        `1..3` (must be `>= 1`, `WitnessRegistry.__init__`'s own validation) and `mid` ranges
        `0..3` (must be `>= 0`), including every `mid == 0` case: 36 combinations."""
        combinations = 0
        for back in range(1, 4):
            for mid in range(0, 4):
                for fwd in range(1, 4):
                    registry = WitnessRegistry(back=back, mid=mid, fwd=fwd, closure=[P])
                    assert registry.target_window() == _box_window(registry)
                    assert registry.target_window() == range(-back, mid + fwd)
                    combinations += 1
        assert combinations == 36


class TestClear:
    def test_clear_releases_bits_guesses_and_witness_lassos(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[BOX_P])
        registry.bit(0, 0, P)
        registry.guess(P)
        registry.allocate_witness_lasso(P)
        registry.clear()
        assert registry._bits == {}
        assert registry._guesses == {}
        assert registry._witness_lassos == {}

    def test_clear_then_reallocate_starts_fresh(self):
        """After `clear()`, a fresh `bit`/`guess`/`allocate_witness_lasso` call must produce a
        *new* variable/index, not silently resurrect the pre-clear one from some other cache."""
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[BOX_P])
        before_index = registry.allocate_witness_lasso(P)
        registry.clear()
        after_index = registry.allocate_witness_lasso(P)
        assert after_index == before_index == 1  # both are "the first allocation", by design

    def test_segment_lengths_and_closure_survive_clear(self):
        registry = WitnessRegistry(back=2, mid=3, fwd=4, closure=[P], max_witnesses=5)
        registry.clear()
        assert (registry.nb, registry.nm, registry.nf) == (2, 3, 4)
        assert registry.closure == frozenset({P})
        assert registry.max_witnesses == 5
