"""Unit tests for `theory_lib/bimodal/semantic/symmetry.py`: the rotation/permutation
symmetry group, its two actions (on decoded certificates and on raw `WitnessRegistry`
keys), and the orbit-invariant canonical key. Deliberately solver-free -- no Z3 model is
built anywhere in this module -- matching `test_certificate.py`/`test_witness_registry.py`'s
own unit-test posture.
"""

from __future__ import annotations

from math import factorial

import pytest

from model_checker.theory_lib.bimodal.semantic import symmetry
from model_checker.theory_lib.bimodal.semantic.certificate import LabelledLasso, WitnessFamily
from model_checker.theory_lib.bimodal.semantic.formula import Atom, Box
from model_checker.theory_lib.bimodal.semantic.witness_registry import WitnessRegistry

P = Atom("p")
Q = Atom("q")
R = Atom("r")


def _label(*formulas):
    return frozenset(formulas)


def _lasso(back, mid, fwd):
    return LabelledLasso(back=tuple(back), mid=tuple(mid), fwd=tuple(fwd))


class TestRotateLasso:
    def test_identity_shift_is_a_noop(self):
        lasso = _lasso([_label(P), _label(Q)], [_label()], [_label(P), _label()])
        rotated = symmetry.rotate_lasso(lasso, 0, 0)
        assert rotated == lasso

    def test_back_and_fwd_rotate_cyclically_mid_untouched(self):
        lasso = _lasso([_label(P), _label(Q)], [_label(R)], [_label(P), _label()])
        rotated = symmetry.rotate_lasso(lasso, 1, 1)
        assert rotated.back == (_label(Q), _label(P))
        assert rotated.fwd == (_label(), _label(P))
        assert rotated.mid == lasso.mid

    def test_shift_is_taken_modulo_segment_length(self):
        lasso = _lasso([_label(P), _label(Q)], [], [_label(P), _label()])
        rotated_by_2 = symmetry.rotate_lasso(lasso, 2, 0)
        assert rotated_by_2.back == lasso.back  # 2 % nb(=2) == 0
        rotated_by_neg1 = symmetry.rotate_lasso(lasso, -1, 0)
        rotated_by_1 = symmetry.rotate_lasso(lasso, 1, 0)
        assert rotated_by_neg1.back == rotated_by_1.back  # -1 % 2 == 1


class TestPermuteWitnesses:
    def _family(self):
        main = _lasso([_label()], [], [_label()])
        w1 = _lasso([_label(P)], [], [_label(P)])
        w2 = _lasso([_label(Q)], [], [_label(Q)])
        return WitnessFamily(bx={P: True}, lassos=(main, w1, w2))

    def test_reorders_only_the_witness_tail(self):
        family = self._family()
        permuted = symmetry.permute_witnesses(family, (2, 1))
        assert permuted.lassos[0] == family.lassos[0]
        assert permuted.lassos[1] == family.lassos[2]
        assert permuted.lassos[2] == family.lassos[1]

    def test_bx_is_untouched(self):
        family = self._family()
        permuted = symmetry.permute_witnesses(family, (2, 1))
        assert permuted.bx == family.bx

    def test_rejects_a_non_permutation(self):
        family = self._family()
        with pytest.raises(ValueError):
            symmetry.permute_witnesses(family, (1, 1))
        with pytest.raises(ValueError):
            symmetry.permute_witnesses(family, (1,))


class TestEnumerateGroup:
    def test_identity_is_first(self):
        elements = list(symmetry.enumerate_group(2, 2, 3))
        identity = elements[0]
        assert identity.rotations == ((0, 0), (0, 0), (0, 0))
        assert identity.perm == (1, 2)

    def test_full_group_size_under_cap(self):
        elements = list(symmetry.enumerate_group(2, 2, 3, cap=symmetry.DEFAULT_GROUP_CAP))
        expected = (2 * 2) ** 3 * factorial(2)
        assert expected == 128
        assert len(elements) == expected

    def test_falls_back_to_reduced_generating_set_over_cap(self):
        elements = list(symmetry.enumerate_group(2, 2, 3, cap=10))
        # identity + lasso_count*(nb-1) + lasso_count*(nf-1) + (k-1) adjacent transpositions
        expected = 1 + 3 * 1 + 3 * 1 + 1
        assert expected == 8
        assert len(elements) == expected
        assert elements[0].rotations == ((0, 0), (0, 0), (0, 0))
        assert elements[0].perm == (1, 2)

    def test_single_lasso_no_witnesses(self):
        elements = list(symmetry.enumerate_group(2, 2, 1))
        # k = 0: only rotation freedom, no permutation freedom (factorial(0) == 1).
        assert len(elements) == 4
        assert all(e.perm == () for e in elements)


class TestApply:
    def _family(self):
        main = _lasso([_label(P), _label()], [_label(Q)], [_label(P), _label()])
        witness = _lasso([_label(R)], [], [_label(R), _label()])
        return WitnessFamily(bx={P: True}, lassos=(main, witness))

    def test_identity_element_is_a_noop(self):
        family = self._family()
        identity = symmetry._identity_element(2)
        new_family, new_time = symmetry.apply(identity, family, 0)
        assert new_family == family
        assert new_time == 0

    def test_rotating_lasso_zero_moves_the_target_time(self):
        family = self._family()
        element = symmetry.GroupElement(rotations=((1, 0), (0, 0)), perm=(1,))
        new_family, new_time = symmetry.apply(element, family, -1)
        assert new_family.lassos[0].back == (family.lassos[0].back[1], family.lassos[0].back[0])
        assert new_time != -1

    def test_rotating_a_witness_lasso_does_not_move_the_target_time(self):
        family = self._family()
        element = symmetry.GroupElement(rotations=((0, 0), (1, 0)), perm=(1,))
        _, new_time = symmetry.apply(element, family, -1)
        assert new_time == -1

    def test_permutation_reorders_the_transformed_tail(self):
        main = _lasso([_label()], [], [_label()])
        w1 = _lasso([_label(P)], [], [_label(P)])
        w2 = _lasso([_label(Q)], [], [_label(Q)])
        family = WitnessFamily(bx={}, lassos=(main, w1, w2))
        element = symmetry.GroupElement(rotations=((0, 0), (0, 0), (0, 0)), perm=(2, 1))
        new_family, _ = symmetry.apply(element, family, 0)
        assert new_family.lassos[1] == w2
        assert new_family.lassos[2] == w1


class TestCertificateOrbitKey:
    def _family(self, back0=(P,), fwd0=(P,), mid0=(), bx=None):
        main = _lasso([_label(f) for f in back0], [_label(f) for f in mid0], [_label(f) for f in fwd0])
        return WitnessFamily(bx=bx or {}, lassos=(main,))

    def test_equal_for_a_rotation_equivalent_pair(self):
        main = _lasso([_label(P), _label()], [], [_label(Q), _label()])
        family = WitnessFamily(bx={}, lassos=(main,))
        element = symmetry.GroupElement(rotations=((1, 1),), perm=())
        rotated_family, rotated_time = symmetry.apply(element, family, -1)

        key1 = symmetry.certificate_orbit_key(family, -1)
        key2 = symmetry.certificate_orbit_key(rotated_family, rotated_time)
        assert key1 == key2

    def test_equal_for_a_witness_permutation_equivalent_pair(self):
        main = _lasso([_label()], [], [_label()])
        w1 = _lasso([_label(P)], [], [_label(P)])
        w2 = _lasso([_label(Q)], [], [_label(Q)])
        family = WitnessFamily(bx={}, lassos=(main, w1, w2))
        permuted = symmetry.permute_witnesses(family, (2, 1))

        assert symmetry.certificate_orbit_key(family, 0) == symmetry.certificate_orbit_key(permuted, 0)

    def test_equal_for_a_combined_rotation_and_permutation_pair(self):
        main = _lasso([_label(P), _label()], [], [_label()])
        w1 = _lasso([_label(P)], [], [_label(P), _label()])
        w2 = _lasso([_label(Q)], [], [_label(Q), _label()])
        family = WitnessFamily(bx={}, lassos=(main, w1, w2))
        element = symmetry.GroupElement(rotations=((1, 1), (0, 1), (1, 0)), perm=(2, 1))
        transformed, transformed_time = symmetry.apply(element, family, -1)

        key1 = symmetry.certificate_orbit_key(family, -1)
        key2 = symmetry.certificate_orbit_key(transformed, transformed_time)
        assert key1 == key2

    def test_unequal_for_a_different_bx(self):
        family_a = self._family(bx={P: True})
        family_b = self._family(bx={P: False})
        assert symmetry.certificate_orbit_key(family_a, 0) != symmetry.certificate_orbit_key(family_b, 0)

    def test_unequal_for_a_mid_difference_no_group_element_can_move(self):
        family_a = self._family(mid0=(P,))
        family_b = self._family(mid0=(Q,))
        assert symmetry.certificate_orbit_key(family_a, 0) != symmetry.certificate_orbit_key(family_b, 0)

    def test_deterministic_and_total_on_frozen_unordered_formula_labels(self):
        family = self._family()
        key1 = symmetry.certificate_orbit_key(family, 0)
        key2 = symmetry.certificate_orbit_key(family, 0)
        assert key1 == key2
        # must not raise TypeError from an attempted `<` comparison between Formula objects
        assert isinstance(key1, tuple)

    def test_tie_breaking_is_deterministic_for_a_periodic_back(self):
        # back = (P, Q, P, Q) -- shifts 0 and 2 both rotate to the identical sequence.
        main = _lasso([_label(P), _label(Q), _label(P), _label(Q)], [], [_label()])
        family = WitnessFamily(bx={}, lassos=(main,))
        # Rotating by the tied shift (2) must canonicalize to the exact same key/target.
        element = symmetry.GroupElement(rotations=((2, 0),), perm=())
        rotated_family, rotated_time = symmetry.apply(element, family, -1)

        key1 = symmetry.certificate_orbit_key(family, -1)
        key2 = symmetry.certificate_orbit_key(rotated_family, rotated_time)
        assert key1 == key2
        # Calling twice on the same input is itself deterministic.
        assert symmetry.certificate_orbit_key(family, -1) == key1


class TestGuessAction:
    def test_no_guess_action_function_exists(self):
        """Box guesses are per-formula and global to the family -- never per-lasso or
        per-position -- so there is nothing for rotation or permutation to move them to.
        This pins that design decision: no `guess_action` is exported, and the excluder
        (`iterate.py`) must carry every `_guesses` variable through unchanged."""
        assert not hasattr(symmetry, "guess_action")


class TestSlotAction:
    def _registry(self):
        registry = WitnessRegistry(back=2, mid=1, fwd=2, closure=[P, Q])
        for lasso in (0, 1, 2):
            for t in range(-2, 4):
                registry.bit(lasso, t, P)
        return registry

    def test_is_a_bijection_on_the_key_set(self):
        registry = self._registry()
        element = symmetry.GroupElement(rotations=((1, 0), (0, 1), (0, 0)), perm=(2, 1))
        mapping = symmetry.slot_action(registry, element)
        assert set(mapping.keys()) == set(registry._bits.keys())
        assert set(mapping.values()) == set(registry._bits.keys())
        assert len(set(mapping.values())) == len(mapping)

    def test_mid_slots_are_fixed_points(self):
        registry = self._registry()
        element = symmetry.GroupElement(rotations=((1, 1), (1, 1), (1, 1)), perm=(2, 1))
        mapping = symmetry.slot_action(registry, element)
        for (lasso, slot, formula), (new_lasso, new_slot, new_formula) in mapping.items():
            if registry.nb <= slot < registry.nb + registry.nm:
                assert new_slot == slot
            assert new_formula == formula

    def test_permutation_component_fixes_lasso_zero(self):
        registry = self._registry()
        element = symmetry.GroupElement(rotations=((0, 0), (0, 0), (0, 0)), perm=(2, 1))
        mapping = symmetry.slot_action(registry, element)
        for (lasso, slot, formula), (new_lasso, new_slot, new_formula) in mapping.items():
            if lasso == 0:
                assert new_lasso == 0
            else:
                assert new_lasso in (1, 2)


class TestSelectorAction:
    def test_is_a_bijection_on_the_window(self):
        registry = WitnessRegistry(back=2, mid=1, fwd=2, closure=[P])
        element = symmetry.GroupElement(rotations=((1, 1), (0, 0)), perm=(1,))
        mapping = symmetry.selector_action(registry, element)
        window = set(registry.target_window())
        assert set(mapping.keys()) == window
        assert set(mapping.values()) == window

    def test_identity_rotation_is_the_identity_map(self):
        registry = WitnessRegistry(back=2, mid=1, fwd=2, closure=[P])
        element = symmetry._identity_element(1)
        mapping = symmetry.selector_action(registry, element)
        for t in registry.target_window():
            assert mapping[t] == t
