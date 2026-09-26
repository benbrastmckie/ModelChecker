"""The rotation/permutation symmetry group acting on a witness-family certificate.

**What this module is for.** `BimodalModelIterator` (`theory_lib/bimodal/iterate.py`) needs a
single, shared definition of "two certificates denote the same model up to relabeling" so its
isomorphism *detector* (`_check_model_isomorphism`) and its orbit *excluder*
(`_create_non_isomorphic_constraint`) cannot drift apart -- mirroring the existing precedent
where `semantic/witness_constraints.py` imports `_coherence_window`/`_scan_forward_bound`/
`_scan_backward_bound` directly from `semantic/certificate.py` rather than restating them.

## The group: `(Z/nb x Z/nf)^L (rtimes) S_k`

A certificate is a `WitnessFamily` of `L = 1 + k` lassos: `lassos[0]` is the main lasso (where
the target condition C4 is read) and `lassos[1..k]` are witness lassos for boxed subformulas
(`semantic/witness_registry.py`'s `allocate_witness_lasso`). A group element combines two
independent pieces of freedom:

- **Rotation**: each of the `L` lassos gets its own independent `(back_shift, fwd_shift)` pair,
  cyclically rotating that lasso's `back`/`fwd` segments (`rotate_lasso`). `mid` is never
  rotated: it is read by absolute position (`LabelledLasso.label`), not periodically, so it has
  no periodic structure to rotate.
- **Permutation**: the `k` witness-lasso *indices* `1..k` may be permuted (`permute_witnesses`),
  holding lasso `0` fixed -- there is exactly one main lasso and permuting it away from index `0`
  would change which lasso the target condition reads.

The group size is `(nb * nf)**L * factorial(L - 1)` (`enumerate_group`'s docstring works this
out per-lasso): `nb * nf` independent rotation choices per lasso, `L` lassos, times `k! = (L-1)!`
permutations of the witness tail. This grows quickly (`nb=nf=4`, three witness lassos already
gives a five-figure group), so `enumerate_group` accepts a `cap` and falls back to a small,
documented *reduced* generating set once the full group would exceed it -- see its own
docstring for the exact fallback shape and the completeness trade-off this makes (search-bound
relative, in the same spirit as `docs/ADEQUACY.md` section 7's own open search-bound caveat).

## D-A: permutation is provably condition-preserving; rotation is not

Permuting witness-lasso indices `1..k` preserves all four certificate conditions
(`certificate.py`'s `_coherent_at`/`_fulfil_at`/`_box_faithful`/`_target_holds`) by inspection:
C1 and C2 are evaluated per lasso independently of its index, C3 quantifies universally over
`family.lassos` (so it is invariant under any reordering), and C4 reads `family.main` only, which
permutation fixes. Rotation is *not* generally condition-preserving: `LabelledLasso.label`
decodes `back[t % nb]` for `t < 0`, `mid[t]` for `0 <= t < nm`, and `fwd[(t - nm) % nf]` for
`t >= nm`, so rotating `back` moves which tuple entry sits at position `-1` while leaving
position `0` untouched, and C1/C2 read the immediate neighbours `t +/- 1` *across* that boundary.
A nontrivial rotation therefore re-pairs the biconditionals at the back/mid and mid/fwd
boundaries and has no a-priori reason to stay coherent.

Consequence: nothing in this module ever *asserts* that a rotated/permuted family is a valid
certificate. `apply` is a pure relabeling function -- it computes what the transformed family
*would be*, nothing more. Every caller that needs a guarantee re-checks the result with
`certificate.recheck` before relying on it (see `iterate.py`'s detector and excluder, decisions
D-B/D-C in the implementation plan).

## Slot-level action, for the raw Z3 exclusion clause

Detection compares *decoded* certificates (`certificate_orbit_key`, pure Python, no Z3).
Exclusion must instead act on the raw `WitnessRegistry` variables
(`_bits`/`_guesses`/`WitnessConstraintGenerator._sel`), because that is the only representation
`ConstraintGenerator.check_satisfiability` understands. `slot_action`/`selector_action` give the
same rotation/permutation action at that lower level: `slot_action` maps every
`(lasso, position_slot, formula)` key in `registry._bits` to the key it moves to under a group
element, and `selector_action` does the same for a target-selector position in
`registry.target_window()`. Box guesses (`_guesses`) are never touched by either action: a guess
is per-formula, global to the whole family, not per-lasso or per-position -- there is nothing for
rotation or permutation to move it to.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import factorial
from itertools import permutations, product
from typing import Dict, Iterable, List, Sequence, Tuple

from .certificate import LabelledLasso, WitnessFamily

__all__ = [
    "GroupElement",
    "DEFAULT_GROUP_CAP",
    "rotate_lasso",
    "permute_witnesses",
    "enumerate_group",
    "apply",
    "certificate_orbit_key",
    "slot_action",
    "selector_action",
]


# A group element is deliberately a plain, hashable, frozen dataclass rather than a bare tuple:
# `rotations`/`perm` on their own are easy to transpose by accident (both are tuples of ints),
# and naming the fields catches that class of bug at construction time.
@dataclass(frozen=True)
class GroupElement:
    """One element of `(Z/nb x Z/nf)^L (rtimes) S_k`.

    `rotations[i] = (back_shift, fwd_shift)` is the rotation applied to the lasso that is at
    index `i` *before* permutation reorders the witness tail (`apply`'s composition order:
    rotate every lasso in place by its own original index, then permute the rotated tail).
    `len(rotations) == L`.

    `perm` is a permutation of `1..k` (`k = L - 1`), read as: the new witness tail is
    `[rotated[perm[0]], rotated[perm[1]], ..., rotated[perm[k-1]]]`. The identity permutation is
    `(1, 2, ..., k)`.
    """

    rotations: Tuple[Tuple[int, int], ...]
    perm: Tuple[int, ...]


# Group size at nb=nf=2, three lassos (one main + two witnesses): (2*2)**3 * 2! = 128 -- small.
# Group size at nb=nf=4, four lassos (one main + three witnesses): (4*4)**4 * 3! = 393216 -- the
# point at which enumerating the full group per exclusion clause becomes impractical. The cap is
# set well below that so the fallback generating set (see `enumerate_group`) engages before
# enumeration itself becomes the bottleneck.
DEFAULT_GROUP_CAP = 4096


def _label_key(label: "frozenset") -> Tuple[str, ...]:
    """A deterministic, total, sortable key for one label (a `FrozenSet[Formula]`).

    `semantic/formula.py`'s formula dataclasses are `frozen=True` but not `order=True`, so `<`
    is not defined between them -- sort by `repr` instead, which is deterministic and total.
    """
    return tuple(sorted(repr(formula) for formula in label))


def _segment_key(segment: Sequence["frozenset"]) -> Tuple[Tuple[str, ...], ...]:
    return tuple(_label_key(label) for label in segment)


def _canonical_rotation(segment_key: Tuple[Tuple[str, ...], ...], n: int) -> Tuple[int, Tuple[Tuple[str, ...], ...]]:
    """The lexicographically-smallest rotation of `segment_key` (length `n`), and the smallest
    shift that achieves it. Ties (a periodic segment has several equally-minimal rotations) are
    broken by preferring the smaller shift -- deterministic, since shifts are tried in increasing
    order and only a strictly smaller key ever replaces the current best."""
    if n == 0:
        return 0, segment_key
    best_shift = 0
    best_rotation = segment_key
    for shift in range(1, n):
        rotated = tuple(segment_key[(i + shift) % n] for i in range(n))
        if rotated < best_rotation:
            best_rotation = rotated
            best_shift = shift
    return best_shift, best_rotation


def _wrap(t: int, nb: int, nm: int, nf: int) -> int:
    """Mirrors `WitnessRegistry.wrap` exactly (duck-typed here rather than imported, since this
    module must stay solver-free and `WitnessRegistry` is a Z3-variable-holding class)."""
    if t < 0:
        return t % nb
    if t < nm:
        return nb + t
    return nb + nm + (t - nm) % nf


def _slot_image(slot: int, back_shift: int, fwd_shift: int, nb: int, nm: int, nf: int) -> int:
    """Where slot `slot` moves to under rotation `(back_shift, fwd_shift)`: the *new* slot whose
    value, after rotation, equals the *old* value that used to sit at `slot`. Mid slots
    (`[nb, nb+nm)`) are fixed points -- mid is never rotated."""
    if slot < nb:
        return (slot - back_shift) % nb
    if slot < nb + nm:
        return slot
    j = slot - nb - nm
    return nb + nm + (j - fwd_shift) % nf


def _window_position_for_slot(slot: int, nb: int) -> int:
    """The inverse of `_wrap` restricted to one representative position per slot: every region
    (back, mid, fwd) satisfies `position = slot - nb` (back slots are `[0, nb)` -> `[-nb, 0)`;
    mid/fwd slots are `[nb, nb+nm+nf)` -> `[0, nm+nf)`), so one formula covers all three."""
    return slot - nb


def _shift_target_time(t: int, back_shift: int, fwd_shift: int, nb: int, nm: int, nf: int) -> int:
    """Where target time `t` moves under lasso `0`'s rotation `(back_shift, fwd_shift)`: the
    representative position, within `WitnessRegistry.target_window()`, whose slot is the image
    of `t`'s own slot under that rotation. Left unchanged for `t` in the mid region, since mid
    slots are fixed points of `_slot_image`."""
    slot = _wrap(t, nb, nm, nf)
    new_slot = _slot_image(slot, back_shift, fwd_shift, nb, nm, nf)
    return _window_position_for_slot(new_slot, nb)


def rotate_lasso(lasso: LabelledLasso, back_shift: int, fwd_shift: int) -> LabelledLasso:
    """Cyclically rotate `lasso`'s `back`/`fwd` segments independently; `mid` is untouched.

    `new_back[i] = lasso.back[(i + back_shift) % nb]` (and symmetrically for `fwd`), so shift
    `(0, 0)` is the identity and shifts are taken modulo `nb`/`nf` regardless of sign or
    magnitude.
    """
    nb, nf = lasso.nb, lasso.nf
    back_shift %= nb
    fwd_shift %= nf
    new_back = tuple(lasso.back[(i + back_shift) % nb] for i in range(nb))
    new_fwd = tuple(lasso.fwd[(i + fwd_shift) % nf] for i in range(nf))
    return LabelledLasso(back=new_back, mid=lasso.mid, fwd=new_fwd)


def permute_witnesses(family: WitnessFamily, perm: Sequence[int]) -> WitnessFamily:
    """Reorder `family.lassos[1:]` according to `perm` (a permutation of `1..k`); `lassos[0]`
    and `family.bx` are untouched. `perm[j]` names the *old* witness index that becomes the new
    witness at position `j`."""
    k = len(family.lassos) - 1
    perm = tuple(perm)
    if sorted(perm) != list(range(1, k + 1)):
        raise ValueError(
            f"perm must be a permutation of 1..{k}, got {perm!r}"
        )
    tail = tuple(family.lassos[i] for i in perm)
    return WitnessFamily(bx=family.bx, lassos=(family.lassos[0],) + tail)


def _identity_element(lasso_count: int) -> GroupElement:
    k = lasso_count - 1
    return GroupElement(
        rotations=tuple((0, 0) for _ in range(lasso_count)),
        perm=tuple(range(1, k + 1)),
    )


def _full_group_size(nb: int, nf: int, lasso_count: int) -> int:
    return (nb * nf) ** lasso_count * factorial(lasso_count - 1)


def _enumerate_full_group(nb: int, nf: int, lasso_count: int) -> Iterable[GroupElement]:
    k = lasso_count - 1
    rotation_choices = list(product(range(nb), range(nf)))
    for rotations in product(rotation_choices, repeat=lasso_count):
        for perm in permutations(range(1, k + 1)):
            yield GroupElement(rotations=tuple(rotations), perm=perm)


def _enumerate_reduced_generating_set(nb: int, nf: int, lasso_count: int) -> Iterable[GroupElement]:
    """The documented fallback once the full group would exceed `cap`: the identity, every
    single-segment single-lasso rotation, and every adjacent transposition of witness indices.
    This is a small, tractable subset of the group -- not its closure -- so exclusion built from
    it is sound (every element is still a genuine, recheck-gated relabeling) but not complete: a
    duplicate reachable only by a *combination* of these moves may still slip through. That
    trade-off is the point of the cap (see the module docstring and the plan's Risk table)."""
    k = lasso_count - 1
    identity_rotations = tuple((0, 0) for _ in range(lasso_count))
    identity_perm = tuple(range(1, k + 1))
    yield GroupElement(rotations=identity_rotations, perm=identity_perm)

    for lasso in range(lasso_count):
        for shift in range(1, nb):
            rotations = list(identity_rotations)
            rotations[lasso] = (shift, 0)
            yield GroupElement(rotations=tuple(rotations), perm=identity_perm)
        for shift in range(1, nf):
            rotations = list(identity_rotations)
            rotations[lasso] = (0, shift)
            yield GroupElement(rotations=tuple(rotations), perm=identity_perm)

    for i in range(1, k):
        perm = list(identity_perm)
        perm[i - 1], perm[i] = perm[i], perm[i - 1]
        yield GroupElement(rotations=identity_rotations, perm=tuple(perm))


def enumerate_group(
    nb: int, nf: int, lasso_count: int, cap: int = DEFAULT_GROUP_CAP
) -> Iterable[GroupElement]:
    """Enumerate `(Z/nb x Z/nf)^lasso_count (rtimes) S_{lasso_count - 1}`, identity first.

    When the full group's size, `(nb * nf) ** lasso_count * factorial(lasso_count - 1)`, is at
    or under `cap`, every element is yielded (identity first, by construction: both
    `itertools.product` over `range(nb)`/`range(nf)` and `itertools.permutations` of the already-
    sorted `1..k` start their iteration at the all-zero/identity combination). Otherwise falls
    back to the small reduced generating set documented in
    `_enumerate_reduced_generating_set` -- identity, single-segment single-lasso rotations, and
    adjacent witness transpositions.
    """
    if lasso_count < 1:
        raise ValueError(f"lasso_count must be >= 1, got {lasso_count!r}")
    if _full_group_size(nb, nf, lasso_count) <= cap:
        yield from _enumerate_full_group(nb, nf, lasso_count)
    else:
        yield from _enumerate_reduced_generating_set(nb, nf, lasso_count)


def apply(element: GroupElement, family: WitnessFamily, target_time: int) -> Tuple[WitnessFamily, int]:
    """Apply `element` to `family`/`target_time`: rotate every lasso by its own entry in
    `element.rotations`, then reorder the rotated witness tail by `element.perm`. The target time
    is moved under lasso `0`'s rotation alone (`_shift_target_time`); it is left unchanged when
    lasso `0`'s rotation is `(0, 0)`.

    This is a pure relabeling -- it makes no claim that the result is a valid certificate (see
    the module docstring's D-A section). Callers that need that guarantee must run
    `certificate.recheck` on the result themselves.
    """
    lassos = family.lassos
    if len(element.rotations) != len(lassos):
        raise ValueError(
            f"element has {len(element.rotations)} rotations for {len(lassos)} lassos"
        )
    rotated = [
        rotate_lasso(lasso, back_shift, fwd_shift)
        for lasso, (back_shift, fwd_shift) in zip(lassos, element.rotations)
    ]
    main = rotated[0]
    back_shift, fwd_shift = element.rotations[0]
    new_target_time = _shift_target_time(target_time, back_shift, fwd_shift, main.nb, main.nm, main.nf)
    tail = tuple(rotated[i] for i in element.perm)
    new_family = WitnessFamily(bx=family.bx, lassos=(main,) + tail)
    return new_family, new_target_time


def certificate_orbit_key(family: WitnessFamily, target_time: int):
    """A canonical, orbit-invariant key: equal for any two families/target-times related by a
    group element (a rotation, a witness permutation, or both), and equal only then (short of a
    genuine coincidence in canonical form -- see below).

    Construction: each lasso's `back`/`fwd` segments are independently canonicalized to their
    lexicographically-smallest rotation (`_canonical_rotation`) -- this is exactly what makes the
    key rotation-invariant, since every rotation of a given lasso canonicalizes to the same
    representative. Lasso `0`'s canonicalizing shift additionally locates which *label* the
    target position reads in that canonical array (not the raw position integer -- see below).
    The witness lassos' canonical forms are then sorted as a multiset, which is what makes the
    key permutation-invariant. `bx` is normalized to its `True` entries only (`bx_of` already
    defaults a missing formula to `False`, so an explicit `False` entry is representation noise,
    not semantic content).

    **Why the target component is a label, not a position.** A naive design would carry
    `_shift_target_time(target_time, ...)`'s numeric result in the key. That breaks when the
    canonicalizing segment is itself periodic with a period properly dividing its length (e.g.
    `back = (p, q, p, q)`, period 2 inside `nb = 4`): two orbit-equivalent representatives can
    legitimately canonicalize to the *same* array by *different* shifts differing by that period,
    which relocates the target to two different -- but, because of the very periodicity that
    caused the tie, label-*equal* -- positions in the identical canonical array. Comparing labels
    (what C4 actually reads) rather than positions makes the key invariant to exactly this case;
    `_canonical_rotation`'s smallest-shift tie-break keeps `apply`/`_shift_target_time`'s own
    position bookkeeping deterministic, but this key never round-trips through that numeric
    position at all.

    Not claimed to be injective on the full space of `WitnessFamily` values in general -- only
    that it separates orbit-equivalent families from a genuinely different `mid` or `bx`, which
    is all `_check_model_isomorphism`/`_create_non_isomorphic_constraint` need.
    """
    main = family.lassos[0]
    nb, nm, nf = main.nb, main.nm, main.nf

    main_back_key = _segment_key(main.back)
    main_fwd_key = _segment_key(main.fwd)
    main_mid_key = _segment_key(main.mid)
    back_shift, canonical_back = _canonical_rotation(main_back_key, nb)
    fwd_shift, canonical_fwd = _canonical_rotation(main_fwd_key, nf)

    target_slot = _wrap(target_time, nb, nm, nf)
    canonical_target_slot = _slot_image(target_slot, back_shift, fwd_shift, nb, nm, nf)
    if canonical_target_slot < nb:
        target_label_key = canonical_back[canonical_target_slot]
    elif canonical_target_slot < nb + nm:
        target_label_key = main_mid_key[canonical_target_slot - nb]
    else:
        target_label_key = canonical_fwd[canonical_target_slot - nb - nm]

    main_repr = (canonical_back, main_mid_key, canonical_fwd)

    witness_reprs: List[Tuple[object, object, object]] = []
    for lasso in family.lassos[1:]:
        back_key = _segment_key(lasso.back)
        fwd_key = _segment_key(lasso.fwd)
        mid_key = _segment_key(lasso.mid)
        _, canon_back = _canonical_rotation(back_key, lasso.nb)
        _, canon_fwd = _canonical_rotation(fwd_key, lasso.nf)
        witness_reprs.append((canon_back, mid_key, canon_fwd))
    witness_reprs.sort()

    bx_key = tuple(sorted(repr(formula) for formula, value in family.bx.items() if value))

    return (bx_key, main_repr, target_label_key, tuple(witness_reprs))


def slot_action(registry, element: GroupElement) -> Dict[Tuple[int, int, object], Tuple[int, int, object]]:
    """The action of `element` on every `(lasso, slot, formula)` key currently in
    `registry._bits`: maps each such key to the key it moves to. A bijection on that key set,
    since rotation is a bijection on slots (mod `nb`/`nf`, identity on mid) and `element.perm` is
    a permutation of the witness indices.

    `registry` is duck-typed on `.nb`/`.nm`/`.nf`/`._bits`, matching the convention already used
    by `certificate.py`'s window helpers and `witness_constraints.py`'s encoder.
    """
    nb, nm, nf = registry.nb, registry.nm, registry.nf
    perm = element.perm

    def _new_lasso(old_lasso: int) -> int:
        if old_lasso == 0:
            return 0
        return perm.index(old_lasso) + 1

    mapping: Dict[Tuple[int, int, object], Tuple[int, int, object]] = {}
    for key in registry._bits.keys():
        lasso, slot, formula = key
        back_shift, fwd_shift = element.rotations[lasso]
        new_slot = _slot_image(slot, back_shift, fwd_shift, nb, nm, nf)
        mapping[key] = (_new_lasso(lasso), new_slot, formula)
    return mapping


def selector_action(registry, element: GroupElement) -> Dict[int, int]:
    """The action of `element` on every position in `registry.target_window()`: maps each
    position to its image under lasso `0`'s rotation (`_shift_target_time`). A bijection on the
    window, since `_shift_target_time` is built from `_slot_image`, itself a bijection."""
    nb, nm, nf = registry.nb, registry.nm, registry.nf
    back_shift, fwd_shift = element.rotations[0]
    return {
        t: _shift_target_time(t, back_shift, fwd_shift, nb, nm, nf)
        for t in registry.target_window()
    }
