"""Witness-family certificate datatypes and the certificate wire-format writer.

`LabelledLasso` and `WitnessFamily` mirror `FormalSystem.Metalogic.Decidability.WitnessFamily`'s
`LabelledLasso`/`WitnessFamily`
(`~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/WitnessFamily/Basic.lean`): a
certificate is a box guess (`bx`) plus a non-empty list of labelled bi-lassos, `lassos[0]` the
main lasso where the target condition is read.

## Three-segment decoding

`LabelledLasso.label(t)` mirrors `Periodic.unrollOf`
(`~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/BiLasso/Periodic.lean`): strictly
negative positions repeat `back` cyclically, positions in `[0, len(mid))` read `mid` directly,
and positions at or past `len(mid)` repeat `fwd` cyclically. `back` and `fwd` must be non-empty
(`LabelledLasso.back_ne`/`fwd_ne` in Lean); `mid` may be empty. Python's `%` operator agrees with
Lean's `Int.emod` for a positive modulus (both non-negative), so no adjustment is needed for the
cyclic reads.

## Extension point: lasso state sharing (not implemented)

`WitnessFamily.lassos` is a plain tuple of independent `LabelledLasso`s -- lassos never share
positions. This is deliberate and load-bearing, not merely the simplest first cut: determinism
(no shared state) is exactly what makes `ShiftSet.total_eq_orbit`
(`Semantics/ShiftSet.lean:252`) true -- every world history equals one of the lasso orbits -- and
that correspondence is what makes Box's range exactly the certified histories, which in turn is
what makes the Box case of the certificate truth lemma go through. It is *not* about Limit or
Saturation, which are both cheap over `Z` regardless (`Int.abs_lt_one_iff` and subsingleton
fibres respectively -- see `docs/ADEQUACY.md`'s "Why the design is deterministic"). Adding
inter-lasso state sharing later therefore requires re-proving the histories correspondence and
redesigning box faithfulness around it, not re-arguing Limit/Saturation -- so it is not attempted
here; a future extension would add an explicit sharing structure (e.g. a union-find over
`(lasso_index, position)` pairs) rather than mutating this module's plain-tuple representation
in place.

## Wire format

`WitnessFamily.to_json` mirrors the fixed external contract documented in
`~/Projects/BimodalLogic/BimodalTools/README.md`'s "Certificate re-verification protocol":

```json
{"target": {"premises": [...], "conclusions": [...], "time": 0},
 "bx":     [[<formula>, true], [<formula>, false], ...],
 "lassos": [{"back": [<label>, ...], "mid": [<label>, ...], "fwd": [<label>, ...]}, ...]}
```

`bx` is sparse: a formula not listed reads as `false` (`WitnessFamily.bx_of`'s default).
`target.time` is always emitted explicitly, even when `0` -- the README is explicit that a
defaulted `0` would silently conflate "the origin, by convention" with "no explicit witness for
this existential," which every other witness in a certificate has.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, Iterable, List, Mapping, Optional, Tuple

from .formula import Atom, Bot, Box, Formula, Imp, Snce, Untl, closure_of, to_json

__all__ = ["LabelledLasso", "WitnessFamily", "recheck"]


Label = FrozenSet[Formula]


@dataclass(frozen=True)
class LabelledLasso:
    """A labelled bi-infinite lasso: `back`/`mid`/`fwd` segments, each a tuple of labels.

    Mirrors `LabelledLasso Γ Del` (`WitnessFamily/Basic.lean`), minus the closure-membership
    proof obligation `label_sub` -- callers check `all_labels() <= closure_of(context)`
    themselves (see `TestLabelsConfinedToClosure` in `tests/unit/test_certificate.py`), since a
    lasso alone does not know the context its closure is computed against.
    """

    back: Tuple[Label, ...]
    mid: Tuple[Label, ...]
    fwd: Tuple[Label, ...]

    def __post_init__(self) -> None:
        if not self.back:
            raise ValueError("back must be non-empty (LabelledLasso.back_ne)")
        if not self.fwd:
            raise ValueError("fwd must be non-empty (LabelledLasso.fwd_ne)")

    @property
    def nb(self) -> int:
        return len(self.back)

    @property
    def nm(self) -> int:
        return len(self.mid)

    @property
    def nf(self) -> int:
        return len(self.fwd)

    def label(self, t: int) -> Label:
        """Decode the label at integer position `t`, mirroring `Periodic.unrollOf`."""
        if t < 0:
            return self.back[t % self.nb]
        if t < self.nm:
            return self.mid[t]
        return self.fwd[(t - self.nm) % self.nf]

    def all_labels(self) -> FrozenSet[Formula]:
        """The union of every formula appearing in any label of this lasso (back, mid, or fwd)."""
        result: FrozenSet[Formula] = frozenset()
        for segment in (self.back, self.mid, self.fwd):
            for label in segment:
                result |= label
        return result

    def _segment_to_json(self, segment: Tuple[Label, ...]) -> List[List[Dict[str, object]]]:
        return [[to_json(formula) for formula in label] for label in segment]

    def to_json(self) -> Dict[str, object]:
        """Serialize this lasso's three segments to the wire shape `{"back": [...], "mid":
        [...], "fwd": [...]}`, each a list of labels (each a list of formula objects)."""
        return {
            "back": self._segment_to_json(self.back),
            "mid": self._segment_to_json(self.mid),
            "fwd": self._segment_to_json(self.fwd),
        }


@dataclass(frozen=True)
class WitnessFamily:
    """A witness-family certificate: the box guess plus a non-empty list of lassos.

    Mirrors `WitnessFamily Γ Del` (`WitnessFamily/Basic.lean`): `lassos[0]` (`main`) is where the
    target condition is read; `bx` is the (sparse) box guess, `bx_of` defaulting unlisted
    formulas to `False`, matching the wire format's sparse `bx` array.
    """

    bx: Mapping[Formula, bool]
    lassos: Tuple[LabelledLasso, ...]

    def __post_init__(self) -> None:
        if not self.lassos:
            raise ValueError("lassos must be non-empty")

    @property
    def main(self) -> LabelledLasso:
        return self.lassos[0]

    def bx_of(self, chi: Formula) -> bool:
        return bool(self.bx.get(chi, False))

    def to_json(
        self,
        premises: Iterable[Formula],
        conclusions: Iterable[Formula],
        target_time: int,
    ) -> Dict[str, object]:
        """Serialize the full certificate to the wire shape documented in the module docstring.

        `target_time` is always emitted, even when it equals `0` -- see the module docstring.
        """
        return {
            "target": {
                "premises": [to_json(p) for p in premises],
                "conclusions": [to_json(c) for c in conclusions],
                "time": target_time,
            },
            "bx": [[to_json(formula), bool(value)] for formula, value in self.bx.items()],
            "lassos": [lasso.to_json() for lasso in self.lassos],
        }


# ---------------------------------------------------------------------------
# Pure-Python re-checker of the four certificate conditions
# ---------------------------------------------------------------------------
#
# Mirrors `FormalSystem.Metalogic.Decidability.WitnessFamily.Predicates`'s `LocalCoherentLab`,
# `FulfillingLab`, `BoxFaithful` and `Target`
# (`~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/WitnessFamily/Predicates.lean`),
# and the proved window collapses of `Decide.lean`:
#
# - `coherent_iff_window` (`:335`) and `fulfil_iff_window` (`:743`) both collapse local
#   coherence and fulfilment to the *wide*, two-period window `[-2*nb, nm + 2*nf)`.
# - `mem_all_iff_window` (`:809`, `:883`) collapses box faithfulness to the *narrower*,
#   one-period window `[-nb, nm + nf)`. This is a genuinely different bound, not a rename of the
#   same one: local coherence and fulfilment read a position's immediate neighbour (`t-1`/`t+1`),
#   so a representative position needs its whole neighbourhood inside the periodic region (two
#   periods each side); box faithfulness reads no neighbours and collapses at one period.
# - `scan_forward`/`scan_backward` (`:192`, `:212`) give the corrected fulfilment witness-scan
#   bounds: forward to `max(t, nm) + nf`, backward to `min(t, 0) - nb`.
#
# independent of any Z3 model object, mirroring `check_certificate`'s verdict vocabulary
# (`~/Projects/BimodalLogic/BimodalTools/README.md`, "Certificate re-verification protocol"):
# `{"status": "countermodel", "time": t}` or `{"status": "rejected", "failed": [...]}`, each
# `failed` entry carrying `condition`, `lasso`, `position`, `formula`, `detail`. `recheck` never
# reports `"error"`: that status is for wire-level parse failures (missing `target`/`target.time`
# in raw JSON), which do not arise here since `target_time` is a required, already-typed
# parameter -- see the certificate-export/round-trip phase for the JSON-boundary wrapper.


def _coherence_window(lasso: "LabelledLasso") -> range:
    """`[-2*nb, nm + 2*nf)` -- the proved window for local coherence and fulfilment
    (`coherent_iff_window`/`fulfil_iff_window`)."""
    return range(-2 * lasso.nb, lasso.nm + 2 * lasso.nf)


def _box_window(lasso: "LabelledLasso") -> range:
    """`[-nb, nm + nf)` -- the proved window for box faithfulness (`mem_all_iff_window`)."""
    return range(-lasso.nb, lasso.nm + lasso.nf)


def _scan_forward_bound(lasso: "LabelledLasso", t: int) -> int:
    """`max(t, nm) + nf` -- the corrected forward witness-scan bound (`scan_forward`)."""
    return max(t, lasso.nm) + lasso.nf


def _scan_backward_bound(lasso: "LabelledLasso", t: int) -> int:
    """`min(t, 0) - nb` -- the corrected backward witness-scan bound (`scan_backward`)."""
    return min(t, 0) - lasso.nb


def _failed(
    condition: str,
    lasso: Optional[int],
    position: Optional[int],
    formula: Optional[Formula],
    detail: str,
) -> Dict[str, object]:
    return {
        "status": "rejected",
        "failed": [
            {
                "condition": condition,
                "lasso": lasso,
                "position": position,
                "formula": to_json(formula) if formula is not None else None,
                "detail": detail,
            }
        ],
    }


def _has_fresh_atom(formula: Formula) -> bool:
    if isinstance(formula, Atom):
        return formula.fresh_index is not None
    if isinstance(formula, Bot):
        return False
    if isinstance(formula, Imp):
        return _has_fresh_atom(formula.left) or _has_fresh_atom(formula.right)
    if isinstance(formula, Box):
        return _has_fresh_atom(formula.child)
    if isinstance(formula, (Untl, Snce)):
        return _has_fresh_atom(formula.guard) or _has_fresh_atom(formula.event)
    raise TypeError(f"not a Formula: {formula!r}")


def _coherent_at(
    closure: FrozenSet[Formula], family: "WitnessFamily", lasso: "LabelledLasso", t: int
) -> Tuple[bool, Optional[Formula]]:
    """(C1) `LocalCoherentLab` at a single position. Returns `(ok, failing_formula_or_None)`."""
    label = lasso.label(t)
    if any(isinstance(f, Bot) for f in label):
        return False, Bot()
    for f in closure:
        if isinstance(f, (Atom, Bot)):
            continue  # atoms are deliberately unconstrained; bot handled above
        if isinstance(f, Imp):
            lhs = f in label
            rhs = (f.left not in label) or (f.right in label)
            if lhs != rhs:
                return False, f
        elif isinstance(f, Box):
            lhs = f in label
            rhs = family.bx_of(f.child)
            if lhs != rhs:
                return False, f
        elif isinstance(f, Untl):
            lhs = f in label
            label_next = lasso.label(t + 1)
            rhs = (f.event in label_next) or (f.guard in label_next and f in label_next)
            if lhs != rhs:
                return False, f
        elif isinstance(f, Snce):
            lhs = f in label
            label_prev = lasso.label(t - 1)
            rhs = (f.event in label_prev) or (f.guard in label_prev and f in label_prev)
            if lhs != rhs:
                return False, f
    return True, None


def _fulfil_at(
    closure: FrozenSet[Formula], lasso: "LabelledLasso", t: int
) -> Tuple[bool, Optional[Formula]]:
    """(C2) `FulfillingLab` at a single position. Returns `(ok, failing_formula_or_None)`."""
    label = lasso.label(t)
    for f in closure:
        if isinstance(f, Untl):
            if f not in label:
                continue
            hi = _scan_forward_bound(lasso, t)
            found = False
            for s in range(t + 1, hi + 1):
                if f.event in lasso.label(s):
                    if all(f.guard in lasso.label(r) for r in range(t + 1, s)):
                        found = True
                        break
            if not found:
                return False, f
        elif isinstance(f, Snce):
            if f not in label:
                continue
            lo = _scan_backward_bound(lasso, t)
            found = False
            for s in range(t - 1, lo - 1, -1):
                if f.event in lasso.label(s):
                    if all(f.guard in lasso.label(r) for r in range(s + 1, t)):
                        found = True
                        break
            if not found:
                return False, f
    return True, None


def _box_faithful(
    closure: FrozenSet[Formula], family: "WitnessFamily"
) -> Tuple[bool, Optional[Formula]]:
    """(C3) `BoxFaithful`, over every lasso's one-period `_box_window`."""
    for f in closure:
        if not isinstance(f, Box):
            continue
        guess = family.bx_of(f.child)
        actual = all(
            f.child in lasso.label(t) for lasso in family.lassos for t in _box_window(lasso)
        )
        if guess != actual:
            return False, f
    return True, None


def _target_holds(
    family: "WitnessFamily", premises: List[Formula], conclusions: List[Formula], t: int
) -> bool:
    """(C4) `Target`, read on the main lasso only."""
    label0 = family.main.label(t)
    return all(p in label0 for p in premises) and all(c not in label0 for c in conclusions)


def recheck(
    family: "WitnessFamily",
    premises: Iterable[Formula],
    conclusions: Iterable[Formula],
    target_time: int,
) -> Dict[str, object]:
    """Independently re-check `family` against `premises`/`conclusions`/`target_time`.

    Returns `{"status": "countermodel", "time": target_time}` if all four conditions hold, or
    `{"status": "rejected", "failed": [...]}` naming the first violation found (structural, then
    local coherence, then fulfilment, then box faithfulness, then the target -- matching the
    order `check_certificate` documents its checks in).
    """
    premises = list(premises)
    conclusions = list(conclusions)
    closure = closure_of(premises + conclusions)

    # Structural: every label must lie within closureOf(premises ++ conclusions)
    # (LabelledLasso.label_sub), and no label may carry a fresh-indexed atom.
    for i, lasso in enumerate(family.lassos):
        stray = lasso.all_labels() - closure
        if stray:
            return _failed(
                "structural",
                i,
                None,
                next(iter(stray)),
                "label formula is not in closureOf(premises ++ conclusions)",
            )
        for label_formula in lasso.all_labels():
            if _has_fresh_atom(label_formula):
                return _failed(
                    "structural",
                    i,
                    None,
                    label_formula,
                    "label carries a fresh-indexed atom, which cannot be checked against a "
                    "Lean-side certificate (Atom.freshIndex is dropped on export)",
                )

    # (C1) local coherence, over the wide (proved) window.
    for i, lasso in enumerate(family.lassos):
        for t in _coherence_window(lasso):
            ok, f = _coherent_at(closure, family, lasso, t)
            if not ok:
                return _failed(
                    "local_coherent", i, t, f, "local coherence fixpoint fails at this position"
                )

    # (C2) fulfilment, over the same wide window.
    for i, lasso in enumerate(family.lassos):
        for t in _coherence_window(lasso):
            ok, f = _fulfil_at(closure, lasso, t)
            if not ok:
                return _failed(
                    "fulfilling", i, t, f, "this eventuality is never discharged within the scan bound"
                )

    # (C3) box faithfulness, over the narrower one-period window.
    ok, f = _box_faithful(closure, family)
    if not ok:
        return _failed(
            "box_faithful", None, None, f, "box guess disagrees with global label membership"
        )

    # (C4) target.
    if not _target_holds(family, premises, conclusions, target_time):
        return _failed(
            "target",
            0,
            target_time,
            None,
            "premises not all present, or a conclusion present, at the target position",
        )

    return {"status": "countermodel", "time": target_time}
