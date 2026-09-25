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
from typing import Dict, FrozenSet, Iterable, List, Mapping, Tuple

from .formula import Formula, to_json

__all__ = ["LabelledLasso", "WitnessFamily"]


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
