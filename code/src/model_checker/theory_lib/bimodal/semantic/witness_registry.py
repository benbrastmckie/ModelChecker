"""The Z3 variable layer for witness-family certificate search.

**Change of meaning.** This module previously implemented `WitnessRegistry` for the retired
window-and-abundance encoding: a table of `accessible_world` witness predicates, one per modal
formula, each a `(Int, Int) -> Int` Z3 function. That encoding is being replaced outright (see
`docs/ADEQUACY.md` and the implementation plan's decision D1), and `WitnessRegistry` is rewritten
to the certificate encoding's own variable layer rather than deleted (report 01 section 4.4: "the
currently inert `WitnessRegistry` ... should be rewritten rather than deleted") -- there is no
relationship between the old and new class bodies beyond the shared name.

**What this registry now does.** A certificate's search variables are exactly:

- One Boolean per (lasso, position slot, closure formula) -- "does this closure formula belong to
  the label at this slot of this lasso" -- via `bit`.
- One Boolean per boxed subformula in the closure -- the box guess `bx(chi)` -- via `guess`.
- A lasso-index allocation for each boxed subformula's witness lasso (needed only when its guess
  is false), via `allocate_witness_lasso`.

All three are quantifier-free: `back`, `mid`, `fwd` (the fixed segment lengths for this search,
matching `LabelledLasso`'s `nb`/`nm`/`nf`) and the closure are fixed at construction, so the
variable set is a finite, statically-known table -- no `ForAll`/`Exists`, no MBQI, no E-matching
pattern.

## Position slots and `wrap`

A lasso's label is periodic by construction (`LabelledLasso.label`, `certificate.py`): strictly
negative positions repeat `back` cyclically, `[0, mid)` reads directly, and positions at or past
`mid` repeat `fwd` cyclically. So a single Boolean suffices per *slot*, not per position -- there
are only `back + mid + fwd` distinct slots, laid out as `[0, back)` for the back segment,
`[back, back+mid)` for mid, and `[back+mid, back+mid+fwd)` for fwd. `wrap(t)` maps any integer
position `t` to its slot, by exactly the same arithmetic `LabelledLasso.label` decodes with:

    t < 0        -> t % back                          (in [0, back))
    0 <= t < mid -> back + t                           (in [back, back+mid))
    t >= mid     -> back + mid + (t - mid) % fwd       (in [back+mid, back+mid+fwd))

This is what lets constraint generators (Phase 7/8) range a position `t` over an arbitrarily wide
window -- e.g. `certificate.py`'s two-period `_coherence_window` -- while only ever allocating
`back + mid + fwd` distinct Z3 variables per (lasso, formula) pair: multiple `t` values sharing a
slot share the same variable, automatically enforcing the periodicity a certificate's labels are
required to have.

## Witness lassos and sharing

`lassos[0]` is always the main lasso (index `0`). `allocate_witness_lasso(box_formula)` hands out
one additional lasso index per distinct boxed subformula the caller requests a witness for,
memoized so repeated requests for the same formula return the same index. The certificate
datatype's own docstring records that witness lassos *may* be shared (a single lasso can happen to
falsify more than one boxed subformula in the same satisfying assignment) but are never *required*
to be -- this registry's default behaviour is to allocate a fresh index per formula, so sharing (if
it occurs) is discovered by the solver, not imposed by the registry.

`max_witnesses`, if given, caps the number of *distinct* witness-lasso indices ever handed out:
once the cap is reached, further distinct formulas are assigned round-robin to already-allocated
indices, which *forces* sharing rather than merely permitting it. This trades completeness for a
bounded search (consistent with (ADEQ) being open and search-bound-relative to begin with, per
`docs/ADEQUACY.md` section 7) -- it never affects soundness, since a witness constraint generated
against a shared lasso is exactly as valid as one against a dedicated one.
"""

from __future__ import annotations

from typing import Dict, FrozenSet, Iterable, Optional, Tuple

from model_checker import z3_shim as z3

from model_checker.theory_lib.errors import WitnessRegistryError

from .certificate import _box_window
from .formula import Box, Formula

__all__ = ["WitnessRegistry"]


class WitnessRegistry:
    """The Z3 variable layer for one certificate search: label bits, box guesses, and witness-lasso
    allocation. See the module docstring for the change of meaning from the retired encoding."""

    def __init__(
        self,
        back: int,
        mid: int,
        fwd: int,
        closure: Iterable[Formula],
        max_witnesses: Optional[int] = None,
    ) -> None:
        if back < 1:
            raise WitnessRegistryError(
                f"back must be >= 1 (LabelledLasso.back_ne), got {back!r}",
                context={"back": back},
                suggestion="Use a positive back-segment length",
            )
        if fwd < 1:
            raise WitnessRegistryError(
                f"fwd must be >= 1 (LabelledLasso.fwd_ne), got {fwd!r}",
                context={"fwd": fwd},
                suggestion="Use a positive fwd-segment length",
            )
        if mid < 0:
            raise WitnessRegistryError(
                f"mid must be >= 0, got {mid!r}", context={"mid": mid}
            )
        if max_witnesses is not None and max_witnesses < 1:
            raise WitnessRegistryError(
                f"max_witnesses must be >= 1 when given, got {max_witnesses!r}",
                context={"max_witnesses": max_witnesses},
            )

        self.nb: int = back
        self.nm: int = mid
        self.nf: int = fwd
        self.closure: FrozenSet[Formula] = frozenset(closure)
        self.max_witnesses: Optional[int] = max_witnesses

        self._bits: Dict[Tuple[int, int, Formula], "z3.BoolRef"] = {}
        self._guesses: Dict[Formula, "z3.BoolRef"] = {}
        self._witness_lassos: Dict[Formula, int] = {}
        self._next_witness_index: int = 1  # 0 is reserved for the main lasso

    @property
    def slots_per_lasso(self) -> int:
        """The number of distinct position slots per lasso: `back + mid + fwd`."""
        return self.nb + self.nm + self.nf

    def wrap(self, t: int) -> int:
        """Map integer position `t` to its slot index in `[0, slots_per_lasso)`, agreeing with
        `LabelledLasso.label`'s decoding (see the module docstring)."""
        if t < 0:
            return t % self.nb
        if t < self.nm:
            return self.nb + t
        return self.nb + self.nm + ((t - self.nm) % self.nf)

    def bit(self, lasso: int, t: int, formula: Formula) -> "z3.BoolRef":
        """The Boolean for "`formula` is in the label at position `t` of `lasso`", memoized per
        (lasso, slot, formula) so that positions sharing a slot share the same variable."""
        index = self.wrap(t)
        key = (lasso, index, formula)
        cached = self._bits.get(key)
        if cached is not None:
            return cached
        var = z3.Bool(f"lab_{lasso}_{index}_{formula!r}")
        self._bits[key] = var
        return var

    def guess(self, formula: Formula) -> "z3.BoolRef":
        """The box-guess Boolean `bx(formula)`, memoized per formula (the guess is global, not
        per-lasso or per-position)."""
        cached = self._guesses.get(formula)
        if cached is not None:
            return cached
        var = z3.Bool(f"bx_{formula!r}")
        self._guesses[formula] = var
        return var

    def allocate_witness_lasso(self, box_formula: Formula) -> int:
        """Allocate (or return the already-allocated) witness-lasso index for `box_formula` (the
        argument of a `Box`, not the `Box` itself). See the module docstring's "Witness lassos and
        sharing" section for the `max_witnesses` round-robin behaviour."""
        cached = self._witness_lassos.get(box_formula)
        if cached is not None:
            return cached
        if self.max_witnesses is not None and len(self._witness_lassos) >= self.max_witnesses:
            index = 1 + (len(self._witness_lassos) % self.max_witnesses)
        else:
            index = self._next_witness_index
            self._next_witness_index += 1
        self._witness_lassos[box_formula] = index
        return index

    def target_window(self) -> range:
        """The position window used for the one-hot target selector (decision D5): one
        representative position per slot, `[-back, mid+fwd)`. Every slot is hit exactly once.

        Now the *shared* definition: identical to box faithfulness's proved `mem_all_iff_window`
        bound (`docs/ADEQUACY.md` section 5.2), reused here because the selector's own
        completeness argument (a lossless Skolemization of (C4)'s existential target time --
        `docs/ADEQUACY.md` section 7.3) requires exactly one representative position per slot,
        the identical requirement box faithfulness's proof establishes. Both uses independently
        require exactly `[-nb, nm+nf)`, so delegating to `certificate._box_window` is the
        technically correct outcome, not a mere convenience -- see that function's docstring and
        `certificate.py`'s four-window-helpers comment block for the shared-import rationale."""
        return _box_window(self)

    def clear(self) -> None:
        """Release every allocated Z3 variable and witness-lasso assignment, resetting the
        registry to its just-constructed state (segment lengths, closure and `max_witnesses` are
        unaffected)."""
        self._bits.clear()
        self._guesses.clear()
        self._witness_lassos.clear()
        self._next_witness_index = 1
