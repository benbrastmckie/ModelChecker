"""Quantifier-free Z3 constraint generators for the witness-family certificate search.

**Change of meaning.** This module previously implemented `WitnessConstraintGenerator` for the
retired window-and-abundance encoding: a `ForAll`-quantified constraint pinning down an
`accessible_world` witness function. That encoding is being replaced outright (see
`docs/ADEQUACY.md` and the implementation plan's decision D1), and `WitnessConstraintGenerator` is
rewritten to the certificate encoding's own constraint generators rather than deleted (report 01
section 4.4). There is no relationship between the old and new class bodies beyond the shared
name.

**What this generator now does (part 1 of 2).** Given a `WitnessRegistry` (the Z3 variable layer;
`witness_registry.py`), this class emits the quantifier-free constraint set for two of the four
certificate conditions:

- **(C1) Local coherence** (`local_coherence_constraints`): the five `LocalCoherentLab`
  biconditionals of `docs/ADEQUACY.md` section 1 -- bottom absent, `imp`/`box`/`untl`/`snce`
  fixpoint laws -- for every closure member, at every position slot of a given lasso.
- **(C4) Target** (`target_constraints`): the one-hot selector `sel[t]` over the main lasso's
  position window (decision D5), with exactly-one and the guarded premise/conclusion
  implications.

(C2) Fulfilment and (C3) Box faithfulness are the second half of the rewrite (a later phase).

## Why one representative position per slot is NOT enough (corrected)

An earlier version of this module asserted local coherence only over
`registry.target_window()` (one representative position per slot, `[-nb, nm+nf)` -- now the
shared `certificate._box_window` definition, see `witness_registry.py`), reasoning that
`WitnessRegistry.bit(lasso, t, formula)`'s slot-sharing (`wrap`, `witness_registry.py`) makes
`bit(lasso, t, f)` and `bit(lasso, t', f)` the *identical* Z3 term whenever `t` and `t'` share a
slot, so a clause written using one representative `t` would "automatically" hold for every other
`t'` sharing its slot. **That reasoning is false for the two slots adjacent to `mid`** (the last
`back` slot and the first `fwd` slot), and the fix here is to use the wide window like fulfilment
already did. The counterexample: with `nb=2`, slot `back[1]` occurs at every odd-magnitude
negative position `t = -1, -3, -5, ...` (all share the identical `bit(lasso, ., f)` term, by
`wrap`'s definition). But the *neighbour* an `Untl`/`Snce` clause at `t` needs is `bit(lasso, t+1,
.)` (or `t-1`), and `t+1`'s *slot* is NOT the same for every occurrence of `t`: at `t=-1`, `t+1=0`
lands in `mid`; at `t=-3, -5, ...`, `t+1` lands back in `back[0]` -- a different slot from `mid`,
in general holding a different truth value for the same formula. So the single shared boolean
`bit(lasso, back[1]-slot, f)` is subject to two genuinely different biconditionals (one pinned to
`mid`, one pinned to `back[0]`) depending on which position is being checked, and asserting only
the `t=-1` clause leaves the `t=-3` (and deeper) requirement completely unconstrained -- which is
exactly the defect this module shipped with: Z3 was free to pick `back[0]`/`back[1]` values that
satisfy the `t=-1` clause while violating local coherence at `t=-3`, and only the pure-Python
re-checker's *wide*-window scan (`certificate.py`'s `_coherence_window`, matching the Lean-proved
`coherent_iff_window` bound) caught it, exactly as the `docs/ADEQUACY.md` section 6.2 S3 fail-fast
guard is there for. **Fix**: `local_coherence_constraints` below asserts the biconditional at
*every* position in the wide window, identical in shape to `fulfilment_constraints`, so every
periodic occurrence of every slot -- not just the one closest to `mid` -- gets its own explicit
clause. This costs more Z3 atoms per position (still quantifier-free, still a fixed finite table
per search) but is the actual requirement the Lean development's window-collapse theorem
establishes, matching what the re-checker already independently verifies.

Fulfilment already used this same wide window and corrected scan bounds
(`scan_forward`/`scan_backward`, themselves functions of `t`, not just of `t`'s slot) from the
start (Phase 8), imported directly from `certificate.py` rather than redefined, so this module's
two constraint families are now consistent in window choice.

## Atoms are deliberately unconstrained

As in the re-checker, atoms carry no coherence clause: the valuation *is* the atom part of the
label (`docs/ADEQUACY.md` Lemma 4's atom case -- `M, tau_i, t |= p` iff `(i,t) in |p|` iff
`atom p in L_i(t)`, an identity, not an appeal to a clause). `bit(lasso, t, Atom(...))` is left
free for the solver to choose.
"""

from __future__ import annotations

from typing import Iterable, List

from model_checker import z3_shim as z3

from .certificate import _box_window, _coherence_window, _scan_backward_bound, _scan_forward_bound
from .formula import Atom, Bot, Box, Formula, Imp, Snce, Untl
from .witness_registry import WitnessRegistry

__all__ = ["WitnessConstraintGenerator"]


class WitnessConstraintGenerator:
    """Quantifier-free constraint generators for the certificate search, built against a
    `WitnessRegistry`. See the module docstring for the change of meaning from the retired
    encoding."""

    def __init__(self, registry: WitnessRegistry) -> None:
        self.registry = registry
        self._sel = {}

    # -----------------------------------------------------------------
    # (C1) Local coherence
    # -----------------------------------------------------------------

    def local_coherence_constraints(self, lasso: int) -> List["z3.BoolRef"]:
        """The `LocalCoherentLab` biconditionals for `lasso`, over every closure member and every
        position in the *wide* `_coherence_window` (see the module docstring's corrected
        rationale for why the narrower `registry.target_window()` is NOT enough)."""
        registry = self.registry
        constraints: List["z3.BoolRef"] = []
        for t in _coherence_window(registry):
            for f in registry.closure:
                constraints.extend(self._coherence_clause_at(lasso, t, f))
        return constraints

    def _coherence_clause_at(self, lasso: int, t: int, f: Formula) -> List["z3.BoolRef"]:
        registry = self.registry
        if isinstance(f, Atom):
            return []  # atoms are deliberately unconstrained (see module docstring)
        if isinstance(f, Bot):
            return [z3.Not(registry.bit(lasso, t, f))]
        if isinstance(f, Imp):
            lhs = registry.bit(lasso, t, f)
            rhs = z3.Or(z3.Not(registry.bit(lasso, t, f.left)), registry.bit(lasso, t, f.right))
            return [lhs == rhs]
        if isinstance(f, Box):
            lhs = registry.bit(lasso, t, f)
            rhs = registry.guess(f.child)
            return [lhs == rhs]
        if isinstance(f, Untl):
            lhs = registry.bit(lasso, t, f)
            next_event = registry.bit(lasso, t + 1, f.event)
            next_guard = registry.bit(lasso, t + 1, f.guard)
            next_self = registry.bit(lasso, t + 1, f)
            rhs = z3.Or(next_event, z3.And(next_guard, next_self))
            return [lhs == rhs]
        if isinstance(f, Snce):
            lhs = registry.bit(lasso, t, f)
            prev_event = registry.bit(lasso, t - 1, f.event)
            prev_guard = registry.bit(lasso, t - 1, f.guard)
            prev_self = registry.bit(lasso, t - 1, f)
            rhs = z3.Or(prev_event, z3.And(prev_guard, prev_self))
            return [lhs == rhs]
        raise TypeError(f"not a Formula: {f!r}")

    # -----------------------------------------------------------------
    # (C4) Target
    # -----------------------------------------------------------------

    def sel(self, t: int) -> "z3.BoolRef":
        """The one-hot target-position selector for position `t` on the main lasso, memoized.
        Conservative: see `target_constraints`'s docstring and `docs/ADEQUACY.md` section 7.3."""
        cached = self._sel.get(t)
        if cached is not None:
            return cached
        var = z3.Bool(f"sel_{t}")
        self._sel[t] = var
        return var

    def target_constraints(
        self, premises: Iterable[Formula], conclusions: Iterable[Formula]
    ) -> List["z3.BoolRef"]:
        """(C4): exactly-one over `sel` across the main lasso's position window, plus the guarded
        premise/conclusion implications of decision D5 -- `sel[t] -> premise in label(t)` and
        `sel[t] -> conclusion not in label(t)`, for every `t` in the window.

        The selector is structure (C1)-(C4) do not themselves contain, but it is conservative: it
        is a lossless Skolemization of (C4) `Target`'s existential target time, since the window
        (`registry.target_window()`, the shared `_box_window`) supplies exactly one
        representative position per slot and `LabelledLasso.label` is exactly periodic, so
        restricting `sel`'s domain to the window can discard only duplicate representations of an
        in-window target time, never a satisfying one. See `docs/ADEQUACY.md` section 7.3 for the
        full argument and `TestSelectorConservativity`
        (`tests/unit/test_witness_constraints.py`) for the pinning test."""
        window = list(self.registry.target_window())
        sels = [self.sel(t) for t in window]
        constraints: List["z3.BoolRef"] = [z3.Or(*sels), z3.AtMost(*sels, 1)]
        premises = list(premises)
        conclusions = list(conclusions)
        for t in window:
            s = self.sel(t)
            for p in premises:
                constraints.append(z3.Implies(s, self.registry.bit(0, t, p)))
            for c in conclusions:
                constraints.append(z3.Implies(s, z3.Not(self.registry.bit(0, t, c))))
        return constraints

    # -----------------------------------------------------------------
    # (C2) Fulfilment
    # -----------------------------------------------------------------
    #
    # Unlike local coherence, fulfilment is generated over the *wide*, two-period window
    # (`_coherence_window`) and the corrected scan bounds (`_scan_forward_bound`/
    # `_scan_backward_bound`), imported directly from `certificate.py` rather than redefined --
    # both duck-typed on `.nb`/`.nm`/`.nf`, which `WitnessRegistry` also carries (Phase 8: "factor
    # the fulfilment window computation into a single function shared with the re-checker"). See
    # the module docstring for why the one-representative-per-slot shortcut used above for local
    # coherence does *not* extend here: the scan bound is itself a function of `t`, not of `t`'s
    # slot alone.

    def fulfilment_constraints(self, lasso: int) -> List["z3.BoolRef"]:
        """The `FulfillingLab` obligations for `lasso`: every `untl`/`snce` closure member true at
        a position must have a later/earlier witness within the corrected scan bound, with the
        guard holding at every position strictly between."""
        registry = self.registry
        constraints: List["z3.BoolRef"] = []
        for t in _coherence_window(registry):
            for f in registry.closure:
                if isinstance(f, Untl):
                    hi = _scan_forward_bound(registry, t)
                    disjuncts = [
                        z3.And(
                            registry.bit(lasso, s, f.event),
                            *[registry.bit(lasso, r, f.guard) for r in range(t + 1, s)],
                        )
                        for s in range(t + 1, hi + 1)
                    ]
                    constraints.append(z3.Implies(registry.bit(lasso, t, f), z3.Or(*disjuncts)))
                elif isinstance(f, Snce):
                    lo = _scan_backward_bound(registry, t)
                    disjuncts = [
                        z3.And(
                            registry.bit(lasso, s, f.event),
                            *[registry.bit(lasso, r, f.guard) for r in range(s + 1, t)],
                        )
                        for s in range(t - 1, lo - 1, -1)
                    ]
                    constraints.append(z3.Implies(registry.bit(lasso, t, f), z3.Or(*disjuncts)))
        return constraints

    # -----------------------------------------------------------------
    # (C3) Box faithfulness
    # -----------------------------------------------------------------
    #
    # The narrower, one-period window (`_box_window`, imported from `certificate.py` -- amended
    # D7's distinct, narrower bound from fulfilment's wide window; see that function's docstring
    # and `docs/ADEQUACY.md` section 5.2's window table). Do not collapse the two windows into
    # one: box faithfulness reads no neighbouring positions, so it needs no margin beyond one
    # period, while fulfilment's neighbour-scanning does.

    def box_faithfulness_constraints(self, lassos: Iterable[int]) -> List["z3.BoolRef"]:
        """The `BoxFaithful` biconditional for every boxed closure member: `guess(chi)` implies
        `chi` is in every label of every lasso in `lassos`, over the narrow window; `Not(guess
        (chi))` implies some (lasso, position) pair in `lassos` omits `chi`. The caller is
        responsible for including, among `lassos`, any witness lasso allocated for a box guessed
        false (`WitnessRegistry.allocate_witness_lasso`) -- this generator only quantifies over
        the lassos it is given."""
        registry = self.registry
        lassos = list(lassos)
        window = list(_box_window(registry))
        constraints: List["z3.BoolRef"] = []
        for f in registry.closure:
            if not isinstance(f, Box):
                continue
            guess = registry.guess(f.child)
            everywhere = z3.And(
                *[registry.bit(i, t, f.child) for i in lassos for t in window]
            )
            somewhere_absent = z3.Or(
                *[z3.Not(registry.bit(i, t, f.child)) for i in lassos for t in window]
            )
            constraints.append(z3.Implies(guess, everywhere))
            constraints.append(z3.Implies(z3.Not(guess), somewhere_absent))
        return constraints
