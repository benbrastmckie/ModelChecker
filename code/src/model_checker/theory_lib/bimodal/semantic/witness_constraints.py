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

## Why one representative position per slot suffices

`WitnessRegistry.bit(lasso, t, formula)` already collapses every position `t` to its slot's
variable (`wrap`, `witness_registry.py`): `bit(lasso, t, f)` and `bit(lasso, t', f)` are the
*identical* Z3 term whenever `t` and `t'` share a slot, by construction, not merely equal under
every model. So a biconditional written using `bit(lasso, t, f)`, `bit(lasso, t+1, ...)` and
`bit(lasso, t-1, ...)` denotes the *same* Z3 constraint for every `t` sharing a slot as it does
for one representative -- enumerating `registry.target_window()` (one representative position per
slot) therefore asserts local coherence at *every* integer position, not just the ones visited.
This is a plain fact about Z3 term identity, and is a different (simpler) argument from why the
pure-Python re-checker (`certificate.py`) needs the *wide*, two-period window
(`coherent_iff_window`/`fulfil_iff_window`, `docs/ADEQUACY.md` section 5): the re-checker decodes
concrete labels pointwise and has no notion of "the same variable" to lean on, so it needs the
Lean-proved window to guarantee it has exercised the periodic region widely enough. The encoder
needs no such margin because the sharing is definitional, not empirical.

**This does not extend to fulfilment (part 2, below).** Fulfilment's witness scan bound
(`scan_forward`/`scan_backward`) is itself a function of `t`, not just of `t`'s slot, so the
one-representative-per-slot shortcut above is unsound for it: fulfilment is generated over the
*wide* `_coherence_window`, identical to the re-checker's, imported directly from
`certificate.py` rather than redefined (see part 2's docstring).

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
        """The `LocalCoherentLab` biconditionals for `lasso`, over every closure member and one
        representative position per slot (see the module docstring for why that suffices)."""
        registry = self.registry
        constraints: List["z3.BoolRef"] = []
        for t in registry.target_window():
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
        """The one-hot target-position selector for position `t` on the main lasso, memoized."""
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
        `sel[t] -> conclusion not in label(t)`, for every `t` in the window."""
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
