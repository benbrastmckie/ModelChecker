"""Independent brute-force ground-truth evaluator for temporal-only bimodal
formulas (atom, bot, imp, untl, snce), used to hand-check which of the two
oracles (MC / BH) is semantically correct on the 13 resolved-and-wrong
disagreements at complexity<=5.

This is a THIRD, independent implementation of strict-future Until / strict-
past Since truth conditions over an UNBOUNDED integer time line (matching the
textbook temporal-logic semantics and matching the Lean BimodalLogic spec's
unbounded `Int` time domain per oracle/bimodal_logic/provider.py's module
docstring), deliberately not reusing either MC's or BH's own Z3 encoding.

Method: a formula of complexity<=5 has temporal depth <= 2, so its truth
value at time 0 can only depend on atom valuations within a small window
around 0. We brute-force every boolean valuation of each atom over a window
[-W, W] (W chosen comfortably larger than the formula's depth) and directly
evaluate untl/snce via their strict semantics. If SOME valuation makes the
formula false at t=0, the formula is genuinely INVALID (oracle should return
SAT / a countermodel). If EVERY valuation makes it true at t=0, the formula
is genuinely VALID (oracle should return UNSAT / None) -- because widening W
further cannot change the answer once W comfortably exceeds the formula's
temporal depth (the truth value at t=0 cannot "see" past its recursive
lookahead/lookbehind).
"""
from __future__ import annotations

import itertools
from typing import Callable


def _collect_atoms(f: dict) -> set[str]:
    tag = f["tag"]
    if tag == "atom":
        return {f["name"]}
    if tag == "bot":
        return set()
    if tag == "imp":
        return _collect_atoms(f["left"]) | _collect_atoms(f["right"])
    if tag in ("untl", "snce"):
        return _collect_atoms(f["event"]) | _collect_atoms(f["guard"])
    raise ValueError(f"unknown tag {tag!r}")


def _eval(f: dict, val: dict[str, dict[int, bool]], t: int, window: int) -> bool:
    """Evaluate formula f at time t under valuation val (atom -> {time: bool}).

    Times outside [-window, window] are never queried for complexity<=5
    formulas given a comfortably large window, but we guard defensively.
    """
    tag = f["tag"]
    if tag == "atom":
        return val[f["name"]][t]
    if tag == "bot":
        return False
    if tag == "imp":
        return (not _eval(f["left"], val, t, window)) or _eval(f["right"], val, t, window)
    if tag == "untl":
        # strict future: exists t' > t (t' <= window) with event(t') and
        # guard holding on all t'' in the OPEN interval (t, t') -- i.e.
        # {t+1, ..., t'-1}, excluding both endpoints. Fixed: was previously
        # `range(t, tp)`, which incorrectly included t itself (the
        # evaluation time), making the guard clause spuriously fail for
        # constant-False guards and producing wrong SAT verdicts. See
        # UntilOperator docstring in bimodal/operators.py: "Guard does NOT
        # need to hold at time t" / "Current time excluded".
        for tp in range(t + 1, window + 1):
            if not _eval(f["event"], val, tp, window):
                continue
            if all(_eval(f["guard"], val, tpp, window) for tpp in range(t + 1, tp)):
                return True
        return False
    if tag == "snce":
        # strict past: exists t' < t (t' >= -window) with event(t') and
        # guard holding on all t'' in (t', t)
        for tp in range(t - 1, -window - 1, -1):
            if not _eval(f["event"], val, tp, window):
                continue
            if all(_eval(f["guard"], val, tpp, window) for tpp in range(tp + 1, t)):
                return True
        return False
    raise ValueError(f"unknown tag {tag!r}")


def ground_truth_verdict(formula_json: dict, window: int = 8) -> tuple[str, dict | None]:
    """Return ("SAT", witness_valuation) if a countermodel exists (formula is
    genuinely invalid), or ("UNSAT", None) if the formula is genuinely valid,
    by brute-force search over all boolean valuations of its atoms across
    [-window, window].

    A `window` of 8 is far more than enough for any complexity<=5 formula
    (temporal depth <= 2): a formula's truth at t=0 can only depend on atom
    values within `depth` steps of 0, so widening the window past depth+1
    cannot change the verdict -- this makes the brute force a decision
    procedure for the true *unbounded*-time semantics, not just a bounded
    approximation.
    """
    atoms = sorted(_collect_atoms(formula_json))
    times = range(-window, window + 1)
    if not atoms:
        # No atoms (only bot/imp/untl/snce over bot) -- single valuation.
        val: dict[str, dict[int, bool]] = {}
        result = _eval(formula_json, val, 0, window)
        return ("UNSAT", None) if result else ("SAT", {})

    for bits in itertools.product([False, True], repeat=len(atoms) * len(list(times))):
        val = {}
        idx = 0
        for a in atoms:
            val[a] = {}
            for t in times:
                val[a][t] = bits[idx]
                idx += 1
        if not _eval(formula_json, val, 0, window):
            witness = {a: {t: v for t, v in val[a].items() if abs(t) <= 3} for a in atoms}
            return "SAT", witness
    return "UNSAT", None
