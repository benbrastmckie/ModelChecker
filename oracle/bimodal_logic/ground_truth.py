"""bimodal_logic.ground_truth - Independent brute-force ground-truth evaluator.

A THIRD, independent implementation of strict-future Until / strict-past
Since truth conditions over an unbounded integer time line, deliberately not
reusing either MC's or BH's own Z3 encoding. Supports the 5 primitive
temporal-only tags: atom, bot, imp, untl, snce.

Correctness contract: this module is a decision procedure for the truly
*unbounded*-time semantics only insofar as widening its brute-force window
does not move the verdict -- and that property is *enforced*, not assumed,
by `TestWindowStability` in `tests/test_ground_truth.py`, which checks every
temporal-only formula at complexity<=5 for verdict stability across windows
`depth+2`, `depth+3`, `depth+4`. Nothing in this repository should trust a
verdict from this module until that test is green.

History: the first version of this evaluator (built during the research that
led to this module) had an off-by-one error in the Until guard-interval
bound (`range(t, tp)` instead of the correct `range(t + 1, tp)`), which
produced a false SAT verdict that happened to agree with BimodalHarness's
(wrong) verdict on one of the 12 formulas this module now confirms UNSAT.
Caught by cross-checking against `UntilOperator`'s own docstring ("Guard
does NOT need to hold at time t") before trusting the tool's output. The fix
is preserved below with its explanation attached directly to the code it
corrects, not just in this history note.

Measured wall clock: the fast (non-`slow`) test class in
tests/test_ground_truth.py runs in well under a second; the window-stability
sweep over all 158 temporal-only formulas at complexity<=5 (3 windows each)
is marked `@pytest.mark.slow` -- see that test's own printed timing.

CLI usage:
    python -m bimodal_logic.ground_truth '<formula-json>'
    python -m bimodal_logic.ground_truth '<formula-json>' --window 6
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from typing import Optional

from .translation import temporal_depth

##############################################################################
# Exceptions
##############################################################################


class GroundTruthUnsupported(ValueError):
    """Raised when a formula uses a JSON tag this evaluator does not
    directly implement.

    Only the 5 primitive temporal-only tags (atom, bot, imp, untl, snce) are
    supported. box (modal accessibility) and all 11 enriched tags (top,
    neg, and, or, diamond, next, prev, some_future, some_past, all_future,
    all_past) are out of scope -- this is a dedicated exception, not a bare
    ValueError, so callers can distinguish "cannot adjudicate this formula"
    from a malformed-input error and route it to `unclassified` rather than
    crashing or silently returning a wrong answer.
    """


_SUPPORTED_TAGS = frozenset({"atom", "bot", "imp", "untl", "snce"})


##############################################################################
# Internal evaluation
##############################################################################


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
    raise GroundTruthUnsupported(
        f"ground_truth evaluator does not support tag {tag!r}; "
        f"supported tags are {sorted(_SUPPORTED_TAGS)}"
    )


def _eval(f: dict, val: dict[str, dict[int, bool]], t: int, window: int) -> bool:
    """Evaluate formula f at time t under valuation val (atom -> {time: bool}).

    Times outside [-window, window] are never queried for the formula
    populations this module is exercised against, given a comfortably large
    window, but the range bounds below guard defensively regardless.
    """
    tag = f["tag"]
    if tag == "atom":
        return val[f["name"]][t]
    if tag == "bot":
        return False
    if tag == "imp":
        return (not _eval(f["left"], val, t, window)) or _eval(f["right"], val, t, window)
    if tag == "untl":
        # Strict future: exists t' > t (t' <= window) with event(t') and
        # guard holding on all t'' in the OPEN interval (t, t') -- i.e.
        # {t+1, ..., t'-1}, excluding both endpoints. The guard range is
        # `range(t + 1, tp)`, NOT `range(t, tp)`: including t itself would
        # incorrectly require the guard to hold at the evaluation time,
        # making this spuriously fail for constant-False guards and
        # producing wrong SAT verdicts (this was a real bug in an earlier
        # version of this module -- see module docstring). UntilOperator's
        # own docstring is explicit: "Guard does NOT need to hold at time t".
        for tp in range(t + 1, window + 1):
            if not _eval(f["event"], val, tp, window):
                continue
            if all(_eval(f["guard"], val, tpp, window) for tpp in range(t + 1, tp)):
                return True
        return False
    if tag == "snce":
        # Strict past: exists t' < t (t' >= -window) with event(t') and
        # guard holding on all t'' in the open interval (t', t).
        for tp in range(t - 1, -window - 1, -1):
            if not _eval(f["event"], val, tp, window):
                continue
            if all(_eval(f["guard"], val, tpp, window) for tpp in range(tp + 1, t)):
                return True
        return False
    raise GroundTruthUnsupported(
        f"ground_truth evaluator does not support tag {tag!r}; "
        f"supported tags are {sorted(_SUPPORTED_TAGS)}"
    )


##############################################################################
# Public API
##############################################################################


def default_window(formula_json: dict) -> int:
    """Return the default brute-force window for a formula: derived from its
    temporal depth, never hard-coded, and always at least depth+2.

    `max(temporal_depth(formula_json) + 2, 4)` -- the +2 mirrors MC's own
    boundary-safety margin (see translation.temporal_depth's docstring), and
    the floor of 4 keeps small/depth-0 formulas comfortably wide (this
    evaluator's window is a brute-force search radius, not a solve budget,
    so a larger-than-strictly-necessary floor costs little and buys margin).
    """
    return max(temporal_depth(formula_json) + 2, 4)


def ground_truth_verdict(
    formula_json: dict, window: Optional[int] = None
) -> tuple[str, dict | None]:
    """Return ("SAT", witness_valuation) if a countermodel exists (formula is
    genuinely invalid), or ("UNSAT", None) if the formula is genuinely valid,
    by brute-force search over all boolean valuations of its atoms across
    [-window, window].

    Args:
        formula_json: A JSON formula dict using only the 5 primitive
            temporal-only tags (atom, bot, imp, untl, snce).
        window: Brute-force search radius. Defaults to `default_window`
            (formula-derived, never hard-coded) when None.

    Returns:
        A ("SAT", witness) or ("UNSAT", None) tuple. `witness` restricts the
        full valuation to times within 3 steps of 0, for readability.

    Raises:
        GroundTruthUnsupported: if the formula (or any subformula) uses a
            tag outside {atom, bot, imp, untl, snce}.
    """
    if window is None:
        window = default_window(formula_json)

    atoms = sorted(_collect_atoms(formula_json))
    times = range(-window, window + 1)
    if not atoms:
        # No atoms (only bot/imp over bot, or vacuous untl/snce) -- a single
        # valuation suffices.
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


##############################################################################
# CLI entry point (mirrors bimodal_logic.cli's shape)
##############################################################################


def main(argv: Optional[list[str]] = None) -> None:
    """Main entry point for `python -m bimodal_logic.ground_truth`.

    Args:
        argv: Command line arguments. Defaults to sys.argv[1:] when None.
              Pass an explicit list for testability.
    """
    parser = argparse.ArgumentParser(
        prog="bimodal_logic.ground_truth",
        description=(
            "Independent brute-force ground-truth decision procedure for "
            "temporal-only bimodal formulas."
        ),
    )
    parser.add_argument(
        "formula_json",
        type=str,
        help='Formula as a JSON string (dict with "tag" key)',
    )
    parser.add_argument(
        "--window",
        type=int,
        default=None,
        metavar="W",
        help="Brute-force search radius (default: formula-derived)",
    )

    args = parser.parse_args(argv)

    try:
        formula = json.loads(args.formula_json)
    except json.JSONDecodeError as e:
        print(f"Error: invalid JSON formula: {e}", file=sys.stderr)
        sys.exit(1)

    try:
        verdict, witness = ground_truth_verdict(formula, window=args.window)
    except GroundTruthUnsupported as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    print(json.dumps({"verdict": verdict, "witness": witness}))
    sys.exit(0)


if __name__ == "__main__":
    main()
