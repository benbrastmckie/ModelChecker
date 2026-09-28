"""Pins, as a machine-checked fact, that the certificate search is not monotone in
`back`/`fwd`: `WitnessRegistry.wrap()` folds a position `t < 0` to slot `t % back` (and
symmetrically `fwd` on the far side), so a back-period-`p` premise chain is representable at a
given `back` **exactly when `p` divides `back`** (see `test_witness_registry.py`'s
`TestWrapFoldsByExactPeriod` for the unit-level pin of the same arithmetic). A formula built
from such a chain can therefore be SAT at one `back` and genuinely UNSAT -- not merely
inconclusive -- at a larger `back`, which is the opposite of what "raising the search bound"
would suggest. `docs/SEARCH_COVERAGE.md` records the decision this fact motivates (the recommended
route, the two routes declined, and the staged path); this module is the regression pin that
decision was measured against, not a restatement of it.

**What this module does and does not establish.** It pins the search *as configured today* --
this is not an encoding-completeness defect (ADEQUACY.md section 7.3's sense): the encoder
faithfully encodes the family of labels at the segment lengths it is given, and the periodicity
those lengths impose is exactly what the module docstring of `witness_registry.py` documents. It
is, instead, the fact that any future change adopting the recommended sweep
(`docs/SEARCH_COVERAGE.md`'s decision) would *change* -- a sweep over `back' in [1, back]` would
make the searched space monotone, and every assertion below would need to become "SAT at every
point" rather than the alternating pattern pinned here.

**Measurement protocol (Scope Hypothesis, plan-format.md).** The two premise chains and the five
grid points below were carried over as a hypothesis from a prior report's prose, not a fact, and
were re-measured directly before writing any assertion (per this phase's plan). Observed verdicts,
all reproducing the report exactly, `timeout` false at every point, wall clock via
`time.perf_counter()` around each `_build` call:

    period3 back=2 mid=1 fwd=2 status=False timeout=False time=0.0598s
    period3 back=3 mid=1 fwd=3 status=True  timeout=False time=0.0701s
    period3 back=4 mid=1 fwd=4 status=False timeout=False time=0.1009s
    period3 back=5 mid=1 fwd=5 status=False timeout=False time=0.1333s
    period3 back=6 mid=1 fwd=6 status=True  timeout=False time=0.2045s
    period2 back=2 mid=1 fwd=2 status=True  timeout=False time=0.0179s
    period2 back=3 mid=1 fwd=3 status=False timeout=False time=0.0343s
    period2 back=4 mid=1 fwd=4 status=True  timeout=False time=0.0599s
    period2 back=5 mid=1 fwd=5 status=True  timeout=False time=0.0948s
    period2 back=6 mid=1 fwd=6 status=True  timeout=False time=0.1432s

Total wall clock for all ten builds: ~0.92s -- well under the ~2s per-point budget this task's
plan sets, so no point is `slow`-marked.

Why the pattern is forced, not a Z3 coincidence: `wrap` maps `t < 0` to `t % back`, so two
premise-pinned positions collide into the same slot exactly when they are a multiple of `back`
apart. A collision between two positions the chain pins to *different* truth values (`A` at one,
`\\neg A` at the other) makes the conjunction of premises unsatisfiable by direct label conflict,
independent of anything else in the closure -- this is why the UNSAT points below are genuine
rather than merely a solver timeout, and `timeout` is asserted `False` at every point to make that
distinction machine-checked rather than assumed.

**Direction claim.** These grid pins are liveness and regression evidence for the search's
*coverage* -- the UNSAT/A2 direction -- never for countermodel trust. They defend a claim about
which families the search can represent before any solve happens, not a claim about a reported
countermodel (which item 1's output gate, `semantic/checker.py`, independently checks per run
instead); there is nothing to independently re-verify about a period the search never had the
chance to represent. See `docs/SEARCH_COVERAGE.md` section 1's own direction claim and
`docs/TRUST_PIPELINE.md`'s "The standing test for A2" for the same reasoning applied to this
module's sibling."""

from __future__ import annotations

import pytest

from model_checker.theory_lib.bimodal.tests._build_support import _build

# Local to the property this module pins -- the search's non-monotonicity in `back`/`fwd` --
# and deliberately not merged with `test_certificate_a2_triangle.py`'s A2-triangle grid or
# `test_structure.py`'s `_A0_SWEPT_GRID`, each of which pins an independent property over its
# own premises/conclusions and grid points (implementation plan Phase 2, declined route F2).
_GRID = [(2, 1, 2), (3, 1, 3), (4, 1, 4), (5, 1, 5), (6, 1, 6)]


def _prev_chain(depth: int, atom: str) -> str:
    """`\\prev` applied `depth` times to `atom`, unary operators chained directly onto their
    argument with no extra parentheses (`examples.py`'s convention, e.g. `'\\Future \\past A'`).
    `\\prev X` is true at `t` iff `X` held at `t - 1`, so this pins `atom`'s truth value at
    position `-depth` relative to the search's target time (position `0`)."""
    formula = atom
    for _ in range(depth):
        formula = f"\\prev {formula}"
    return formula


def _period_chain(pattern: List[str]) -> List[str]:
    """One premise per entry of `pattern` (each `"A"` or `"\\neg A"`), pinning `pattern[0]` at
    position `-1`, `pattern[1]` at position `-2`, and so on -- a premise list whose positions
    repeat with period `len(pattern)` if extended indefinitely, though only the listed positions
    are actually pinned."""
    return [_prev_chain(depth, atom) for depth, atom in enumerate(pattern, start=1)]


# Period-3: A, not-A, not-A, A, not-A, not-A at positions -1..-6. Representable without a
# forced slot conflict exactly when 3 divides `back` -- true at back=3 and back=6 in the grid,
# false at back=2, 4, 5.
_PERIOD_3_PREMISES = _period_chain(["A", "\\neg A", "\\neg A", "A", "\\neg A", "\\neg A"])

# Period-2 (the counterpart direction): A, not-A, A, not-A at positions -1..-4. Representable
# without a forced conflict exactly when 2 divides `back` -- true at back=2, 4, and 6 in the
# grid (all pin only 4 of 6 positions, so back=5's 4-slot window also has no collision), false
# at back=3.
_PERIOD_2_PREMISES = _period_chain(["A", "\\neg A", "A", "\\neg A"])


class TestPeriodThreeChainNonMonotoneInBack:
    """SAT at (3,1,3) and (6,1,6) -- `back` a multiple of the chain's period-3 -- genuinely
    UNSAT at (2,1,2), (4,1,4) and (5,1,5), where it is not."""

    @pytest.mark.parametrize(
        "back,mid,fwd,expected_sat",
        [(b, m, f, (b % 3 == 0)) for b, m, f in _GRID],
    )
    def test_grid_point_matches_the_divisibility_pattern(self, back, mid, fwd, expected_sat):
        structure = _build(_PERIOD_3_PREMISES, [], back=back, mid=mid, fwd=fwd)
        assert structure.z3_model_status is expected_sat
        # Never let an inconclusive solver run (UNKNOWN, mapped to status=False with
        # timeout=True by `models/structure.py`) masquerade as a genuine UNSAT verdict.
        assert structure.timeout is False


class TestPeriodTwoChainIsTheCounterpartDirection:
    """SAT at (2,1,2), genuinely UNSAT at (3,1,3) -- the same non-monotonicity from the other
    side, so the phenomenon is not an artifact of one lucky formula. (4,1,4), (5,1,5) and
    (6,1,6) are also SAT here: this shorter, 4-position chain has no forced slot collision at
    any `back >= 4` regardless of divisibility, since there are only 4 pinned positions to
    collide."""

    @pytest.mark.parametrize(
        "back,mid,fwd,expected_sat",
        [(2, 1, 2, True), (3, 1, 3, False), (4, 1, 4, True), (5, 1, 5, True), (6, 1, 6, True)],
    )
    def test_grid_point_matches_the_measured_pattern(self, back, mid, fwd, expected_sat):
        structure = _build(_PERIOD_2_PREMISES, [], back=back, mid=mid, fwd=fwd)
        assert structure.z3_model_status is expected_sat
        assert structure.timeout is False
