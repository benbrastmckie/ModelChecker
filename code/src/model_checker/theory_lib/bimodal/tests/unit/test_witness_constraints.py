"""Unit tests for `WitnessConstraintGenerator`'s local-coherence and target generators.

Mirrors `docs/ADEQUACY.md` section 1's `LocalCoherentLab` and `Target`, and the certificate
re-checker's `_coherent_at`/`_target_holds` (`certificate.py`) -- the encoder and the re-checker
must agree on what "coherent" and "on target" mean, even though the encoder only ever visits one
representative position per slot (see `witness_constraints.py`'s module docstring for why that
suffices).
"""

from __future__ import annotations

import pytest
import z3

from model_checker.theory_lib.bimodal.semantic.formula import Atom, Bot, Box, Imp, Snce, Untl
from model_checker.theory_lib.bimodal.semantic.witness_constraints import (
    WitnessConstraintGenerator,
)
from model_checker.theory_lib.bimodal.semantic.witness_registry import WitnessRegistry

P = Atom("p")
Q = Atom("q")
BOX_P = Box(P)


def _contains_quantifier(expr) -> bool:
    """Recursively walk a Z3 AST looking for a `ForAll`/`Exists` node."""
    if z3.is_quantifier(expr):
        return True
    return any(_contains_quantifier(child) for child in expr.children())


class TestLocalCoherenceIsQuantifierFree:
    def test_no_quantifier_node_for_a_closure_with_every_connective(self):
        until = Untl(guard=P, event=Q)
        since = Snce(guard=P, event=Q)
        closure = [P, Q, Bot(), Imp(P, Q), BOX_P, until, since]
        registry = WitnessRegistry(back=2, mid=2, fwd=2, closure=closure)
        generator = WitnessConstraintGenerator(registry)
        constraints = generator.local_coherence_constraints(lasso=0)
        assert constraints, "expected at least one constraint"
        for constraint in constraints:
            assert not _contains_quantifier(constraint)

    def test_target_constraints_are_quantifier_free(self):
        registry = WitnessRegistry(back=2, mid=2, fwd=2, closure=[P, Q])
        generator = WitnessConstraintGenerator(registry)
        constraints = generator.target_constraints(premises=[P], conclusions=[Q])
        assert constraints
        for constraint in constraints:
            assert not _contains_quantifier(constraint)


class TestLocalCoherenceDiscrimination:
    """A hand-built satisfying assignment must be SAT together with the generated constraints;
    a hand-built incoherent one must be UNSAT."""

    def build(self):
        closure = [P, BOX_P]
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=closure)
        generator = WitnessConstraintGenerator(registry)
        constraints = generator.local_coherence_constraints(lasso=0)
        return registry, generator, constraints

    def test_coherent_assignment_is_sat(self):
        registry, _, constraints = self.build()
        solver = z3.Solver()
        solver.add(*constraints)
        # box_p's guess agrees with its label membership at every position (all positions share
        # one slot each since back=mid=fwd=1): guess(p) True, box_p present everywhere.
        solver.add(registry.guess(P) == True)
        for t in (-1, 0, 1):
            solver.add(registry.bit(0, t, BOX_P) == True)
        assert solver.check() == z3.sat

    def test_incoherent_assignment_is_unsat(self):
        """`bx(p) = False` but the label carries `Box(p)` anyway -- violates the box
        biconditional (mirrors `TestRecheckLocalCoherentFailure` in `test_certificate.py`)."""
        registry, _, constraints = self.build()
        solver = z3.Solver()
        solver.add(*constraints)
        solver.add(registry.guess(P) == False)
        solver.add(registry.bit(0, 0, BOX_P) == True)
        assert solver.check() == z3.unsat

    def test_bot_is_never_satisfiable_in_a_label(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[Bot()])
        generator = WitnessConstraintGenerator(registry)
        constraints = generator.local_coherence_constraints(lasso=0)
        solver = z3.Solver()
        solver.add(*constraints)
        solver.add(registry.bit(0, 0, Bot()) == True)
        assert solver.check() == z3.unsat

    def test_until_unfolding_is_enforced(self):
        """`(p U q)` at `t` must agree with `q@(t+1) or (p@(t+1) and (p U q)@(t+1))` -- forcing
        the until bit true while both disjuncts are false must be UNSAT."""
        until = Untl(guard=P, event=Q)
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P, Q, until])
        generator = WitnessConstraintGenerator(registry)
        constraints = generator.local_coherence_constraints(lasso=0)
        solver = z3.Solver()
        solver.add(*constraints)
        solver.add(registry.bit(0, 0, until) == True)
        solver.add(registry.bit(0, 1, Q) == False)
        solver.add(registry.bit(0, 1, P) == False)
        assert solver.check() == z3.unsat


class TestTargetConstraints:
    def test_exactly_one_selector_is_satisfiable(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P])
        generator = WitnessConstraintGenerator(registry)
        constraints = generator.target_constraints(premises=[], conclusions=[])
        solver = z3.Solver()
        solver.add(*constraints)
        assert solver.check() == z3.sat

    def test_two_selectors_true_is_unsat(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P])
        generator = WitnessConstraintGenerator(registry)
        constraints = generator.target_constraints(premises=[], conclusions=[])
        solver = z3.Solver()
        solver.add(*constraints)
        window = list(registry.target_window())
        solver.add(generator.sel(window[0]) == True)
        solver.add(generator.sel(window[1]) == True)
        assert solver.check() == z3.unsat

    def test_no_selector_true_is_unsat(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P])
        generator = WitnessConstraintGenerator(registry)
        constraints = generator.target_constraints(premises=[], conclusions=[])
        solver = z3.Solver()
        solver.add(*constraints)
        for t in registry.target_window():
            solver.add(generator.sel(t) == False)
        assert solver.check() == z3.unsat

    def test_selected_position_must_carry_every_premise(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P])
        generator = WitnessConstraintGenerator(registry)
        constraints = generator.target_constraints(premises=[P], conclusions=[])
        solver = z3.Solver()
        solver.add(*constraints)
        t0 = list(registry.target_window())[0]
        solver.add(generator.sel(t0) == True)
        solver.add(registry.bit(0, t0, P) == False)
        assert solver.check() == z3.unsat

    def test_selected_position_must_not_carry_any_conclusion(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P])
        generator = WitnessConstraintGenerator(registry)
        constraints = generator.target_constraints(premises=[], conclusions=[P])
        solver = z3.Solver()
        solver.add(*constraints)
        t0 = list(registry.target_window())[0]
        solver.add(generator.sel(t0) == True)
        solver.add(registry.bit(0, t0, P) == True)
        assert solver.check() == z3.unsat

    def test_unselected_positions_are_unconstrained_by_target(self):
        """A premise absent at a non-selected position must not, by itself, force UNSAT."""
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P])
        generator = WitnessConstraintGenerator(registry)
        constraints = generator.target_constraints(premises=[P], conclusions=[])
        solver = z3.Solver()
        solver.add(*constraints)
        window = list(registry.target_window())
        solver.add(generator.sel(window[0]) == True)
        solver.add(registry.bit(0, window[0], P) == True)  # satisfy the selected position
        solver.add(registry.bit(0, window[1], P) == False)  # unselected: unconstrained
        assert solver.check() == z3.sat


# ---------------------------------------------------------------------------
# Selector conservativity: sel[t] against the re-checker's _target_holds
# ---------------------------------------------------------------------------
#
# `TestTargetConstraints` above spot-checks individual clauses; it never cross-checks a full
# `target_constraints()` assertion against the re-checker's own `_target_holds`, and never
# isolates the selector from (C1)-(C3). This section closes that gap: it establishes F1's
# conservativity equivalence directly, with every expected verdict computed by
# `certificate._target_holds` on a hand-built `WitnessFamily`, never re-derived inline.

from model_checker.theory_lib.bimodal.semantic.certificate import (
    LabelledLasso,
    WitnessFamily,
    _target_holds,
)


def _selector_pattern_none(n):
    """`n` window positions, none satisfying (C4): cycles through (premise absent, conclusion
    present), (premise present, conclusion present), (premise absent, conclusion absent) --
    never (premise present, conclusion absent), which is exactly what satisfying (C4) requires."""
    combos = [(False, True), (True, True), (False, False)]
    return [combos[i % 3] for i in range(n)]


def _selector_pattern_one(n):
    """`n` window positions, exactly index 0 satisfying (C4); the rest cycle through every other
    premise/conclusion combination, so every combination is exercised somewhere in this pattern."""
    combos = [(False, True), (True, True), (False, False)]
    return [(True, False)] + [combos[(i - 1) % 3] for i in range(1, n)]


def _selector_pattern_several(n):
    """`n` window positions, exactly indices 0 and `n - 1` satisfying (C4); the interior cycles
    through non-satisfying combinations."""
    combos = [(False, True), (True, True), (False, False)]
    result = [(True, False)] * n
    for i in range(1, n - 1):
        result[i] = combos[(i - 1) % 3]
    return result


def _selector_pattern_all(n):
    """`n` window positions, every one satisfying (C4)."""
    return [(True, False)] * n


_SELECTOR_PATTERNS = {
    "none": _selector_pattern_none,
    "one": _selector_pattern_one,
    "several": _selector_pattern_several,
    "all": _selector_pattern_all,
}


def _build_selector_family(nb, nm, nf, pattern):
    """Build a single-lasso `WitnessFamily` whose main lasso's label at window position `i`
    carries `P` iff `pattern[i][0]` and `Q` iff `pattern[i][1]`. The window-position order
    (`registry.target_window()`, now `certificate._box_window`) is exactly the concatenation of
    the back, mid, and fwd segments in index order -- both `wrap` and `t` are monotonic across
    the window (see the swept-range test in `test_witness_registry.py`) -- so slicing `pattern`
    at `nb`/`nb + nm` lines up exactly with `LabelledLasso`'s own segment order."""
    labels = [
        frozenset(f for f, present in ((P, has_p), (Q, has_q)) if present)
        for has_p, has_q in pattern
    ]
    lasso = LabelledLasso(
        back=tuple(labels[:nb]),
        mid=tuple(labels[nb:nb + nm]),
        fwd=tuple(labels[nb + nm:nb + nm + nf]),
    )
    return WitnessFamily(bx={}, lassos=(lasso,))


def _assert_bits_from_family(solver, registry, family):
    """Assert `registry.bit(0, t, f) == (f in family.main.label(t))` for every `t` in the window
    and every `f` in the closure -- derived from the *same* `family`/`LabelledLasso` the expected
    verdicts below are read from, never written out twice by hand."""
    for t in registry.target_window():
        label = family.main.label(t)
        for f in registry.closure:
            solver.add(registry.bit(0, t, f) == (f in label))


class TestSelectorConservativity:
    """Pins that the one-hot target selector (`sel`/`target_constraints`, decision D5) is a
    *conservative* encoding of (C4) `Target`: with only `target_constraints` asserted -- no local
    coherence, no fulfilment, no box faithfulness -- the encoding is satisfiable with some
    `sel[t]` true exactly when `certificate._target_holds` holds of the corresponding hand-built
    `WitnessFamily` at that `t`. Every expected verdict here is computed by calling
    `_target_holds`, never re-derived inline -- the weakness `TestTargetConstraints` above does
    not close (F2). See `docs/ADEQUACY.md` section 7.3 for the conservativity argument this test
    pins: the selector is a lossless Skolemization of (C4)'s existential target time, so
    restricting `sel`'s domain to `target_window()` can discard only duplicate representations of
    an in-window target time, never a satisfying one."""

    @pytest.mark.parametrize("back,mid,fwd", [(2, 1, 2), (1, 1, 1)])
    @pytest.mark.parametrize("pattern_name", ["none", "one", "several", "all"])
    def test_aggregate_satisfiability_matches_target_holds(self, back, mid, fwd, pattern_name):
        registry = WitnessRegistry(back=back, mid=mid, fwd=fwd, closure=[P, Q])
        generator = WitnessConstraintGenerator(registry)
        window = list(registry.target_window())
        pattern = _SELECTOR_PATTERNS[pattern_name](len(window))
        family = _build_selector_family(back, mid, fwd, pattern)

        solver = z3.Solver()
        solver.add(*generator.target_constraints(premises=[P], conclusions=[Q]))
        _assert_bits_from_family(solver, registry, family)

        expected_sat = any(_target_holds(family, [P], [Q], t) for t in window)
        assert (solver.check() == z3.sat) == expected_sat

    @pytest.mark.parametrize("back,mid,fwd", [(2, 1, 2), (1, 1, 1)])
    @pytest.mark.parametrize("pattern_name", ["none", "one", "several", "all"])
    def test_per_position_selectability_matches_target_holds(self, back, mid, fwd, pattern_name):
        registry = WitnessRegistry(back=back, mid=mid, fwd=fwd, closure=[P, Q])
        generator = WitnessConstraintGenerator(registry)
        window = list(registry.target_window())
        pattern = _SELECTOR_PATTERNS[pattern_name](len(window))
        family = _build_selector_family(back, mid, fwd, pattern)

        solver = z3.Solver()
        solver.add(*generator.target_constraints(premises=[P], conclusions=[Q]))
        _assert_bits_from_family(solver, registry, family)

        for t in window:
            expected = _target_holds(family, [P], [Q], t)
            solver.push()
            solver.add(generator.sel(t) == True)
            result = solver.check()
            solver.pop()
            assert (result == z3.sat) == expected

    def test_flipped_premise_bit_at_the_only_satisfying_position_is_unsat(self):
        """Deliberate-mismatch guard against vacuity: take the "one" pattern's only satisfying
        position and flip that position's premise bit against what the family actually says.
        The solver must disagree (flip to unsat) while `_target_holds`, read off the *unflipped*
        family, still reports that position as satisfying -- evidence the assertions above are
        actually reading the bits they claim to, not passing vacuously."""
        back, mid, fwd = 2, 1, 2
        registry = WitnessRegistry(back=back, mid=mid, fwd=fwd, closure=[P, Q])
        generator = WitnessConstraintGenerator(registry)
        window = list(registry.target_window())
        pattern = _selector_pattern_one(len(window))
        family = _build_selector_family(back, mid, fwd, pattern)
        t0 = window[0]  # the only satisfying position, by _selector_pattern_one's construction

        assert _target_holds(family, [P], [Q], t0)  # sanity: unflipped family satisfies at t0

        solver = z3.Solver()
        solver.add(*generator.target_constraints(premises=[P], conclusions=[Q]))
        for t in window:
            label = family.main.label(t)
            for f in registry.closure:
                value = f in label
                if t == t0 and f == P:
                    value = not value  # the deliberate flip
                solver.add(registry.bit(0, t, f) == value)
        assert solver.check() == z3.unsat

    def test_periodicity_corollary_agrees_with_in_window_representative(self):
        """No Z3 solve at all: `_target_holds` at a position outside `target_window()` must equal
        `_target_holds` at its in-window representative (`registry.wrap` agreement), covering
        both `t < -nb` and `t >= nm + nf`."""
        back, mid, fwd = 2, 1, 2
        registry = WitnessRegistry(back=back, mid=mid, fwd=fwd, closure=[P, Q])
        window = list(registry.target_window())
        pattern = _selector_pattern_several(len(window))
        family = _build_selector_family(back, mid, fwd, pattern)

        below_window = [-3, -4, -5]  # each < -nb == -2
        above_window = [3, 4, 5]  # each >= nm + nf == 3
        assert all(t < -registry.nb for t in below_window)
        assert all(t >= registry.nm + registry.nf for t in above_window)

        for t in below_window + above_window:
            slot = registry.wrap(t)
            representative = next(tp for tp in window if registry.wrap(tp) == slot)
            assert _target_holds(family, [P], [Q], t) == _target_holds(
                family, [P], [Q], representative
            )


# ---------------------------------------------------------------------------
# Phase 8: fulfilment and box-faithfulness constraint generators
# ---------------------------------------------------------------------------

from model_checker.theory_lib.bimodal.semantic.certificate import _box_window, _coherence_window


class TestFulfilmentConstraints:
    def test_forcing_until_true_with_no_possible_witness_is_unsat(self):
        """Locally coherent alone admits infinite postponement (the fixpoint law is satisfied by
        never delivering the event); adding fulfilment must reject it once the event is forced
        false everywhere in the scan window."""
        until = Untl(guard=P, event=Q)
        registry = WitnessRegistry(back=1, mid=0, fwd=1, closure=[P, Q, until])
        generator = WitnessConstraintGenerator(registry)
        solver = z3.Solver()
        solver.add(*generator.local_coherence_constraints(lasso=0))
        solver.add(*generator.fulfilment_constraints(lasso=0))
        solver.add(registry.bit(0, 0, until) == True)
        for t in _coherence_window(registry):
            solver.add(registry.bit(0, t, Q) == False)
        assert solver.check() == z3.unsat

    def test_an_immediate_witness_is_sat(self):
        """`p U q` at `t=0` with `q` true at `t=1` is fulfilled immediately -- no contradiction
        with local coherence or fulfilment."""
        until = Untl(guard=P, event=Q)
        registry = WitnessRegistry(back=1, mid=0, fwd=1, closure=[P, Q, until])
        generator = WitnessConstraintGenerator(registry)
        solver = z3.Solver()
        solver.add(*generator.local_coherence_constraints(lasso=0))
        solver.add(*generator.fulfilment_constraints(lasso=0))
        solver.add(registry.bit(0, 0, until) == True)
        solver.add(registry.bit(0, 1, Q) == True)
        assert solver.check() == z3.sat

    def test_since_mirrors_until_in_the_backward_direction(self):
        since = Snce(guard=P, event=Q)
        registry = WitnessRegistry(back=1, mid=0, fwd=1, closure=[P, Q, since])
        generator = WitnessConstraintGenerator(registry)
        solver = z3.Solver()
        solver.add(*generator.local_coherence_constraints(lasso=0))
        solver.add(*generator.fulfilment_constraints(lasso=0))
        solver.add(registry.bit(0, 0, since) == True)
        for t in _coherence_window(registry):
            solver.add(registry.bit(0, t, Q) == False)
        assert solver.check() == z3.unsat

    def test_fulfilment_constraints_are_quantifier_free(self):
        until = Untl(guard=P, event=Q)
        registry = WitnessRegistry(back=2, mid=2, fwd=2, closure=[P, Q, until])
        generator = WitnessConstraintGenerator(registry)
        for constraint in generator.fulfilment_constraints(lasso=0):
            assert not _contains_quantifier(constraint)


class TestBoxFaithfulnessConstraints:
    def test_box_guessed_true_forces_argument_everywhere(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P, BOX_P])
        generator = WitnessConstraintGenerator(registry)
        solver = z3.Solver()
        solver.add(*generator.box_faithfulness_constraints(lassos=[0]))
        solver.add(registry.guess(P) == True)
        # Forcing p false at some position of the (only) lasso must be UNSAT.
        solver.add(registry.bit(0, 0, P) == False)
        assert solver.check() == z3.unsat

    def test_box_guessed_true_and_argument_everywhere_is_sat(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P, BOX_P])
        generator = WitnessConstraintGenerator(registry)
        solver = z3.Solver()
        solver.add(*generator.box_faithfulness_constraints(lassos=[0]))
        solver.add(registry.guess(P) == True)
        for t in _box_window(registry):
            solver.add(registry.bit(0, t, P) == True)
        assert solver.check() == z3.sat

    def test_box_guessed_false_forces_an_omitting_position_on_some_lasso(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P, BOX_P])
        generator = WitnessConstraintGenerator(registry)
        solver = z3.Solver()
        solver.add(*generator.box_faithfulness_constraints(lassos=[0, 1]))
        solver.add(registry.guess(P) == False)
        # p present at every position of every lasso must be UNSAT.
        for lasso in (0, 1):
            for t in _box_window(registry):
                solver.add(registry.bit(lasso, t, P) == True)
        assert solver.check() == z3.unsat

    def test_box_guessed_false_with_one_omitting_position_is_sat(self):
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P, BOX_P])
        generator = WitnessConstraintGenerator(registry)
        solver = z3.Solver()
        solver.add(*generator.box_faithfulness_constraints(lassos=[0, 1]))
        solver.add(registry.guess(P) == False)
        window = list(_box_window(registry))
        for t in window:
            solver.add(registry.bit(0, t, P) == True)
        # lasso 1 omits p at the first window position -- a genuine witness.
        solver.add(registry.bit(1, window[0], P) == False)
        assert solver.check() == z3.sat

    def test_the_witness_lasso_allocated_for_a_false_box_can_be_included(self):
        """`allocate_witness_lasso` and `box_faithfulness_constraints` compose: the caller passes
        the allocated index among `lassos`, and that lasso alone omitting the argument suffices."""
        registry = WitnessRegistry(back=1, mid=1, fwd=1, closure=[P, BOX_P])
        generator = WitnessConstraintGenerator(registry)
        witness_lasso = registry.allocate_witness_lasso(P)
        solver = z3.Solver()
        solver.add(*generator.box_faithfulness_constraints(lassos=[0, witness_lasso]))
        solver.add(registry.guess(P) == False)
        solver.add(registry.bit(witness_lasso, list(_box_window(registry))[0], P) == False)
        assert solver.check() == z3.sat

    def test_box_faithfulness_constraints_are_quantifier_free(self):
        registry = WitnessRegistry(back=2, mid=2, fwd=2, closure=[P, BOX_P])
        generator = WitnessConstraintGenerator(registry)
        for constraint in generator.box_faithfulness_constraints(lassos=[0, 1]):
            assert not _contains_quantifier(constraint)
