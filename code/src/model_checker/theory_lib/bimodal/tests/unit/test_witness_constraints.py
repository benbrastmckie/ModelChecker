"""Unit tests for `WitnessConstraintGenerator`'s local-coherence and target generators.

Mirrors `docs/ADEQUACY.md` section 1's `LocalCoherentLab` and `Target`, and the certificate
re-checker's `_coherent_at`/`_target_holds` (`certificate.py`) -- the encoder and the re-checker
must agree on what "coherent" and "on target" mean, even though the encoder only ever visits one
representative position per slot (see `witness_constraints.py`'s module docstring for why that
suffices).
"""

from __future__ import annotations

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
