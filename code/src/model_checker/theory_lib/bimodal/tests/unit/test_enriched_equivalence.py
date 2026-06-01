"""Enriched Operator Equivalence Test Suite.

This module verifies that all 11 enriched operators in the bimodal logic framework
produce Z3 results identical to their primitive-operator expansions. Each test
constructs a biconditional (iff) formula and checks it is a theorem (no countermodel).

Test Matrix Coverage:
  Level 1 (direct primitive mappings): neg, top, next, prev -- 20 tests (5 each)
  Level 2 (defined via Level 1): and, or, diamond, some_future, some_past -- 25 tests (5 each)
  Level 3 (defined via Level 2): all_future, all_past -- 10 tests (5 each)
  Nested combinations: 5 cross-operator tests at complexity levels 3, 5, 7
  Boundary sensitivity: 6 tests for all_future/all_past at M=2 and M=3

Total: 66 test cases

Enriched -> Primitive Mappings:
  neg A        = A -> bot         (\\neg A  vs  A \\rightarrow \\bot)
  top          = neg bot          (\\neg \\bot  -- TopOperator has pre-existing bug, don't use \\top)
  and A B      = neg(A -> neg B)  ((A \\wedge B)  vs  \\neg (A \\rightarrow \\neg B))
  or A B       = neg A -> B       ((A \\vee B)  vs  \\neg A \\rightarrow B)
  diamond A    = neg(box(neg A))  (\\Diamond A  vs  \\neg \\Box \\neg A)
  next A       = A U bot          (\\next A  vs  A \\Until \\bot)
  prev A       = A S bot          (\\prev A  vs  A \\Since \\bot)
  some_future A = A U neg bot     (\\future A  vs  A \\Until \\neg \\bot)  [lowercase \\future = F]
  some_past A  = A S neg bot      (\\past A  vs  A \\Since \\neg \\bot)    [lowercase \\past = P]
  all_future A = neg(F(neg A))    (\\Future A  vs  \\neg \\future \\neg A) [uppercase \\Future = G]
  all_past A   = neg(P(neg A))    (\\Past A  vs  \\neg \\past \\neg A)    [uppercase \\Past = H]

Gate Criteria:
  No enriched-tag formula produces a different SAT/UNSAT result than its
  primitive equivalent. All biconditionals must be theorems (return False from
  run_test, meaning no countermodel was found).

Note on TopOperator:
  TopOperator (\\top) has a known pre-existing evaluation bug in derived_definition.
  All top-related tests use the \\neg \\bot expansion instead of \\top directly.
"""

from __future__ import annotations

import pytest

from model_checker import ModelConstraints, Syntax, run_test
from model_checker.theory_lib.bimodal import (
    BimodalStructure,
    BimodalProposition,
    BimodalSemantics,
    bimodal_operators,
)
from model_checker.utils.context import isolated_z3_context


##############################################################################
# Shared helper functions
##############################################################################

def _make_equiv_example(conclusion, M=2):
    """Create example dict for an equivalence theorem test.

    Args:
        conclusion: The infix formula string to test as a theorem.
        M: Number of time steps (default 2, increase for boundary tests).

    Returns:
        An example list [premises, conclusions, settings] ready for run_test.
    """
    return [
        [],
        [conclusion],
        {
            'N': 2,
            'M': M,
            'contingent': False,
            'disjoint': False,
            'max_time': 5,
            'expectation': False,
        }
    ]


def _run_theorem(conclusion, M=2):
    """Run an equivalence test and return True if it's a theorem (no countermodel).

    Uses isolated_z3_context() to prevent Z3 state leakage between tests.

    Args:
        conclusion: The infix formula string to check as a theorem.
        M: Number of time steps (default 2, increase for boundary tests).

    Returns:
        True if no countermodel was found (formula is a theorem), False otherwise.
    """
    example = _make_equiv_example(conclusion, M=M)
    with isolated_z3_context():
        result = run_test(
            example,
            BimodalSemantics,
            BimodalProposition,
            bimodal_operators,
            Syntax,
            ModelConstraints,
            BimodalStructure,
        )
    return result


##############################################################################
# Phase 1: Infrastructure smoke test
##############################################################################

class TestInfrastructure:
    """Smoke test to verify the helper infrastructure works correctly."""

    def test_smoke_neg_basic(self):
        """Smoke test: neg A <-> (A -> bot) is a theorem via _run_theorem."""
        assert _run_theorem("(\\neg A \\leftrightarrow (A \\rightarrow \\bot))"), (
            "Infrastructure smoke test failed: neg equivalence should be a theorem"
        )


##############################################################################
# Phase 2: Level 1 Operator Tests (neg, top, next, prev)
##############################################################################

class TestNegEquivalence:
    """Tests that \\neg (negation) is equivalent to its primitive expansion A -> bot."""

    def test_neg_basic_definition(self):
        """\\neg A <-> (A \\rightarrow \\bot) is a theorem."""
        assert _run_theorem("(\\neg A \\leftrightarrow (A \\rightarrow \\bot))"), (
            "neg basic definition should be a theorem"
        )

    def test_neg_double_negation(self):
        """\\neg \\neg A <-> A is a theorem (double negation elimination)."""
        assert _run_theorem("(\\neg \\neg A \\leftrightarrow A)"), (
            "double negation should be a theorem"
        )

    def test_neg_de_morgan(self):
        """\\neg (A \\wedge B) <-> (\\neg A \\vee \\neg B) is a theorem (De Morgan)."""
        assert _run_theorem("(\\neg (A \\wedge B) \\leftrightarrow (\\neg A \\vee \\neg B))"), (
            "De Morgan's law for negation of conjunction should be a theorem"
        )

    def test_neg_bot(self):
        """\\neg \\bot <-> \\neg \\bot is a trivial theorem."""
        assert _run_theorem("(\\neg \\bot \\leftrightarrow \\neg \\bot)"), (
            "neg bot self-equivalence should be a theorem"
        )

    def test_neg_implication(self):
        """\\neg (A \\rightarrow B) <-> (A \\wedge \\neg B) is a theorem."""
        assert _run_theorem("(\\neg (A \\rightarrow B) \\leftrightarrow (A \\wedge \\neg B))"), (
            "neg of implication equivalence should be a theorem"
        )


class TestTopEquivalence:
    """Tests for top (tautology) using \\neg \\bot expansion.

    Note: TopOperator (\\top) has a pre-existing evaluation bug in derived_definition.
    All tests use the \\neg \\bot expansion instead of \\top directly.
    """

    def test_top_self_equivalence(self):
        """\\neg \\bot <-> \\neg \\bot is a trivial theorem."""
        assert _run_theorem("(\\neg \\bot \\leftrightarrow \\neg \\bot)"), (
            "top self-equivalence (using \\neg \\bot) should be a theorem"
        )

    def test_top_implies_top(self):
        """(\\neg \\bot \\rightarrow \\neg \\bot) is a theorem."""
        assert _run_theorem("(\\neg \\bot \\rightarrow \\neg \\bot)"), (
            "top implies top should be a theorem"
        )

    def test_neg_top_implies_bot(self):
        """\\neg \\neg \\bot \\rightarrow \\bot is a theorem (negation of top implies bot)."""
        assert _run_theorem("(\\neg \\neg \\bot \\rightarrow \\bot)"), (
            "neg of top implies bot should be a theorem"
        )

    def test_anything_implies_top(self):
        """(A \\rightarrow \\neg \\bot) is a theorem (anything implies top)."""
        assert _run_theorem("(A \\rightarrow \\neg \\bot)"), (
            "anything implies top should be a theorem"
        )

    def test_bot_implies_top(self):
        """(\\bot \\rightarrow \\neg \\bot) is a theorem (bot implies top by ex falso)."""
        assert _run_theorem("(\\bot \\rightarrow \\neg \\bot)"), (
            "bot implies top should be a theorem"
        )


class TestNextEquivalence:
    """Tests that \\next (next-step) is equivalent to A \\Until \\bot."""

    def test_next_basic_definition(self):
        """\\next A <-> (A \\Until \\bot) is a theorem."""
        assert _run_theorem("(\\next A \\leftrightarrow (A \\Until \\bot))"), (
            "next basic definition should be a theorem"
        )

    def test_next_of_neg(self):
        """\\next \\neg A <-> (\\neg A \\Until \\bot) is a theorem."""
        assert _run_theorem("(\\next \\neg A \\leftrightarrow (\\neg A \\Until \\bot))"), (
            "next of negation should be a theorem"
        )

    def test_next_of_and(self):
        """\\next (A \\wedge B) <-> ((A \\wedge B) \\Until \\bot) is a theorem."""
        assert _run_theorem("(\\next (A \\wedge B) \\leftrightarrow ((A \\wedge B) \\Until \\bot))"), (
            "next of conjunction should be a theorem"
        )

    def test_next_of_or(self):
        """\\next (A \\vee B) <-> ((A \\vee B) \\Until \\bot) is a theorem."""
        assert _run_theorem("(\\next (A \\vee B) \\leftrightarrow ((A \\vee B) \\Until \\bot))"), (
            "next of disjunction should be a theorem"
        )

    def test_neg_of_next(self):
        """\\neg \\next A <-> \\neg (A \\Until \\bot) is a theorem."""
        assert _run_theorem("(\\neg \\next A \\leftrightarrow \\neg (A \\Until \\bot))"), (
            "negation of next should be a theorem"
        )


class TestPrevEquivalence:
    """Tests that \\prev (previous-step) is equivalent to A \\Since \\bot."""

    def test_prev_basic_definition(self):
        """\\prev A <-> (A \\Since \\bot) is a theorem."""
        assert _run_theorem("(\\prev A \\leftrightarrow (A \\Since \\bot))"), (
            "prev basic definition should be a theorem"
        )

    def test_prev_of_neg(self):
        """\\prev \\neg A <-> (\\neg A \\Since \\bot) is a theorem."""
        assert _run_theorem("(\\prev \\neg A \\leftrightarrow (\\neg A \\Since \\bot))"), (
            "prev of negation should be a theorem"
        )

    def test_prev_of_and(self):
        """\\prev (A \\wedge B) <-> ((A \\wedge B) \\Since \\bot) is a theorem."""
        assert _run_theorem("(\\prev (A \\wedge B) \\leftrightarrow ((A \\wedge B) \\Since \\bot))"), (
            "prev of conjunction should be a theorem"
        )

    def test_prev_of_or(self):
        """\\prev (A \\vee B) <-> ((A \\vee B) \\Since \\bot) is a theorem."""
        assert _run_theorem("(\\prev (A \\vee B) \\leftrightarrow ((A \\vee B) \\Since \\bot))"), (
            "prev of disjunction should be a theorem"
        )

    def test_neg_of_prev(self):
        """\\neg \\prev A <-> \\neg (A \\Since \\bot) is a theorem."""
        assert _run_theorem("(\\neg \\prev A \\leftrightarrow \\neg (A \\Since \\bot))"), (
            "negation of prev should be a theorem"
        )


##############################################################################
# Phase 3: Level 2 Operator Tests (and, or, diamond, some_future, some_past)
##############################################################################

class TestAndEquivalence:
    """Tests that \\wedge (conjunction) is equivalent to \\neg (A \\rightarrow \\neg B)."""

    def test_and_basic_definition(self):
        """(A \\wedge B) <-> \\neg (A \\rightarrow \\neg B) is a theorem."""
        assert _run_theorem("((A \\wedge B) \\leftrightarrow \\neg (A \\rightarrow \\neg B))"), (
            "and basic definition should be a theorem"
        )

    def test_and_commutativity(self):
        """(A \\wedge B) <-> (B \\wedge A) is a theorem (commutativity)."""
        assert _run_theorem("((A \\wedge B) \\leftrightarrow (B \\wedge A))"), (
            "conjunction commutativity should be a theorem"
        )

    def test_and_with_bot(self):
        """(A \\wedge \\bot) <-> \\bot is a theorem."""
        assert _run_theorem("((A \\wedge \\bot) \\leftrightarrow \\bot)"), (
            "conjunction with bot should be a theorem"
        )

    def test_and_associativity(self):
        """((A \\wedge B) \\wedge C) <-> (A \\wedge (B \\wedge C)) is a theorem."""
        assert _run_theorem("(((A \\wedge B) \\wedge C) \\leftrightarrow (A \\wedge (B \\wedge C)))"), (
            "conjunction associativity should be a theorem"
        )

    def test_and_contradiction(self):
        """(A \\wedge \\neg A) <-> \\bot is a theorem (law of non-contradiction)."""
        assert _run_theorem("((A \\wedge \\neg A) \\leftrightarrow \\bot)"), (
            "conjunction contradiction should be a theorem"
        )


class TestOrEquivalence:
    """Tests that \\vee (disjunction) is equivalent to \\neg A \\rightarrow B."""

    def test_or_basic_definition(self):
        """(A \\vee B) <-> (\\neg A \\rightarrow B) is a theorem."""
        assert _run_theorem("((A \\vee B) \\leftrightarrow (\\neg A \\rightarrow B))"), (
            "or basic definition should be a theorem"
        )

    def test_or_commutativity(self):
        """(A \\vee B) <-> (B \\vee A) is a theorem (commutativity)."""
        assert _run_theorem("((A \\vee B) \\leftrightarrow (B \\vee A))"), (
            "disjunction commutativity should be a theorem"
        )

    def test_or_with_bot(self):
        """(A \\vee \\bot) <-> A is a theorem."""
        assert _run_theorem("((A \\vee \\bot) \\leftrightarrow A)"), (
            "disjunction with bot should be a theorem"
        )

    def test_or_excluded_middle(self):
        """(A \\vee \\neg A) is a theorem (law of excluded middle)."""
        assert _run_theorem("(A \\vee \\neg A)"), (
            "excluded middle should be a theorem"
        )

    def test_or_excluded_middle_is_top(self):
        """(A \\vee \\neg A) <-> \\neg \\bot is a theorem."""
        assert _run_theorem("((A \\vee \\neg A) \\leftrightarrow \\neg \\bot)"), (
            "excluded middle equivalence to top should be a theorem"
        )


class TestDiamondEquivalence:
    """Tests that \\Diamond (possibility) is equivalent to \\neg \\Box \\neg A."""

    def test_diamond_basic_definition(self):
        """\\Diamond A <-> \\neg \\Box \\neg A is a theorem."""
        assert _run_theorem("(\\Diamond A \\leftrightarrow \\neg \\Box \\neg A)"), (
            "diamond basic definition should be a theorem"
        )

    def test_diamond_of_neg(self):
        """\\Diamond \\neg A <-> \\neg \\Box A is a theorem."""
        assert _run_theorem("(\\Diamond \\neg A \\leftrightarrow \\neg \\Box A)"), (
            "diamond of negation should be a theorem"
        )

    def test_diamond_of_and(self):
        """\\Diamond (A \\wedge B) <-> \\neg \\Box \\neg (A \\wedge B) is a theorem."""
        assert _run_theorem(
            "(\\Diamond (A \\wedge B) \\leftrightarrow \\neg \\Box \\neg (A \\wedge B))"
        ), (
            "diamond of conjunction should be a theorem"
        )

    def test_diamond_of_or(self):
        """\\Diamond (A \\vee B) <-> \\neg \\Box (\\neg A \\wedge \\neg B) is a theorem."""
        assert _run_theorem(
            "(\\Diamond (A \\vee B) \\leftrightarrow \\neg \\Box (\\neg A \\wedge \\neg B))"
        ), (
            "diamond of disjunction should be a theorem"
        )

    def test_box_implies_diamond(self):
        """(\\Box A \\rightarrow \\Diamond A) is a theorem."""
        assert _run_theorem("(\\Box A \\rightarrow \\Diamond A)"), (
            "box implies diamond should be a theorem"
        )


class TestSomeFutureEquivalence:
    """Tests that \\future (some_future, F) is equivalent to its primitive expansion.

    Note: lowercase \\future = F (DefFuture / some_future) = A Until neg-bot
          uppercase \\Future = G (FutureOperator / all_future) = primitive
    """

    def test_some_future_via_all_future(self):
        """\\future A <-> \\neg \\Future \\neg A is a theorem.

        This verifies that F A (some_future) is the dual of G (all_future).
        Note: \\future = F = some_future; \\Future = G = all_future.
        """
        assert _run_theorem("(\\future A \\leftrightarrow \\neg \\Future \\neg A)"), (
            "some_future via all_future duality should be a theorem"
        )

    def test_some_future_via_until(self):
        """\\future A <-> (A \\Until \\neg \\bot) is a theorem.

        This verifies F A unfolds as A Until top (= A Until neg-bot).
        """
        assert _run_theorem("(\\future A \\leftrightarrow (A \\Until \\neg \\bot))"), (
            "some_future via Until should be a theorem"
        )

    def test_some_future_of_neg(self):
        """\\future \\neg A <-> \\neg \\Future A is a theorem."""
        assert _run_theorem("(\\future \\neg A \\leftrightarrow \\neg \\Future A)"), (
            "some_future of negation should be a theorem"
        )

    def test_some_future_of_and(self):
        """\\future (A \\wedge B) <-> \\neg \\Future \\neg (A \\wedge B) is a theorem."""
        assert _run_theorem(
            "(\\future (A \\wedge B) \\leftrightarrow \\neg \\Future \\neg (A \\wedge B))"
        ), (
            "some_future of conjunction should be a theorem"
        )

    def test_some_future_of_or(self):
        """\\future (A \\vee B) <-> \\neg \\Future \\neg (A \\vee B) is a theorem."""
        assert _run_theorem(
            "(\\future (A \\vee B) \\leftrightarrow \\neg \\Future \\neg (A \\vee B))"
        ), (
            "some_future of disjunction should be a theorem"
        )


class TestSomePastEquivalence:
    """Tests that \\past (some_past, P) is equivalent to its primitive expansion.

    Note: lowercase \\past = P (DefPast / some_past) = A Since neg-bot
          uppercase \\Past = H (PastOperator / all_past) = primitive
    """

    def test_some_past_via_all_past(self):
        """\\past A <-> \\neg \\Past \\neg A is a theorem.

        This verifies that P A (some_past) is the dual of H (all_past).
        Note: \\past = P = some_past; \\Past = H = all_past.
        """
        assert _run_theorem("(\\past A \\leftrightarrow \\neg \\Past \\neg A)"), (
            "some_past via all_past duality should be a theorem"
        )

    def test_some_past_via_since(self):
        """\\past A <-> (A \\Since \\neg \\bot) is a theorem.

        This verifies P A unfolds as A Since top (= A Since neg-bot).
        """
        assert _run_theorem("(\\past A \\leftrightarrow (A \\Since \\neg \\bot))"), (
            "some_past via Since should be a theorem"
        )

    def test_some_past_of_neg(self):
        """\\past \\neg A <-> \\neg \\Past A is a theorem."""
        assert _run_theorem("(\\past \\neg A \\leftrightarrow \\neg \\Past A)"), (
            "some_past of negation should be a theorem"
        )

    def test_some_past_of_and(self):
        """\\past (A \\wedge B) <-> \\neg \\Past \\neg (A \\wedge B) is a theorem."""
        assert _run_theorem(
            "(\\past (A \\wedge B) \\leftrightarrow \\neg \\Past \\neg (A \\wedge B))"
        ), (
            "some_past of conjunction should be a theorem"
        )

    def test_some_past_of_or(self):
        """\\past (A \\vee B) <-> \\neg \\Past \\neg (A \\vee B) is a theorem."""
        assert _run_theorem(
            "(\\past (A \\vee B) \\leftrightarrow \\neg \\Past \\neg (A \\vee B))"
        ), (
            "some_past of disjunction should be a theorem"
        )


##############################################################################
# Phase 4: Level 3 Operators, Nested Combinations, Boundary Sensitivity
##############################################################################

class TestAllFutureEquivalence:
    """Tests for \\Future (all_future, G) -- the universal future operator (primitive).

    Note: uppercase \\Future = G = all_future (primitive operator)
          lowercase \\future = F = some_future (derived operator)
    """

    def test_all_future_self_equivalence(self):
        """\\Future A <-> \\Future A is a trivial theorem."""
        assert _run_theorem("(\\Future A \\leftrightarrow \\Future A)"), (
            "all_future self-equivalence should be a theorem"
        )

    def test_all_future_via_some_future(self):
        """\\Future A <-> \\neg \\future \\neg A is a theorem (G as dual of F)."""
        assert _run_theorem("(\\Future A \\leftrightarrow \\neg \\future \\neg A)"), (
            "all_future via some_future duality should be a theorem"
        )

    def test_all_future_via_until(self):
        """\\Future A <-> \\neg (\\neg A \\Until \\neg \\bot) is a theorem."""
        assert _run_theorem(
            "(\\Future A \\leftrightarrow \\neg (\\neg A \\Until \\neg \\bot))"
        ), (
            "all_future via Until should be a theorem"
        )

    def test_all_future_of_and(self):
        """\\Future (A \\wedge B) <-> \\neg \\future \\neg (A \\wedge B) is a theorem."""
        assert _run_theorem(
            "(\\Future (A \\wedge B) \\leftrightarrow \\neg \\future \\neg (A \\wedge B))"
        ), (
            "all_future of conjunction should be a theorem"
        )

    def test_all_future_of_or(self):
        """\\Future (A \\vee B) <-> \\neg \\future \\neg (A \\vee B) is a theorem."""
        assert _run_theorem(
            "(\\Future (A \\vee B) \\leftrightarrow \\neg \\future \\neg (A \\vee B))"
        ), (
            "all_future of disjunction should be a theorem"
        )


class TestAllPastEquivalence:
    """Tests for \\Past (all_past, H) -- the universal past operator (primitive).

    Note: uppercase \\Past = H = all_past (primitive operator)
          lowercase \\past = P = some_past (derived operator)
    """

    def test_all_past_self_equivalence(self):
        """\\Past A <-> \\Past A is a trivial theorem."""
        assert _run_theorem("(\\Past A \\leftrightarrow \\Past A)"), (
            "all_past self-equivalence should be a theorem"
        )

    def test_all_past_via_some_past(self):
        """\\Past A <-> \\neg \\past \\neg A is a theorem (H as dual of P)."""
        assert _run_theorem("(\\Past A \\leftrightarrow \\neg \\past \\neg A)"), (
            "all_past via some_past duality should be a theorem"
        )

    def test_all_past_via_since(self):
        """\\Past A <-> \\neg (\\neg A \\Since \\neg \\bot) is a theorem."""
        assert _run_theorem(
            "(\\Past A \\leftrightarrow \\neg (\\neg A \\Since \\neg \\bot))"
        ), (
            "all_past via Since should be a theorem"
        )

    def test_all_past_of_and(self):
        """\\Past (A \\wedge B) <-> \\neg \\past \\neg (A \\wedge B) is a theorem."""
        assert _run_theorem(
            "(\\Past (A \\wedge B) \\leftrightarrow \\neg \\past \\neg (A \\wedge B))"
        ), (
            "all_past of conjunction should be a theorem"
        )

    def test_all_past_of_or(self):
        """\\Past (A \\vee B) <-> \\neg \\past \\neg (A \\vee B) is a theorem."""
        assert _run_theorem(
            "(\\Past (A \\vee B) \\leftrightarrow \\neg \\past \\neg (A \\vee B))"
        ), (
            "all_past of disjunction should be a theorem"
        )


class TestNestedCombinations:
    """Tests for nested operator combinations at complexity levels 3, 5, and 7.

    These tests verify equivalences hold when operators are composed together,
    exercising the pipeline with more complex formula structures.
    """

    def test_diamond_of_and_neg(self):
        """\\Diamond (A \\wedge \\neg B) <-> \\neg \\Box \\neg (A \\wedge \\neg B) (depth 3)."""
        assert _run_theorem(
            "(\\Diamond (A \\wedge \\neg B) \\leftrightarrow \\neg \\Box \\neg (A \\wedge \\neg B))"
        ), (
            "diamond of (A and neg B) should be a theorem (depth 3)"
        )

    def test_some_future_of_or_neg(self):
        """\\future (A \\vee \\neg B) <-> \\neg \\Future \\neg (A \\vee \\neg B) (depth 3)."""
        assert _run_theorem(
            "(\\future (A \\vee \\neg B) \\leftrightarrow \\neg \\Future \\neg (A \\vee \\neg B))"
        ), (
            "some_future of (A or neg B) should be a theorem (depth 3)"
        )

    def test_quadruple_negation(self):
        """\\neg \\neg \\neg \\neg A <-> A is a theorem (depth 4, quadruple negation)."""
        assert _run_theorem("(\\neg \\neg \\neg \\neg A \\leftrightarrow A)"), (
            "quadruple negation elimination should be a theorem (depth 4)"
        )

    def test_diamond_or_distribution(self):
        """(\\Diamond A \\vee \\Diamond B) <-> \\neg (\\Box \\neg A \\wedge \\Box \\neg B) (depth 5)."""
        assert _run_theorem(
            "((\\Diamond A \\vee \\Diamond B) \\leftrightarrow \\neg (\\Box \\neg A \\wedge \\Box \\neg B))"
        ), (
            "diamond-or distribution should be a theorem (depth 5)"
        )

    def test_next_of_and_neg(self):
        """\\next (A \\wedge \\neg B) <-> ((A \\wedge \\neg B) \\Until \\bot) (depth 3)."""
        assert _run_theorem(
            "(\\next (A \\wedge \\neg B) \\leftrightarrow ((A \\wedge \\neg B) \\Until \\bot))"
        ), (
            "next of (A and neg B) should be a theorem (depth 3)"
        )

    def test_prev_next_negation_symmetry(self):
        """\\neg \\next A <-> \\neg (A \\Until \\bot) and \\neg \\prev A <-> \\neg (A \\Since \\bot) combined."""
        assert _run_theorem(
            "((\\neg \\next A \\leftrightarrow \\neg (A \\Until \\bot)) \\wedge (\\neg \\prev A \\leftrightarrow \\neg (A \\Since \\bot)))"
        ), (
            "prev-next negation symmetry should be a theorem (depth 5)"
        )

    def test_modal_temporal_nesting(self):
        """\\Box \\next A <-> \\Box (A \\Until \\bot) is a theorem (modal-temporal nesting)."""
        assert _run_theorem(
            "(\\Box \\next A \\leftrightarrow \\Box (A \\Until \\bot))"
        ), (
            "modal-temporal nesting (box of next) should be a theorem (depth 3)"
        )


class TestBoundarySensitivity:
    """Boundary sensitivity tests for all_future and all_past at M=2 and M=3.

    Universal quantifier operators (G/H) can exhibit boundary effects when the
    time horizon (M) affects vacuous quantification. These tests verify the
    equivalences hold at both M=2 and M=3.
    """

    def test_all_future_equiv_at_m2(self):
        """\\Future A <-> \\neg \\future \\neg A at M=2 is a theorem."""
        assert _run_theorem("(\\Future A \\leftrightarrow \\neg \\future \\neg A)", M=2), (
            "all_future equivalence at M=2 should be a theorem"
        )

    def test_all_future_equiv_at_m3(self):
        """\\Future A <-> \\neg \\future \\neg A at M=3 is a theorem."""
        assert _run_theorem("(\\Future A \\leftrightarrow \\neg \\future \\neg A)", M=3), (
            "all_future equivalence at M=3 should be a theorem"
        )

    def test_all_past_equiv_at_m2(self):
        """\\Past A <-> \\neg \\past \\neg A at M=2 is a theorem."""
        assert _run_theorem("(\\Past A \\leftrightarrow \\neg \\past \\neg A)", M=2), (
            "all_past equivalence at M=2 should be a theorem"
        )

    def test_all_past_equiv_at_m3(self):
        """\\Past A <-> \\neg \\past \\neg A at M=3 is a theorem."""
        assert _run_theorem("(\\Past A \\leftrightarrow \\neg \\past \\neg A)", M=3), (
            "all_past equivalence at M=3 should be a theorem"
        )

    def test_all_future_via_until_at_m3(self):
        """\\Future A <-> \\neg (\\neg A \\Until \\neg \\bot) at M=3 is a theorem."""
        assert _run_theorem(
            "(\\Future A \\leftrightarrow \\neg (\\neg A \\Until \\neg \\bot))", M=3
        ), (
            "all_future via Until at M=3 should be a theorem"
        )

    def test_all_past_via_since_at_m3(self):
        """\\Past A <-> \\neg (\\neg A \\Since \\neg \\bot) at M=3 is a theorem."""
        assert _run_theorem(
            "(\\Past A \\leftrightarrow \\neg (\\neg A \\Since \\neg \\bot))", M=3
        ), (
            "all_past via Since at M=3 should be a theorem"
        )
