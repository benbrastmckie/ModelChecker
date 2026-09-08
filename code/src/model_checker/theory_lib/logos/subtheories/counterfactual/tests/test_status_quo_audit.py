"""Audit of the status-quo counterfactual verifier clauses.

``CounterfactualOperator`` in ``operators.py`` carries two verifier clauses that
disagree with each other:

- ``extended_verify`` / ``extended_falsify`` (the Z3-side clause, around lines
  74-90): a state verifies ``A \\boxright B`` at evaluation world ``w`` iff it
  *is* ``w`` and the counterfactual is true at ``w``.  The verifier set is
  ``{w}`` and varies with the evaluation point.
- ``find_verifiers_and_falsifiers`` (the Python-side clause, around lines
  92-150): every world at which the counterfactual is true is a verifier and
  every world at which it is false is a falsifier, regardless of the evaluation
  point.

These tests pin both clauses exactly as they stand so that a later change to
either side is caught, and record the disagreement as a finding rather than a
defect: every later measurement of the status quo must say which side it
measured.
"""

import pytest

from model_checker.theory_lib.logos.subtheories.counterfactual.tests.harness import (
    base_settings,
    find_sentence,
    solve,
)

# \Box forces the counterfactual to be true at every world, and a contingent
# sentence letter forces at least two worlds, so the two clauses must differ.
PREMISES = ['\\Box (A \\boxright C)']
CONCLUSIONS = []


@pytest.fixture(scope="module")
def solved():
    syntax, semantics, structure = solve(PREMISES, CONCLUSIONS, base_settings(N=3))
    assert structure.z3_model is not None, "expected a model for a satisfiable premise"
    sentence = find_sentence(syntax, '(A \\boxright C)')
    return syntax, semantics, structure, sentence


def _truth_set(semantics, structure, sentence):
    evaluate = structure.z3_model.evaluate
    return {
        w for w in structure.z3_world_states
        if bool(evaluate(sentence.operator.true_at(*sentence.arguments, {"world": w})))
    }


def test_at_least_two_worlds(solved):
    _, _, structure, _ = solved
    assert len(structure.z3_world_states) >= 2


def test_z3_side_verifier_set_is_the_evaluation_world(solved):
    """Z3 side: verifiers at ``w`` are exactly ``{w}`` when true there, else empty."""
    _, semantics, structure, sentence = solved
    op = sentence.operator
    left, right = sentence.arguments
    evaluate = structure.z3_model.evaluate
    truth_set = _truth_set(semantics, structure, sentence)
    for w in structure.z3_world_states:
        z3_verifiers = {
            s for s in structure.all_states
            if bool(evaluate(op.extended_verify(s, left, right, {"world": w})))
        }
        z3_falsifiers = {
            s for s in structure.all_states
            if bool(evaluate(op.extended_falsify(s, left, right, {"world": w})))
        }
        expected_v = {w} if w in truth_set else set()
        expected_f = set() if w in truth_set else {w}
        assert z3_verifiers == expected_v, f"Z3-side verifiers at {w}: {z3_verifiers}"
        assert z3_falsifiers == expected_f, f"Z3-side falsifiers at {w}: {z3_falsifiers}"


def test_python_side_verifier_set_is_every_true_world(solved):
    """Python side: verifiers are all true worlds, independent of the evaluation point."""
    _, semantics, structure, sentence = solved
    op = sentence.operator
    left, right = sentence.arguments
    truth_set = _truth_set(semantics, structure, sentence)
    worlds = set(structure.z3_world_states)
    for w in worlds:
        py_v, py_f = op.find_verifiers_and_falsifiers(left, right, {"world": w})
        assert py_v == truth_set, f"Python-side verifiers at {w}: {py_v}"
        assert py_f == worlds - truth_set, f"Python-side falsifiers at {w}: {py_f}"


def test_the_two_clauses_disagree(solved):
    """Finding: the Z3-side and Python-side verifier sets differ at every world.

    The premise makes the counterfactual true everywhere, so the Python side
    returns every world while the Z3 side returns only the evaluation world.
    """
    _, semantics, structure, sentence = solved
    op = sentence.operator
    left, right = sentence.arguments
    evaluate = structure.z3_model.evaluate
    assert _truth_set(semantics, structure, sentence) == set(structure.z3_world_states)
    for w in structure.z3_world_states:
        z3_verifiers = {
            s for s in structure.all_states
            if bool(evaluate(op.extended_verify(s, left, right, {"world": w})))
        }
        py_v, _ = op.find_verifiers_and_falsifiers(left, right, {"world": w})
        assert z3_verifiers != py_v
        assert z3_verifiers < py_v
