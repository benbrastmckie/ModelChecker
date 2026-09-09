"""Availability, parsing and cross-validation of the candidate counterfactual operators.

Cross-validation runs each candidate on identical examples and checks, on
every solved model, that three independent computations of the verifier and
falsifier sets agree:

(a) the operator's Python-side ``find_verifiers_and_falsifiers``,
(b) the frame oracle evaluated on the frame extracted from the model, and
(c) the operator's Z3-side clause evaluated in the model at every state and
    at every evaluation world -- which also checks context-freedom, since the
    Z3-side set must not vary with the world.
"""

import pytest

from model_checker import Syntax
from model_checker.theory_lib.logos.subtheories.counterfactual import (
    CANDIDATE_OPERATORS,
    CANDIDATE_ROLES,
    MIGHT_OPERATORS,
    get_operators,
    substitute_candidate,
)
from model_checker.theory_lib.logos.subtheories.counterfactual.candidates import (
    DIRECT,
    PREDICATE,
    CandidateCounterfactual,
)
from model_checker.theory_lib.logos.subtheories.counterfactual.frame_oracle import (
    CF,
    Evaluator,
    formula_from_sentence,
    frame_from_model_structure,
    interpretation_from_model_structure,
)
from model_checker.theory_lib.logos.subtheories.counterfactual.tests.harness import (
    base_settings,
    load_registry,
    solve,
    state_int,
)

KEYS = sorted(CANDIDATE_OPERATORS)

# Examples with countermodels, so that a solved model exists to cross-validate
# on, with the smallest N at which the countermodel appears (CF_CM_1 needs
# N=4 under every clause, including the status quo).  CF_CM_19 nests a
# counterfactual in consequent position; the last example nests one in
# antecedent position.
CROSS_VALIDATION_EXAMPLES = {
    "CF_CM_1": (['\\neg A', '(A \\boxright C)'], ['((A \\wedge B) \\boxright C)'], 4),
    "CF_CM_7": (['(A \\boxright B)'], ['(\\neg B \\boxright \\neg A)'], 3),
    "CF_CM_19": (['((A \\wedge B) \\boxright C)'], ['(A \\boxright (B \\boxright C))'], 3),
    "NESTED_ANTECEDENT": (['((A \\boxright B) \\boxright C)', '\\neg (A \\boxright B)'], [], 3),
}


# ---------------------------------------------------------------------------
# Availability and parsing
# ---------------------------------------------------------------------------

def test_candidate_operators_are_registered():
    """Scope hypothesis: six candidates, twelve candidate operator names, one status quo pair."""
    operators = get_operators()
    assert set(CANDIDATE_OPERATORS) == {"I", "ILC", "ILMC", "W", "L", "MC"}
    assert set(CANDIDATE_ROLES) == set(CANDIDATE_OPERATORS)
    candidate_names = {n for n in operators if n not in ("\\boxright", "\\diamondright")}
    assert len(candidate_names) == 12
    for key, cls in CANDIDATE_OPERATORS.items():
        assert operators[f"\\boxright{key}"] is cls
        assert operators[f"\\diamondright{key}"] is MIGHT_OPERATORS[key]
        assert issubclass(cls, CandidateCounterfactual)
        assert cls.key == key
    assert operators["\\boxright"].__name__ == "CounterfactualOperator"


def test_no_name_collides_with_imposition_aliases():
    from model_checker.theory_lib.imposition.operators import get_imposition_operators
    imposition_names = set(get_imposition_operators())
    candidate_names = {f"\\boxright{k}" for k in KEYS} | {f"\\diamondright{k}" for k in KEYS}
    assert not (candidate_names & imposition_names)
    assert "\\boxrightlogos" in imposition_names


@pytest.mark.parametrize("key", KEYS)
def test_candidate_names_parse_in_nested_formulas(key):
    registry = load_registry()
    premises = [
        substitute_candidate('((A \\boxright B) \\boxright (A \\diamondright B))', key),
    ]
    syntax = Syntax(premises, [], registry.get_operators())
    outer = syntax.premises[0]
    assert outer.operator.name == f"\\boxright{key}"
    assert outer.arguments[0].operator.name == f"\\boxright{key}"
    # The might variant is a defined operator: it expands to a negation.
    assert outer.arguments[1].operator.name == "\\neg"
    assert outer.arguments[1].original_operator.name == f"\\diamondright{key}"


def test_substitute_candidate_rewrites_both_operators():
    assert substitute_candidate('(A \\boxright (B \\diamondright C))', "W") == '(A \\boxrightW (B \\diamondrightW C))'
    assert substitute_candidate('\\neg A', "W") == '\\neg A'


# ---------------------------------------------------------------------------
# Cross-validation
# ---------------------------------------------------------------------------

def _solved(key, name):
    premises, conclusions, N = CROSS_VALIDATION_EXAMPLES[name]
    premises = [substitute_candidate(p, key) for p in premises]
    conclusions = [substitute_candidate(c, key) for c in conclusions]
    syntax, semantics, structure = solve(premises, conclusions, base_settings(N=N))
    assert structure.z3_model is not None, f"{name} has no countermodel under {key}"
    return syntax, semantics, structure


def _candidate_sentences(syntax, key):
    return [
        s for s in syntax.all_sentences.values()
        if s.operator is not None and s.operator.name == f"\\boxright{key}"
    ]


@pytest.mark.parametrize("name", sorted(CROSS_VALIDATION_EXAMPLES))
@pytest.mark.parametrize("key", KEYS)
def test_python_side_equals_oracle(key, name):
    syntax, semantics, structure = _solved(key, name)
    frame = frame_from_model_structure(structure)
    interp = interpretation_from_model_structure(structure, syntax)
    oracle = Evaluator(frame, interp)
    sentences = _candidate_sentences(syntax, key)
    assert sentences
    for sentence in sentences:
        left, right = sentence.arguments
        py_v, py_f = sentence.operator.find_verifiers_and_falsifiers(left, right, {"world": structure.z3_main_world})
        formula = formula_from_sentence(sentence)
        assert isinstance(formula, CF) and formula.key == key
        or_v, or_f = oracle.proposition(formula)
        assert {state_int(s) for s in py_v} == set(or_v), f"{sentence.name}: verifiers"
        assert {state_int(s) for s in py_f} == set(or_f), f"{sentence.name}: falsifiers"
        # The proposition attached to the sentence is the Python-side one.
        assert sentence.proposition.verifiers == py_v
        assert sentence.proposition.falsifiers == py_f


@pytest.mark.parametrize("name", sorted(CROSS_VALIDATION_EXAMPLES))
@pytest.mark.parametrize("key", KEYS)
def test_z3_side_equals_python_side_at_every_world(key, name):
    """Z3/Python agreement and context-freedom in one assertion."""
    syntax, semantics, structure = _solved(key, name)
    evaluate = structure.z3_model.evaluate
    for sentence in _candidate_sentences(syntax, key):
        op = sentence.operator
        left, right = sentence.arguments
        py_v, py_f = op.find_verifiers_and_falsifiers(left, right, {"world": structure.z3_main_world})
        for w in structure.z3_world_states:
            point = {"world": w}
            z3_v = {
                s for s in structure.all_states
                if bool(evaluate(op.verifier_clause(s, left, right, point, DIRECT)))
            }
            z3_f = {
                s for s in structure.all_states
                if bool(evaluate(op.falsifier_clause(s, left, right, point, DIRECT)))
            }
            if z3_v != py_v:
                view_info = {
                    "worlds": sorted(int(x.as_long()) for x in structure.z3_world_states),
                    "possible": sorted(int(x.as_long()) for x in structure.z3_possible_states),
                    "left_verifiers": sorted(int(x.as_long()) for x in left.proposition.verifiers),
                    "T_direct_z3": {int(u.as_long()): bool(evaluate(op.true_at(left, right, {"world": u}))) for u in structure.z3_world_states},
                    "is_world_at": {int(u.as_long()): bool(evaluate(op.is_world_at(u))) for u in structure.all_states},
                }
                assert z3_v == py_v, f"{sentence.name} at {w}: Z3 verifiers {z3_v} vs Python {py_v}; {view_info}"
            assert z3_f == py_f, f"{sentence.name} at {w}: Z3 falsifiers {z3_f} vs Python {py_f}"


@pytest.mark.parametrize("name", sorted(CROSS_VALIDATION_EXAMPLES))
@pytest.mark.parametrize("key", KEYS)
def test_truth_and_falsity_clauses_are_complementary_at_worlds(key, name):
    """Licenses ``Not(cf_true)`` as the falsity side of the predicate encoding."""
    syntax, semantics, structure = _solved(key, name)
    evaluate = structure.z3_model.evaluate
    for sentence in _candidate_sentences(syntax, key):
        left, right = sentence.arguments
        for w in structure.z3_world_states:
            point = {"world": w}
            t = bool(evaluate(sentence.operator.true_at(left, right, point)))
            f = bool(evaluate(sentence.operator.false_at(left, right, point)))
            assert t != f, f"{sentence.name} is {'both' if t else 'neither'} at {w}"


@pytest.mark.parametrize("key", [k for k in KEYS if k != "I"])
def test_predicate_encoding_agrees_with_direct_encoding(key):
    """Solve a nested-antecedent example under the predicate encoding and compare clauses."""
    cls = CANDIDATE_OPERATORS[key]
    previous = cls.truth_encoding
    cls.truth_encoding = PREDICATE
    try:
        syntax, semantics, structure = _solved(key, "NESTED_ANTECEDENT")
    finally:
        cls.truth_encoding = previous
    evaluate = structure.z3_model.evaluate
    inner = syntax.all_sentences[substitute_candidate('(A \\boxright B)', key)]
    left, right = inner.arguments
    op = inner.operator
    for s in structure.all_states:
        for w in structure.z3_world_states:
            point = {"world": w}
            direct = bool(evaluate(op.verifier_clause(s, left, right, point, DIRECT)))
            predicate = bool(evaluate(op.verifier_clause(s, left, right, point, PREDICATE)))
            assert direct == predicate, f"{inner.name}: encodings differ at state {s}"
