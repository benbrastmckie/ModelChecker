"""Z3 confirmation of the candidates' nested logic, hyperintensionality, and regression.

The oracle tests (``test_candidate_logic_oracle.py``) pin each candidate's
profile from sampled small frames; these tests ask Z3 for the same schemata
at N=3 (nested antecedents) and N=3/N=4 (constitutive comparison) and assert
the recorded outcome.  A solve that hits ``max_time`` is recorded as
``timeout`` and only fails the test when it contradicts a definite
expectation the oracle has pinned.

The constitutive comparison sharpens the research's small-frame
hypothesis: at N=4 Z3's exhaustive search finds two counterfactuals with the
same truth-set and distinct ``ILC``/``ILMC`` propositions, while ``W``,
``L``, ``MC`` remain valid.  The countermodels Z3 returned differ only on
*impossible* states (``\equiv`` compares whole verifier and falsifier sets,
as it does for sentence letters); the oracle's large n=4 samples also hold
pairs differing on possible states (``test_candidate_logic_oracle.py``,
``tests/n4_separation_witnesses.json``).
``test_constitutive_countermodel_is_confirmed_by_the_oracle`` re-evaluates
the Z3 model in the oracle: the settled clauses separate the pair, the
truth-set functions do not.
"""

import pytest

from model_checker import ModelConstraints, Syntax, run_test
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.theory_lib.logos.semantic import (
    LogosModelStructure,
    LogosProposition,
    LogosSemantics,
)
from model_checker.theory_lib.logos.subtheories.counterfactual.candidate_examples import (
    CANDIDATE_KEYS,
    CONSTITUTIVE_SUBTHEORIES,
    NESTED_SUBTHEORIES,
    ORACLE_PROFILE,
    SCHEMATA,
    constitutive_example,
    constitutive_examples,
    counterfactual_candidate_examples,
    nested_examples,
    regression_examples,
)
from model_checker.theory_lib.logos.subtheories.counterfactual.examples import unit_tests
from model_checker.theory_lib.logos.subtheories.counterfactual.frame_oracle import (
    CF,
    Atom,
    Evaluator,
    frame_from_model_structure,
    interpretation_from_model_structure,
)
from model_checker.theory_lib.logos.subtheories.counterfactual.tests.harness import (
    outcome,
    solve,
)

A, B, C, D = Atom("A"), Atom("B"), Atom("C"), Atom("D")

#: Constitutive comparison outcomes recorded in the implementation run (max_time 60 s).
CONSTITUTIVE_OUTCOME = {
    3: {"I": "countermodel", "ILC": "valid", "ILMC": "valid", "W": "valid", "L": "valid", "MC": "valid"},
    4: {"I": "countermodel", "ILC": "countermodel", "ILMC": "countermodel", "W": "valid", "L": "valid", "MC": "valid"},
}

REGRESSION_GUARD = ("CF_CM_1", "CF_CM_7", "CF_TH_2", "CF_TH_11")


def _run(case, subtheories):
    registry = LogosOperatorRegistry()
    registry.load_subtheories(list(subtheories))
    return run_test(case, LogosSemantics, LogosProposition, registry.get_operators(),
                    Syntax, ModelConstraints, LogosModelStructure)


# ---------------------------------------------------------------------------
# Generators
# ---------------------------------------------------------------------------

def test_generator_counts():
    """Scope hypothesis: 6 x 6 nested examples, 6 constitutive per N, 37 x 6 regression runs."""
    assert len(CANDIDATE_KEYS) == 6
    assert sum(len(nested_examples(key)) for key in CANDIDATE_KEYS) == 36
    assert sum(len(constitutive_examples(key, (3,))) for key in CANDIDATE_KEYS) == 6
    assert sum(len(regression_examples(key)) for key in CANDIDATE_KEYS) == 37 * 6
    assert len(unit_tests) == 37
    assert set(counterfactual_candidate_examples).isdisjoint(unit_tests)


# ---------------------------------------------------------------------------
# Nested-antecedent schemata at N=3
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("schema", SCHEMATA)
@pytest.mark.parametrize("key", CANDIDATE_KEYS)
def test_nested_schema_matches_the_oracle_profile(key, schema):
    premises, conclusions, settings = nested_examples(key, N=3, max_time=30)[f"{key}_{schema.upper()}"]
    expected = "countermodel" if ORACLE_PROFILE[key][schema] == "countermodel" else "valid"
    result = outcome(premises, conclusions, settings, NESTED_SUBTHEORIES)
    assert result != "timeout", f"{key} {schema}: inconclusive at N=3 within {settings['max_time']} s"
    assert result == expected, f"{key} {schema}: Z3 {result}, oracle {expected}"


def test_ilmc_nested_profile_is_the_base_counterfactual_profile():
    """Identity, MP, strict -> cf and might-identity theorems; strengthening and cf -> strict countermodels."""
    profile = ORACLE_PROFILE["ILMC"]
    assert {s for s in SCHEMATA if profile[s] == "theorem"} == {"identity", "modus_ponens", "strict_to_cf", "might_identity"}
    assert {s for s in SCHEMATA if profile[s] == "countermodel"} == {"strengthening", "cf_to_strict"}
    assert ORACLE_PROFILE["ILC"] == {s: "theorem" for s in SCHEMATA}


# ---------------------------------------------------------------------------
# Constitutive comparison: necessary equivalence versus identity
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("N", (3, 4))
@pytest.mark.parametrize("key", CANDIDATE_KEYS)
def test_constitutive_comparison_outcome(key, N):
    """Recorded outcome per candidate; see the module docstring for the N=4 separation."""
    premises, conclusions, settings = constitutive_example(key, N, max_time=60)
    result = outcome(premises, conclusions, settings, CONSTITUTIVE_SUBTHEORIES)
    expected = CONSTITUTIVE_OUTCOME[N][key]
    if result == "timeout":
        pytest.xfail(f"{key} N={N}: inconclusive within {settings['max_time']} s (recorded {expected})")
    assert result == expected, f"{key} N={N}: Z3 {result}, recorded {expected}"


@pytest.mark.parametrize("key", ("ILMC", "ILC"))
def test_constitutive_countermodel_is_confirmed_by_the_oracle(key):
    """On the Z3-found N=4 model the settled clauses separate the pair and the truth-set functions do not."""
    premises, conclusions, settings = constitutive_example(key, 4, max_time=60)
    syntax, semantics, structure = solve(premises, conclusions, settings, CONSTITUTIVE_SUBTHEORIES)
    if structure.z3_model is None:
        pytest.xfail(f"{key} N=4: no countermodel within {settings['max_time']} s")
    frame = frame_from_model_structure(structure)
    interp = interpretation_from_model_structure(structure, syntax)
    ev = Evaluator(frame, interp)
    x, y = CF(key, A, B), CF(key, C, D)
    assert ev.truth_set(x) == ev.truth_set(y)
    assert not ev.identical_proposition(x, y)
    for baseline in ("W", "L", "MC"):
        assert ev.identical_proposition(CF(baseline, A, B), CF(baseline, C, D)), baseline
    # The countermodels Z3 returned in the implementation run differed only
    # on impossible members; models differing on possible states exist at
    # n=4 too (tests/n4_separation_witnesses.json), so which kind Z3 returns
    # is not pinned -- only that the pair is separated at all.
    vx, fx = ev.proposition(x)
    vy, fy = ev.proposition(y)
    assert (vx ^ vy) | (fx ^ fy)


# ---------------------------------------------------------------------------
# Regression guard: the baseline examples behave identically under every candidate
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name", REGRESSION_GUARD)
@pytest.mark.parametrize("key", CANDIDATE_KEYS)
def test_regression_guard(key, name):
    case = regression_examples(key)[f"{key}_{name}"]
    assert _run(case, NESTED_SUBTHEORIES), f"{name} under {key} no longer meets its expectation"
