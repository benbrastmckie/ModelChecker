"""Characterization tests: structural properties of the candidate clauses.

Every count here is pinned from the research exploration (report
``01_exact-imposition-verifier-clauses.md``, findings F4-F6); if a count
differs, the report is corrected, not the test.  The sweeps run in a few
seconds, so they stay in the default run.

Set ``CF_STRUCTURE_MATRIX=/path/to/file.json`` to have the sweep fixture
write the full property matrix (counts, population sizes, first witnesses)
to that file.
"""

import json
import os

import pytest

from model_checker.theory_lib.logos.subtheories.counterfactual.frame_oracle import (
    CF,
    SWEEP_PROPERTIES,
    Atom,
    Evaluator,
    enumerate_models,
    exact_sufficiency_mismatches,
    is_part_of,
    measure,
    structure_sweep,
)
from model_checker.theory_lib.logos.subtheories.counterfactual.tests.witness_frames import (
    f3_worlds,
    frame_f3,
    frame_f3z,
    frame_g,
    src_null_remainder_model,
)

A, B = Atom("A"), Atom("B")

SWEEP_KEYS = ("I", "ILC", "ILMC", "W", "L", "MC", "SRC", "XPe", "XPa", "XS")

#: n=3 exhaustive: (population, contingent) and the seed/limit of the n=4 sample.
N3_POPULATION = 3204
N3_CONTINGENT = 24
N4_SEED, N4_LIMIT, N4_CONTINGENT = 11, 300, 11

# Count of models failing each property; a name not listed is 0.
N3_FAILS = {
    "I": {"exclusive_compat": 24, "bridge_sound_V": 24, "bridge_sound_F": 24},
    "ILC": {},
    "ILMC": {},
    "W": {},
    "L": {},
    "MC": {},
    "SRC": {},
    "XPe": {"closure_V": 3, "closure_F": 18, "exhaustive": 3192, "bridge_sound_V": 6,
            "bridge_sufficient_V": 1554, "bridge_sufficient_F": 1644},
    "XPa": {"exhaustive": 3198, "bridge_sufficient_V": 1560, "bridge_sufficient_F": 1644},
    "XS": {"exhaustive": 3192, "bridge_sound_V": 6,
           "bridge_sufficient_V": 1554, "bridge_sufficient_F": 1644},
}
N4_FAILS = {
    "I": {"closure_F": 1, "exclusive_compat": 11, "bridge_sound_V": 6, "bridge_sound_F": 11},
    "ILC": {},
    "ILMC": {},
    "W": {},
    "L": {},
    "MC": {},
    "SRC": {"exhaustive": 1, "bridge_sufficient_F": 1},
    "XPe": {"closure_V": 1, "closure_F": 18, "exhaustive": 297, "bridge_sound_V": 2,
            "bridge_sufficient_V": 118, "bridge_sufficient_F": 180},
    "XPa": {"exhaustive": 297, "bridge_sufficient_V": 119, "bridge_sufficient_F": 180},
    "XS": {"exhaustive": 297, "bridge_sound_V": 2,
           "bridge_sufficient_V": 118, "bridge_sufficient_F": 180},
}
# (contingent models with a possible proper verifier, ... with a proper falsifier).
N3_PROPER = {
    "I": (24, 24), "ILC": (0, 24), "ILMC": (0, 24), "W": (0, 0), "L": (0, 24),
    "MC": (0, 24), "SRC": (0, 24), "XPe": (6, 6), "XPa": (0, 6), "XS": (6, 6),
}
N4_PROPER = {
    "I": (10, 11), "ILC": (6, 11), "ILMC": (6, 11), "W": (0, 0), "L": (6, 11),
    "MC": (6, 11), "SRC": (2, 7), "XPe": (4, 3), "XPa": (2, 3), "XS": (4, 3),
}


@pytest.fixture(scope="module")
def n3_models():
    models = list(enumerate_models(3, ("A", "B")))
    assert len(models) == N3_POPULATION
    return models


@pytest.fixture(scope="module")
def n4_models():
    models = list(enumerate_models(4, ("A", "B"), limit=N4_LIMIT, seed=N4_SEED))
    assert len(models) == N4_LIMIT
    return models


@pytest.fixture(scope="module")
def sweeps(n3_models, n4_models):
    result = {
        "n3_exhaustive": structure_sweep(n3_models, SWEEP_KEYS, A, B),
        "n4_sample": structure_sweep(n4_models, SWEEP_KEYS, A, B),
    }
    target = os.environ.get("CF_STRUCTURE_MATRIX")
    if target:
        payload = {
            "populations": {
                "n3_exhaustive": {"models": N3_POPULATION, "contingent": N3_CONTINGENT},
                "n4_sample": {"models": N4_LIMIT, "seed": N4_SEED, "contingent": N4_CONTINGENT},
            },
            "properties": list(SWEEP_PROPERTIES),
            "sweeps": result,
        }
        with open(target, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=1, ensure_ascii=False)
    return result


# ---------------------------------------------------------------------------
# Exhaustive n=3 and sampled n=4 sweeps
# ---------------------------------------------------------------------------

def test_populations_match_the_research(sweeps):
    """Scope hypothesis: 3,204 models with 24 contingent at n=3; 300 sampled with 11 at n=4."""
    for key in SWEEP_KEYS:
        assert sweeps["n3_exhaustive"][key]["models"] == N3_POPULATION
        assert sweeps["n3_exhaustive"][key]["proper"]["contingent_models"] == N3_CONTINGENT
        assert sweeps["n4_sample"][key]["models"] == N4_LIMIT
        assert sweeps["n4_sample"][key]["proper"]["contingent_models"] == N4_CONTINGENT


@pytest.mark.parametrize("key", SWEEP_KEYS)
def test_n3_exhaustive_failure_counts(sweeps, key):
    fails = sweeps["n3_exhaustive"][key]["fails"]
    expected = {prop: N3_FAILS[key].get(prop, 0) for prop in SWEEP_PROPERTIES}
    assert fails == expected, key


@pytest.mark.parametrize("key", SWEEP_KEYS)
def test_n4_sample_failure_counts(sweeps, key):
    fails = sweeps["n4_sample"][key]["fails"]
    expected = {prop: N4_FAILS[key].get(prop, 0) for prop in SWEEP_PROPERTIES}
    assert fails == expected, key


@pytest.mark.parametrize("key", SWEEP_KEYS)
def test_proper_verifier_desideratum(sweeps, key):
    """Contingent models with a possible verifier (falsifier) properly below a world."""
    for population, expected in (("n3_exhaustive", N3_PROPER), ("n4_sample", N4_PROPER)):
        proper = sweeps[population][key]["proper"]
        observed = (proper["contingent_with_proper_V"], proper["contingent_with_proper_F"])
        assert observed == expected[key], (population, key)


def test_settled_imposition_clauses_are_structurally_clean_everywhere(sweeps):
    """ILC, ILMC and the baselines fail no property on any model; only ILC/ILMC/L/MC/SRC have proper falsifiers at n=3."""
    for population in ("n3_exhaustive", "n4_sample"):
        for key in ("ILC", "ILMC", "W", "L", "MC"):
            assert not any(sweeps[population][key]["fails"].values()), (population, key)
    # The concession: at n=3 no contingent model gives ILMC a proper possible verifier.
    assert sweeps["n3_exhaustive"]["ILMC"]["proper"]["contingent_with_proper_V"] == 0
    assert sweeps["n3_exhaustive"]["ILMC"]["proper"]["contingent_with_proper_F"] == N3_CONTINGENT
    # From n=4 on most contingent models do.
    assert sweeps["n4_sample"]["ILMC"]["proper"]["contingent_with_proper_V"] == 6
    assert sweeps["n4_sample"]["ILMC"]["proper"]["contingent_proper_V_and_all_props"] == 6


def test_impossible_verifiers_are_harmless_for_every_candidate(sweeps):
    """Report 02 F3.5: impossible members lie below no world, so they never reach the bridge."""
    for population in ("n3_exhaustive", "n4_sample"):
        for key in SWEEP_KEYS:
            fails = sweeps[population][key]["fails"]
            assert fails["impossible_harmless_V"] == 0 and fails["impossible_harmless_F"] == 0, key


# ---------------------------------------------------------------------------
# F4: the exact family is characterized, and out
# ---------------------------------------------------------------------------

def test_f4_exact_sufficiency_characterization(n3_models):
    """XPe has a verifier below a true world iff every alternative carries a B-verifier already part of that world."""
    checked, mismatches = exact_sufficiency_mismatches(n3_models, A, B, "XPe")
    assert checked == 3228
    assert mismatches == 0


# ---------------------------------------------------------------------------
# F3 frame: ILMC's proper verifiers and IL's closure witness
# ---------------------------------------------------------------------------

def test_f3_ilmc_proper_verifiers_and_il_closure_witness():
    frame, interp = frame_f3()
    ev = Evaluator(frame, interp)
    st = frame.state
    v_ilmc, _ = ev.proposition(CF("ILMC", A, B))
    proper = {s for s in v_ilmc if s in frame.possible and s not in frame.worlds}
    assert proper == {st("a", "p'"), st("a", "q'"), st("a", "b"), st("a", "p'", "b"), st("a", "q'", "b")}
    v_il, _ = ev.proposition(CF("IL", A, B))
    s1, s2 = st("a", "p", "p'"), st("a", "q", "q'")
    assert s1 in v_il and s2 in v_il and (s1 | s2) not in v_il
    assert not frame.is_possible(s1 | s2)
    record = measure("IL", A, B, frame, interp)
    assert record["closure_V"] is False and record["impossible_harmless_V"] is True
    assert measure("ILMC", A, B, frame, interp)["closure_V"] is True


# ---------------------------------------------------------------------------
# Frame G: the mechanism constraint bites (IL != L, ILMC != MC)
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def g():
    frame, interp = frame_g()
    return frame, interp, Evaluator(frame, interp)


def test_frame_g_settlers_that_survive_no_imposition(g):
    """y and a' settle the counterfactual but are not I-verifiers: Alt(y, a) reaches u = a.x.b'."""
    frame, interp, ev = g
    st = frame.state
    u, w = st("a", "x", "b'"), st("a'", "x", "y", "c", "b")
    assert ev.truth_set(CF("L", A, B)) == {st("a", "x", "c", "b"), w}
    v_l, _ = ev.proposition(CF("L", A, B))
    v_i, _ = ev.proposition(CF("I", A, B))
    for settler in (st("y"), st("a'")):
        assert settler in v_l and settler not in v_i
        assert frame.max_compatible_parts(settler, st("a")) == {0}
        assert u in frame.alternatives(settler, st("a"))


def test_frame_g_il_differs_from_l_and_ilmc_from_mc(g):
    frame, interp, ev = g
    st = frame.state
    poss = frame.possible
    v_il, _ = ev.proposition(CF("IL", A, B))
    v_l, _ = ev.proposition(CF("L", A, B))
    assert v_il & poss != v_l & poss
    assert (v_l - v_il) & poss >= {st("y"), st("a'")}
    v_ilmc, _ = ev.proposition(CF("ILMC", A, B))
    v_mc, _ = ev.proposition(CF("MC", A, B))
    assert v_ilmc & poss == {st("c"), st("b"), st("c", "b")}
    assert {st("a'"), st("y")} <= v_mc & poss
    assert not ev.identical_proposition(CF("ILMC", A, B), CF("MC", A, B))
    for key in ("IL", "ILC", "ILMC", "L", "MC"):
        record = measure(key, A, B, frame, interp)
        assert record["bridge_sound_V"] and record["bridge_sufficient_V"] and record["exhaustive"], key


# ---------------------------------------------------------------------------
# Frame F3z: holism defeats the remainder clause
# ---------------------------------------------------------------------------

def test_frame_f3z_remainder_clause_is_insufficient_at_the_holistic_world():
    frame, interp = frame_f3z()
    ev = Evaluator(frame, interp)
    st = frame.state
    w4 = st("a'", "p", "p'", "b", "z")
    w0 = st("a'", "p", "p'", "q", "q'", "b")
    assert ev.cf_true(A, B, w4) and not ev.cf_true(A, B, w0)
    assert frame.max_compatible_parts(w4, st("a")) == {st("p", "p'", "b")}
    assert is_part_of(st("p", "p'", "b"), w0)
    for key in ("SR", "SRC"):
        v, f = ev.proposition(CF(key, A, B))
        assert not any(is_part_of(s, w4) for s in v), key
        assert not any(is_part_of(s, w4) for s in f), key
        record = measure(key, A, B, frame, interp)
        assert record["exhaustive"] is False and record["exhaustive_witness"] == frame.fmt(w4)
        assert record["bridge_sufficient_V"] is False and record["bridge_sufficient_V_witness"] == frame.fmt(w4)
    v_ilmc, _ = ev.proposition(CF("ILMC", A, B))
    for s in (st("p'", "z"), st("b", "z"), st("p'", "b", "z")):
        assert s in v_ilmc and is_part_of(s, w4)
    record = measure("ILMC", A, B, frame, interp)
    assert record["bridge_sufficient_V"] and record["exhaustive"]


# ---------------------------------------------------------------------------
# The null-remainder model: SRC has no falsifier at an antecedent-incompatible world
# ---------------------------------------------------------------------------

def test_src_null_remainder_model_has_no_falsifier_at_d():
    frame, interp = src_null_remainder_model()
    ev = Evaluator(frame, interp)
    st = frame.state
    d, b = st("d"), st("b")
    assert ev.cf_false(A, B, d)
    assert frame.max_compatible_parts(d, b) == {0}
    assert frame.alternatives(d, b) == {st("a", "b"), st("b", "c")}
    for key in ("SR", "SRC"):
        _, f = ev.proposition(CF(key, A, B))
        assert not any(is_part_of(s, d) for s in f), key
        record = measure(key, A, B, frame, interp)
        assert record["bridge_sufficient_F"] is False and record["bridge_sufficient_F_witness"] == "d"
    for key in ("ILMC", "MC"):
        _, f = ev.proposition(CF(key, A, B))
        assert d in f, key
