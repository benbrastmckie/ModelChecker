"""Characterization tests: nested-antecedent logic and hyperintensionality per candidate.

Counts are pinned from the research exploration (report
``01_exact-imposition-verifier-clauses.md``, findings F7 and F8) over the
same seeded n=3 samples the research used (letters ``A, B, C, D``; seed 23
for the logic sweep, seed 37 for the hyperintensionality sweep; 1,500
models each).  One pin corrects the report's prose: the same-truth-set,
distinct-proposition count for ``SR``/``SRC`` on the seed-37 sample is 403
(the value in the archived table), not the 428 the F8 paragraph quotes.

Set ``CF_LOGIC_MATRIX_DIR=/path/to/dir`` to have the sweep fixtures write
``06_logic-matrix.json`` and ``07_hyperintensionality.json`` there.
"""

import json
import os

import pytest

from model_checker.theory_lib.logos.subtheories.counterfactual.frame_oracle import (
    Box,
    CF,
    Implies,
    LOGIC_PRINCIPLES,
    Atom,
    Evaluator,
    Neg,
    enumerate_models,
    hyperintensionality_sweep,
    logic_failures,
    logic_sweep,
    model_to_dict,
)
from model_checker.theory_lib.logos.subtheories.counterfactual.tests.witness_frames import (
    frame_g2,
)

A, B, C, D = Atom("A"), Atom("B"), Atom("C"), Atom("D")

LOGIC_KEYS = ("I", "ILC", "ILMC", "W", "L", "MC", "SRC", "XPa", "XS")
LOGIC_SEED, HYPER_SEED, SAMPLE = 23, 37, 1500
SAME_TRUTH_SET_PAIRS = 723

# Models (of 1,500) with a world at which the principle fails; unlisted = 0.
LOGIC_FAILS = {
    "I": {"identity": 22, "strengthening": 6, "strict_to_cf": 8, "might_identity": 22},
    "ILC": {},
    "W": {},
    "L": {},
    "ILMC": {"strengthening": 361, "cf_to_strict": 700},
    "MC": {"strengthening": 361, "cf_to_strict": 700},
    "SRC": {"strengthening": 200, "cf_to_strict": 372},
    "XPa": {"modus_ponens": 389, "strengthening": 4, "cf_to_strict": 402},
    "XS": {"identity": 7, "modus_ponens": 384, "strengthening": 8, "strict_to_cf": 2, "cf_to_strict": 400},
}

# Same-truth-set pairs with distinct propositions (all states / on possible states).
HYPER_DISTINCT = {
    "I": (1, 1), "ILC": (0, 0), "ILMC": (0, 0), "W": (0, 0), "L": (0, 0), "MC": (0, 0),
    "SRC": (403, 403), "XPa": (480, 480), "XS": (482, 480),
}


@pytest.fixture(scope="module")
def logic_models():
    models = list(enumerate_models(3, ("A", "B", "C", "D"), limit=SAMPLE, seed=LOGIC_SEED))
    assert len(models) == SAMPLE
    return models


@pytest.fixture(scope="module")
def hyper_models():
    models = list(enumerate_models(3, ("A", "B", "C", "D"), limit=SAMPLE, seed=HYPER_SEED))
    assert len(models) == SAMPLE
    return models


def _strict_collapse_witness(models):
    """First sampled model where ILMC separates ``X □→ C`` from ``□(X → C)`` at some world."""
    for frame, interp in models:
        ev = Evaluator(frame, interp)
        x = CF("ILMC", A, B)
        x_c, strict = CF("ILMC", x, C), Box(Implies(x, C))
        for w in frame.worlds:
            if ev.truth(x_c, w) != ev.truth(strict, w):
                return {
                    "model": model_to_dict(frame, interp),
                    "world": frame.fmt(w),
                    "X_cf_C": ev.truth(x_c, w),
                    "strict": ev.truth(strict, w),
                    "ILMC_verifiers_of_X": frame.fmt_set(ev.proposition(x)[0]),
                }
    return None


@pytest.fixture(scope="module")
def sweeps(logic_models, hyper_models):
    logic = logic_sweep(logic_models, LOGIC_KEYS, A, B, C, D)
    hyper = hyperintensionality_sweep(hyper_models, LOGIC_KEYS, (A, B), (C, D))
    collapse = _strict_collapse_witness(logic_models)
    target = os.environ.get("CF_LOGIC_MATRIX_DIR")
    if target:
        with open(os.path.join(target, "06_logic-matrix.json"), "w", encoding="utf-8") as handle:
            json.dump({
                "population": {"n": 3, "letters": ["A", "B", "C", "D"], "seed": LOGIC_SEED, "models": SAMPLE},
                "principles": list(LOGIC_PRINCIPLES),
                "sweep": logic,
                "ilmc_strict_collapse_counterexample": collapse,
            }, handle, indent=1, ensure_ascii=False)
        with open(os.path.join(target, "07_hyperintensionality.json"), "w", encoding="utf-8") as handle:
            json.dump({
                "population": {"n": 3, "letters": ["A", "B", "C", "D"], "seed": HYPER_SEED, "models": SAMPLE},
                "comparison": "A □→ B versus C □→ D with the same truth-set",
                "sweep": hyper,
            }, handle, indent=1, ensure_ascii=False)
    return {"logic": logic, "hyper": hyper, "collapse": collapse}


# ---------------------------------------------------------------------------
# F7: nested-antecedent logic
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("key", LOGIC_KEYS)
def test_f7_nested_logic_profile(sweeps, key):
    fails = sweeps["logic"][key]["fails"]
    expected = {name: LOGIC_FAILS[key].get(name, 0) for name in LOGIC_PRINCIPLES}
    assert sweeps["logic"][key]["models"] == SAMPLE
    assert fails == expected, key


def test_ilmc_has_the_base_counterfactual_profile(sweeps):
    """Identity and modus ponens valid; strengthening and cf -> strict invalid; strict -> cf valid."""
    fails = sweeps["logic"]["ILMC"]["fails"]
    assert fails["identity"] == 0 and fails["modus_ponens"] == 0 and fails["might_identity"] == 0
    assert fails["strict_to_cf"] == 0
    assert fails["strengthening"] > 0 and fails["cf_to_strict"] > 0


def test_every_true_world_verifying_collapses_to_the_strict_conditional(sweeps, logic_models):
    """W, L, IL, ILC keep every true world as a verifier and validate both collapse directions."""
    for key in ("ILC", "W", "L"):
        assert not any(sweeps["logic"][key]["fails"].values()), key
    for frame, interp in logic_models:
        ev = Evaluator(frame, interp)
        x = CF("ILC", A, B)
        v, _ = ev.proposition(x)
        assert ev.truth_set(x) <= v
        x_c, strict = CF("ILC", x, C), Box(Implies(x, C))
        for w in frame.worlds:
            assert ev.truth(x_c, w) == ev.truth(strict, w)


def test_ilmc_separates_the_counterfactual_from_the_strict_conditional(sweeps):
    witness = sweeps["collapse"]
    assert witness is not None
    assert witness["X_cf_C"] != witness["strict"]


# ---------------------------------------------------------------------------
# F8: same truth-set, distinct proposition
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("key", LOGIC_KEYS)
def test_f8_hyperintensionality_counts(sweeps, key):
    entry = sweeps["hyper"][key]
    assert entry["models"] == SAMPLE
    assert entry["same_truth_set"] == SAME_TRUTH_SET_PAIRS
    assert (entry["distinct_props"], entry["distinct_on_possible"]) == HYPER_DISTINCT[key], key


# ---------------------------------------------------------------------------
# Frame G2: the small-frame coincidence broken
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def g2():
    frame, interp = frame_g2()
    return frame, interp, Evaluator(frame, interp)


def test_frame_g2_the_two_counterfactuals_share_a_truth_set(g2):
    frame, _, ev = g2
    st = frame.state
    expected = {st("a", "x'", "b"), st("a", "x", "c", "b"), st("a'", "x", "y", "c", "b")}
    for key in ("L", "MC", "ILC", "ILMC"):
        assert ev.truth_set(CF(key, A, B)) == expected, key
        assert ev.truth_set(CF(key, C, D)) == expected, key


def test_frame_g2_truth_set_functions_give_identical_propositions(g2):
    _, _, ev = g2
    for key in ("L", "MC", "W"):
        assert ev.identical_proposition(CF(key, A, B), CF(key, C, D)), key


def test_frame_g2_settled_imposition_gives_distinct_propositions(g2):
    frame, _, ev = g2
    st = frame.state
    for key in ("IL", "ILC", "ILMC"):
        assert not ev.identical_proposition(CF(key, A, B), CF(key, C, D)), key
        v_ab, _ = ev.proposition(CF(key, A, B))
        v_cd, _ = ev.proposition(CF(key, C, D))
        assert st("x'") in v_ab and st("x'") not in v_cd, key
        for s in (st("a'"), st("y")):
            assert s in v_cd and s not in v_ab, key
    v_ab, _ = ev.proposition(CF("ILMC", A, B))
    v_cd, _ = ev.proposition(CF("ILMC", C, D))
    poss = frame.possible
    assert v_ab & poss == {st("x'"), st("c"), st("b"), st("x'", "b"), st("c", "b")}
    assert {st("a'"), st("y"), st("a'", "y"), st("c"), st("b")} <= v_cd & poss


def test_frame_g2_ilmc_difference_is_visible_in_nested_truth(g2):
    """(A □→ B) □→ C is false at every world while (C □→ D) □→ C is true at three of four."""
    frame, _, ev = g2
    st = frame.state
    worlds = [st("a", "x", "b'"), st("a", "x", "c", "b"), st("a'", "x", "y", "c", "b"), st("a", "x'", "b")]
    x, y = CF("ILMC", A, B), CF("ILMC", C, D)
    assert [ev.truth(CF("ILMC", x, C), w) for w in worlds] == [False, False, False, False]
    assert [ev.truth(CF("ILMC", y, C), w) for w in worlds] == [True, True, True, False]
    assert [ev.truth(CF("ILMC", x, Neg(A)), w) for w in worlds] == [False, False, False, False]
    assert [ev.truth(CF("ILMC", y, Neg(A)), w) for w in worlds] == [False, False, True, False]
    # Under ILC the two nested counterfactuals agree (strict collapse hides the difference).
    xc, yc = CF("ILC", A, B), CF("ILC", C, D)
    assert [ev.truth(CF("ILC", xc, C), w) for w in worlds] == [ev.truth(CF("ILC", yc, C), w) for w in worlds]


def test_logic_failures_helper_matches_the_f3_identity_verdict():
    """Reading I fails identity on the F3 frame; the settled clauses do not."""
    from model_checker.theory_lib.logos.subtheories.counterfactual.tests.witness_frames import frame_f3
    frame, interp = frame_f3()
    interp_abcd = type(interp)({**interp.letters, "C": interp["B"], "D": interp["A"]})
    assert logic_failures("I", frame, interp_abcd, A, B, C, D)["identity"] is True
    for key in ("ILC", "ILMC", "MC"):
        assert logic_failures(key, frame, interp_abcd, A, B, C, D)["identity"] is False
