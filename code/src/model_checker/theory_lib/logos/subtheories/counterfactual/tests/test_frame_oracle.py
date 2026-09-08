"""Frame-oracle tests: primitives, the F3 refutation frame, and the enumerator.

The F3 frame is the eight-atom, four-world frame from the provenance research
(report ``02_context-free-counterfactual-verifiers.md``, finding F3.1) that
refutes Reading I (imposition-local verification) on four counts.  Each F3.3
claim gets its own test whose docstring records the mechanical verdict.
"""

import pytest

from model_checker.theory_lib.logos.subtheories.counterfactual.frame_oracle import (
    ALL_KEYS,
    CANDIDATE_KEYS,
    CF,
    Atom,
    Evaluator,
    Frame,
    Interpretation,
    PROPERTY_NAMES,
    antichains,
    enumerate_frames,
    enumerate_letter_propositions,
    enumerate_models,
    fusion_closure,
    is_fusion_closed,
    is_part_of,
    letter_constraints_hold,
    measure,
    minimal_elements,
)

F3_ATOMS = ["a", "a'", "p", "p'", "q", "q'", "b", "b'"]


def f3_frame():
    """Report 02's F3.1 frame: worlds w0..w3 over eight atoms."""
    names = F3_ATOMS
    bit = {name: 1 << i for i, name in enumerate(names)}

    def st(*atoms):
        s = 0
        for a in atoms:
            s |= bit[a]
        return s

    w0 = st("a'", "p", "p'", "q", "q'", "b")
    w1 = st("a", "p", "p'", "b")
    w2 = st("a", "q", "q'", "b")
    w3 = st("a", "p", "q", "b'")
    frame = Frame.from_worlds(8, [w0, w1, w2, w3], names)
    interp = Interpretation({
        "A": ({st("a")}, {st("a'")}),
        "B": ({st("b")}, {st("b'")}),
    })
    return frame, interp, (w0, w1, w2, w3)


A, B = Atom("A"), Atom("B")


@pytest.fixture(scope="module")
def f3():
    return f3_frame()


# ---------------------------------------------------------------------------
# Primitives
# ---------------------------------------------------------------------------

def test_fusion_closure_and_minimal_elements():
    assert fusion_closure({1, 2}) == {1, 2, 3}
    assert fusion_closure({1, 2, 4}) == {1, 2, 3, 4, 5, 6, 7}
    assert is_fusion_closed({1, 2}) == (1, 2) or is_fusion_closed({1, 2}) == (2, 1)
    assert is_fusion_closed({1, 2, 3}) is None
    assert minimal_elements({3, 1, 7, 5}) == {1}
    assert minimal_elements({3, 5}) == {3, 5}


def test_frame_rejects_non_downward_closed_possibility():
    with pytest.raises(ValueError):
        Frame(2, {0, 3})


def test_frame_worlds_are_maximal_possible_states():
    frame = Frame(2, {0, 1, 2})
    assert frame.worlds == {1, 2}
    frame = Frame(2, {0, 1, 2, 3})
    assert frame.worlds == {3}


def test_max_compatible_parts_and_alternatives_on_two_atoms():
    # Worlds a and b are incompatible; imposing a on world b yields world a.
    frame = Frame(2, {0, 1, 2})
    assert frame.max_compatible_parts(2, 1) == {0}
    assert frame.alternatives(2, 1) == {1}
    assert frame.alternatives(1, 1) == {1}
    # Imposing an impossible state yields no alternatives.
    assert frame.alternatives(1, 3) == set()


# ---------------------------------------------------------------------------
# F3.1: the frame
# ---------------------------------------------------------------------------

def test_f3_frame_has_exactly_the_declared_worlds(f3):
    """Scope hypothesis: the four declared worlds are exactly the maximal possible states."""
    frame, _, worlds = f3
    assert frame.size == 256
    assert frame.worlds == set(worlds)
    assert all(frame.is_possible(s) for s in worlds)


def test_f3_letters_satisfy_the_logos_letter_constraints(f3):
    frame, interp, _ = f3
    for name in ("A", "B"):
        v, f = interp[name]
        assert letter_constraints_hold(frame, v, f)


# ---------------------------------------------------------------------------
# F3.2: the facts
# ---------------------------------------------------------------------------

def test_f3_2_max_compatible_parts_of_w0(f3):
    frame, _, (w0, _, _, _) = f3
    a = frame.state("a")
    expected = {frame.state("p", "p'", "b"), frame.state("q", "q'", "b"), frame.state("p", "q")}
    assert frame.max_compatible_parts(w0, a) == expected


def test_f3_2_truth_values_at_the_four_worlds(f3):
    frame, interp, (w0, w1, w2, w3) = f3
    ev = Evaluator(frame, interp)
    assert ev.cf_true(A, B, w0) is False
    assert ev.cf_true(A, B, w1) is True
    assert ev.cf_true(A, B, w2) is True
    assert ev.cf_true(A, B, w3) is False
    assert ev.cf_false(A, B, w0) is True
    assert ev.cf_false(A, B, w3) is True


# ---------------------------------------------------------------------------
# F3.3: the four failures of Reading I
# ---------------------------------------------------------------------------

def test_f3_3_1_reading_i_is_not_closed_under_fusion(f3):
    """Verdict: CONFIRMED. {p,p'} and {q,q'} verify, their fusion does not."""
    frame, interp, _ = f3
    ev = Evaluator(frame, interp)
    v, _ = ev.proposition(CF("I", A, B))
    s1, s2 = frame.state("p", "p'"), frame.state("q", "q'")
    assert s1 in v and s2 in v
    assert (s1 | s2) not in v
    assert frame.max_compatible_parts(s1 | s2, frame.state("a")) == {
        s1, s2, frame.state("p", "q")
    }
    record = measure("I", A, B, frame, interp)
    assert record["closure_V"] is False


def test_f3_3_2_reading_i_verifier_and_falsifier_are_compatible(f3):
    """Verdict: CONFIRMED. {p,p'} verifies, {q} falsifies, and {p,p',q} is possible."""
    frame, interp, _ = f3
    ev = Evaluator(frame, interp)
    v, f = ev.proposition(CF("I", A, B))
    s1, t = frame.state("p", "p'"), frame.state("q")
    assert s1 in v and t in f
    assert frame.compatible(s1, t)
    record = measure("I", A, B, frame, interp)
    assert record["exclusive_compat"] is False
    # The weaker exclusivity (no possible state in both sets) is what remains.
    assert record["exclusive_possible"] is True


def test_f3_3_3_reading_i_verifier_sits_inside_a_false_world(f3):
    """Verdict: CONFIRMED, and strengthened on two counts the report does not mention.

    {p,p'} is part of w0, where the counterfactual is false, so the bridge
    gluts at w0 as the report says.  The oracle also finds that the *null
    state* falsifies under Reading I: imposing {a} on the null state reaches
    every world containing {a}, including w3 where B is false.  Since the
    null state is part of every world, every world that contains any
    I-verifier gluts -- w0, w1 and w2 -- and bridge soundness fails in the
    falsifier polarity too ({q} falsifies and sits inside the true world w2).
    In general the null state verifies under Reading I iff the strict
    conditional (every world containing an A-verifier makes B true) holds,
    and falsifies iff it fails.
    """
    frame, interp, (w0, w1, w2, w3) = f3
    ev = Evaluator(frame, interp)
    v, f = ev.proposition(CF("I", A, B))
    s1, t = frame.state("p", "p'"), frame.state("q")
    assert is_part_of(s1, w0)
    assert not ev.cf_true(A, B, w0)
    assert is_part_of(t, w2) and t in f
    assert ev.cf_true(A, B, w2)
    assert 0 in f and 0 not in v
    assert frame.alternatives(0, frame.state("a")) == {w1, w2, w3}
    record = measure("I", A, B, frame, interp)
    assert record["bridge_sound_V"] is False
    assert record["bridge_sound_F"] is False
    assert record["bridge_glut"] is True
    assert set(record["bridge_glut_worlds"]) == {frame.fmt(w0), frame.fmt(w1), frame.fmt(w2)}


def test_f3_3_4_identity_fails_at_a_reading_i_antecedent(f3):
    """Verdict: CONFIRMED. (A □→ B) □→ (A □→ B) is false at w0 when the antecedent's verifiers are V_I."""
    frame, interp, (w0, w1, w2, w3) = f3
    ev = Evaluator(frame, interp)
    inner = CF("I", A, B)
    identity = CF("I", inner, inner)
    assert ev.truth(identity, w0) is False
    assert ev.falsity(identity, w0) is True
    # The witness is {p,p'} imposed on w0, whose only alternative is w0 itself.
    s1 = frame.state("p", "p'")
    assert frame.alternatives(w0, s1) == {w0}
    # By contrast the identity holds under the settler clauses at every world.
    for key in ("W", "L", "M", "MC", "IL"):
        inner_k = CF(key, A, B)
        for w in (w0, w1, w2, w3):
            assert ev.truth(CF(key, inner_k, inner_k), w), (key, frame.fmt(w))


def test_f3_5_impossible_states_are_not_vacuous_verifiers_under_reading_i(f3):
    """Verdict: CONFIRMED. {a,a'} is impossible yet constrained by the clause, and fails it."""
    frame, interp, _ = f3
    ev = Evaluator(frame, interp)
    v, _ = ev.proposition(CF("I", A, B))
    aa = frame.state("a", "a'")
    assert not frame.is_possible(aa)
    assert frame.alternatives(aa, frame.state("a")) != set()
    assert aa not in v
    record = measure("I", A, B, frame, interp)
    assert record["impossible_vacuous_V"] is False
    assert record["impossible_harmless_V"] is True


# ---------------------------------------------------------------------------
# F5 sanity check and the cross-candidate table
# ---------------------------------------------------------------------------

def test_f5_reading_w_sets_on_the_f3_frame(f3):
    frame, interp, (w0, w1, w2, w3) = f3
    ev = Evaluator(frame, interp)
    v, f = ev.proposition(CF("W", A, B))
    assert v == {w1, w2, w1 | w2}
    assert f == {w0, w3, w0 | w3}
    record = measure("W", A, B, frame, interp)
    for prop in PROPERTY_NAMES:
        if prop.startswith("impossible_vacuous"):
            assert record[prop] is False
        else:
            assert record[prop] is True, prop
    assert record["proper_possible_V"] == []


def f3_candidate_table():
    """The full measurement record of every clause on the F3 frame."""
    frame, interp, (w0, _, _, _) = f3_frame()
    table = {}
    for key in ALL_KEYS:
        eval_world = w0 if key == "SQ" else None
        table[key] = measure(key, A, B, frame, interp, eval_world)
    return table


def test_cross_candidate_table_on_the_f3_frame(f3):
    frame, interp, (w0, w1, w2, w3) = f3
    table = f3_candidate_table()
    assert set(table) == set(ALL_KEYS)
    for key, record in table.items():
        assert record["true_worlds"] == frame.fmt_set({w1, w2})
        assert record["bivalent_at_worlds"] is True
    # Settler-based clauses are sound and sufficient at the bridge.
    for key in ("W", "L", "M", "MC", "IL"):
        assert table[key]["bridge_sound_V"] and table[key]["bridge_sound_F"], key
        assert table[key]["bridge_sufficient_V"] and table[key]["bridge_sufficient_F"], key
        assert table[key]["exclusive_compat"], key
        assert table[key]["exhaustive"], key
    # L is upward closed, so it is closed under fusion and contains every impossible state.
    assert table["L"]["closure_V"] and table["L"]["impossible_vacuous_V"]
    # The desideratum: which clauses have possible verifiers properly below a world?
    for key in ("L", "M", "MC"):
        assert table[key]["proper_possible_V"], key


# ---------------------------------------------------------------------------
# Enumerator
# ---------------------------------------------------------------------------

def test_antichains_on_two_atoms():
    found = set(antichains([1, 2, 3]))
    assert found == {frozenset({1}), frozenset({2}), frozenset({3}), frozenset({1, 2})}


def test_enumerated_frames_are_well_formed():
    frames = list(enumerate_frames(3))
    assert len(frames) == 18
    for frame in frames:
        for s in frame.possible:
            assert all(t in frame.possible for t in frame.states if is_part_of(t, s))
        for w in frame.worlds:
            assert not any(w != v and is_part_of(w, v) for v in frame.possible)


def test_enumerated_letter_propositions_satisfy_the_constraints():
    frame = Frame(2, {0, 1, 2})
    props = enumerate_letter_propositions(frame)
    assert props
    for v, f in props:
        assert letter_constraints_hold(frame, v, f)
    assert (frozenset({1}), frozenset({2})) in props


def test_enumerate_models_is_reproducible_when_sampled():
    first = [(fr.worlds, tuple(sorted(it.letters.items()))) for fr, it in enumerate_models(3, limit=5, seed=7)]
    second = [(fr.worlds, tuple(sorted(it.letters.items()))) for fr, it in enumerate_models(3, limit=5, seed=7)]
    assert first == second
    assert len(first) == 5


def test_every_candidate_measures_on_every_small_model():
    count = 0
    for frame, interp in enumerate_models(2):
        for key in CANDIDATE_KEYS:
            record = measure(key, A, B, frame, interp)
            assert record["bivalent_at_worlds"]
        count += 1
    assert count > 0
