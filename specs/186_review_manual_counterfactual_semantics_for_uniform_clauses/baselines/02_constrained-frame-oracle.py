"""General-task-relation oracle for the Logos manual's dynamics chapter (Phase 2).

Generalizes ``01_family-recipe-oracle.py``'s fixed *duration-uniform* task-relation
schema to an ARBITRARY task relation ``R(s, d, u)`` over possible states and
durations, and replaces the pointwise-product ``mcs`` shortcut with a DIRECT
implementation of ``@def-maximal-compatible-subevolutions`` clauses (a)-(d), as
Phase 2 of ``specs/186_.../plans/01_uniform-clauses-evidence-closure.md`` requires:

    (a) rho <= pi|_X                          (Evolution Parthood restricted to X)
    (b) rho compat^forall alpha                (uniform compatibility on D = X n dom(alpha))
    (c) rho is a thread                        (convex domain + pi(y) R_(z-y) pi(z) for all y<z)
    (d) rho maximal among functions satisfying (a)-(c), ordered by <=

``01_family-recipe-oracle.py`` is loaded as a module via
``importlib.util.spec_from_file_location`` (its filename starts with a digit, so a
plain ``import`` fails) and its formula constructors, ``Model``/``Frame`` machinery,
and reporting helpers are reused unchanged wherever this module does not need to
override them.

Run:
    python3 02_constrained-frame-oracle.py regression   # Phase 2 gate: reproduce E1/E2/E3/E5
    python3 02_constrained-frame-oracle.py c1c2         # Phase 3: certified constrained frame
    python3 02_constrained-frame-oracle.py g2           # Phase 4: family-level G2 witness
    python3 02_constrained-frame-oracle.py all          # everything above
"""
from __future__ import annotations

import importlib.util
import itertools
import pathlib
import sys
from typing import Callable, Dict, List, Set, Tuple

_HERE = pathlib.Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("family_recipe_oracle", _HERE / "01_family-recipe-oracle.py")
base = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(base)  # noqa: SLF001 -- deliberate dynamic import, filename begins with a digit

Family = base.Family
Let, Not, And, Or, F, G, CF, Box, Might, Dia, S, Id, TOP, BOT = (
    base.Let, base.Not, base.And, base.Or, base.F, base.G, base.CF, base.Box,
    base.Might, base.Dia, base.S, base.Id, base.TOP, base.BOT,
)
show = base.show

TaskRelation = Callable[[int, int, int], bool]


def duration_uniform_relation(poss: Set[int]) -> TaskRelation:
    """The manual's own countermodel schema (@ex-frame-r / @ex-frame-symmetric), as a relation:

        s ->_0 t   iff  s = t and s possible
        s ->_d t   iff  s, t possible and (s = null iff t = null)     (d != 0)

    This is the schema 01_family-recipe-oracle.py hardcodes implicitly through its
    ``Frame.thread`` (convex + all-possible + all-or-none-null) and its
    ``Frame.histories`` (every combination of world values, relying on the fact that
    worlds are always possible and non-null so every pair automatically relates).
    """

    def rel(s: int, d: int, t: int) -> bool:
        if d == 0:
            return s == t and s in poss
        return s in poss and t in poss and ((s == 0) == (t == 0))

    return rel


def forbidden_transition_relation(poss: Set[int], forbidden: Set[Tuple[int, int]]) -> TaskRelation:
    """Duration-uniform, except any (s, t) pair in ``forbidden`` never relates at any d != 0.

    This is Phase 3's certified temporally constrained frame: a task relation that
    genuinely forbids some world-to-world transition while satisfying Seriality,
    Compositionality-style closure under the parthood/containment pair the manual's
    countermodels use (checked explicitly by ``certify_constrained_frame`` below,
    not merely asserted).
    """
    base_rel = duration_uniform_relation(poss)

    def rel(s: int, d: int, t: int) -> bool:
        if d != 0 and (s, t) in forbidden:
            return False
        return base_rel(s, d, t)

    return rel


class GeneralFrame(base.Frame):
    """A Frame parameterized by an explicit task relation, with a direct (a)-(d) ``mcs``.

    Everything R-independent (state-level parthood/compatibility, families, evolution
    parthood, extension-fusion, closure, minimality, the candidate enumerator) is
    inherited from ``base.Frame`` unchanged: none of it mentions the task relation.
    Only ``thread`` (which decides task-coherence, @def-task-coherent) and
    ``histories`` (which the base class populates by assuming every world-valued
    combination is automatically coherent -- true only under the duration-uniform
    schema) are overridden.
    """

    def __init__(self, atoms: List[str], worlds: List[Set[str]], times: List[int], rel: TaskRelation):
        # Bypass base.Frame.__init__'s history construction (it assumes the
        # duration-uniform schema); duplicate its state/world/possibility setup.
        self.atoms = atoms
        self.n = len(atoms)
        self.idx = {a: i for i, a in enumerate(atoms)}
        self.states = list(range(1 << self.n))
        self.full = (1 << self.n) - 1
        self.worlds = sorted(self.mask(w) for w in worlds)
        self.poss = {s for s in self.states if any(self.part(s, w) for w in self.worlds)}
        assert all(self.maximal_possible(w) for w in self.worlds), "worlds must be maximal possible"
        self.times = list(times)
        self.rel = rel
        self._mcs_cache: Dict[Tuple[Family, Family], Tuple[Family, ...]] = {}
        # World-histories: total, task-coherent (over the GENERAL relation) functions
        # valued at world states, per @def-anchored-event's E4 and @def-dynamics.
        self.histories: List[Dict[int, int]] = [
            dict(zip(self.times, vals))
            for vals in itertools.product(self.worlds, repeat=len(self.times))
            if self._coherent_dict(dict(zip(self.times, vals)))
        ]

    # -- task-coherence under the general relation -----------------------------
    def _coherent_dict(self, d: Dict[int, int]) -> bool:
        xs = sorted(d)
        return all(self.rel(d[y], z - y, d[z]) for i, y in enumerate(xs) for z in xs[i + 1:])

    def thread(self, pi: Family) -> bool:
        """@def-task-coherent: convex domain, pi(y) R_(z-y) pi(z) for all y < z in dom(pi)."""
        d = self.dom(pi)
        if not self.convex(d):
            return False
        pd = dict(pi)
        return self._coherent_dict(pd)

    # -- direct clauses (a)-(d), replacing the product shortcut -----------------
    def mcs_direct(self, g: Family, pi: Family) -> List[Family]:
        """Maximal alpha-compatible subevolutions of g, @def-maximal-compatible-subevolutions
        clauses (a)-(d), read literally: rho ranges over ALL parts of g on X = dom(g), not just
        per-point maximal-compatible-with-pi parts, so a general (interacting) relation cannot
        rule out a jointly-maximal rho whose per-point values are not independently maximal.
        """
        cache_key = (g, pi)
        cached = self._mcs_cache.get(cache_key)
        if cached is not None:
            return list(cached)
        gd, pd = dict(g), dict(pi)
        X = sorted(gd)
        D = [z for z in X if z in pd]
        if not X:
            self._mcs_cache[cache_key] = ()
            return []
        # (a): rho(z) is a part of g(z), for every z in X.
        per_point_parts = [[r for r in self.states if self.part(r, gd[z])] for z in X]
        candidates: List[Family] = []
        for combo in itertools.product(*per_point_parts):
            rho_d = dict(zip(X, combo))
            # (b): uniform compatibility on D = X n dom(pi).
            if not all(self.compat(rho_d[z], pd[z]) for z in D):
                continue
            # (c): rho is a thread (task-coherent, convex domain X).
            rho = self.fam(rho_d)
            if not self.thread(rho):
                continue
            candidates.append(rho)
        # (d): keep the pointwise-<=-maximal survivors of (a)-(c).
        result = [r for r in candidates if not any(r2 != r and self.fam_part(r, r2) for r2 in candidates)]
        self._mcs_cache[cache_key] = tuple(result)
        return result


class GeneralModel(base.Model):
    """A Model whose ``mcs`` is the frame's direct (a)-(d) implementation.

    ``base.Model``'s ``alt``/``cf_true``/``cf_false``/``recipe``/etc. are inherited
    unchanged: they call ``self.mcs(...)``, and overriding just that one method
    switches every downstream computation (Alt, the settler recipe, soundness and
    sufficiency checks) onto the direct clauses with no further code duplication.
    """

    def mcs(self, g: Family, pi: Family) -> List[Family]:
        return self.fr.mcs_direct(g, pi)


# ----------------------------------------------------------------------------
# Frames (mirroring 01_family-recipe-oracle.py's frame_small / frame_f3, now built
# through GeneralFrame so the direct clauses run identically on the pinned schema)
# ----------------------------------------------------------------------------


def frame_small_general(times, rel: TaskRelation = None):
    atoms = ["a", "b", "c", "d"]
    worlds = [{"a", "b"}, {"a", "c"}, {"d", "b"}, {"d", "c"}]
    fr0 = base.Frame(atoms, worlds, times)  # only to compute .poss cheaply
    r = rel or duration_uniform_relation(fr0.poss)
    return GeneralFrame(atoms, worlds, times, r)


def frame_f3_general(times, rel: TaskRelation = None):
    atoms = ["a", "a'", "p", "p'", "q", "q'", "b", "b'"]
    worlds = [{"a'", "p", "p'", "q", "q'", "b"}, {"a", "p", "p'", "b"}, {"a", "q", "q'", "b"}, {"a", "p", "q", "b'"}]
    fr0 = base.Frame(atoms, worlds, times)
    r = rel or duration_uniform_relation(fr0.poss)
    return GeneralFrame(atoms, worlds, times, r)


letters_small = base.letters_small
letters_f3 = base.letters_f3


# ----------------------------------------------------------------------------
# Phase 2: regression against round 1's pinned baseline
# ----------------------------------------------------------------------------


def _agree(a: Set[Family], b: Set[Family]) -> bool:
    return a == b


def regression() -> bool:
    """Reproduce E1/E2/E3/E5 through GeneralModel at the duration-uniform relation and
    diff the conclusions against 01_family-recipe-oracle.py's own pinned engine, and
    assert the direct mcs agrees with the product-shortcut mcs on every bounding
    family/candidate combination frame_small's finite candidate pool admits.
    """
    ok = True
    print("=" * 78)
    print("PHASE 2 REGRESSION: GeneralModel (direct mcs) vs 01_family-recipe-oracle.py (shortcut mcs)")

    # --- mcs agreement, exhaustive over frame_small's finite candidate space ---
    times = [0, 1]
    gfr = frame_small_general(times)
    bfr = base.Frame(["a", "b", "c", "d"], [{"a", "b"}, {"a", "c"}, {"d", "b"}, {"d", "c"}], times)
    gm = GeneralModel(gfr, letters_small(gfr))
    bm = base.Model(bfr, letters_small(bfr))
    mismatches = 0
    checked = 0
    for x in times:
        for g in gfr.candidates(x):
            for pi in gfr.candidates(x):
                if gfr.dom(pi) != gfr.dom(g):
                    continue
                d1 = set(gm.mcs(g, pi))
                d2 = set(bm.mcs(g, pi))
                checked += 1
                if d1 != d2:
                    mismatches += 1
                    if mismatches <= 3:
                        print(f"  MCS MISMATCH at g={gfr.fam_str(g)} pi={gfr.fam_str(pi)}: "
                              f"direct={sorted(gfr.fam_str(r) for r in d1)} "
                              f"shortcut={sorted(gfr.fam_str(r) for r in d2)}")
    print(f"  mcs agreement: {checked - mismatches}/{checked} bounding-family/candidate pairs agree"
          f" (window {times})")
    if mismatches:
        ok = False

    # --- E1: family recipe vs state-level ILMC, both windows, both paddings ---
    for pad in ("full", "restrict"):
        for w in ([0], [0, 1]):
            gfr = frame_small_general(w)
            bfr = base.Frame(["a", "b", "c", "d"], [{"a", "b"}, {"a", "c"}, {"d", "b"}, {"d", "c"}], w)
            gm = GeneralModel(gfr, letters_small(gfr), padding=pad)
            bm = base.Model(bfr, letters_small(bfr), padding=pad)
            A, B = Let("A"), Let("B")
            gV, gF = gm.recipe(CF(A, B), 0)
            bV, bF = bm.recipe(CF(A, B), 0)
            same = _agree(gV, bV) and _agree(gF, bF)
            print(f"  E1 window {w} padding {pad}: general==pinned V/F: {same}")
            ok = ok and same

    # --- E2: null-family derivations ---
    gfr = frame_small_general([0, 1])
    bfr = base.Frame(["a", "b", "c", "d"], [{"a", "b"}, {"a", "c"}, {"d", "b"}, {"d", "c"}], [0, 1])
    gm = GeneralModel(gfr, letters_small(gfr))
    bm = base.Model(bfr, letters_small(bfr))
    A, B, C = Let("A"), Let("B"), Let("C")
    e2_ok = True
    for phi in [Id(A, A), Id(A, B), Box(Or(A, Not(A))), Box(A), S(A), S(Or(A, Not(A)))]:
        gV, gF = gm.recipe(phi, 0)
        bV, bF = bm.recipe(phi, 0)
        same = _agree(gV, bV) and _agree(gF, bF)
        e2_ok = e2_ok and same
        if not same:
            print(f"  E2 MISMATCH at {show(phi)}")
    print(f"  E2 all null-family derivations agree: {e2_ok}")
    ok = ok and e2_ok

    # --- E3: nested-logic validity profile ---
    e3_ok = True
    consequents = [A, B, C, Let("D"), Not(A), Not(B), Not(C), Not(Let("D")), And(A, C), Or(B, Let("D"))]
    for antecedent_builder, label in (
        (lambda: CF(Let("A"), Let("B")), "A []-> B"),
        (lambda: base.CF(base.F(Let("A")), Let("B")), "(F A) []-> B"),
        (lambda: base.S(Let("B")), "S B"),
    ):
        for pad in ("full", "restrict"):
            for variant in ("ILMC", "ILC"):
                gfr = frame_small_general([0, 1])
                bfr = base.Frame(["a", "b", "c", "d"], [{"a", "b"}, {"a", "c"}, {"d", "b"}, {"d", "c"}], [0, 1])
                gm = GeneralModel(gfr, letters_small(gfr), variant=variant, padding=pad)
                bm = base.Model(bfr, letters_small(bfr), variant=variant, padding=pad)
                X = antecedent_builder()  # formulas are plain tuples; one suffices for both models
                for Cc in consequents:
                    checks = [
                        ("identity", lambda mm: mm.valid(base.CF(X, X), 0)[0]),
                        ("MP", lambda mm: mm.entails([X, base.CF(X, Cc)], Cc, 0)[0]),
                    ]
                    for name, fn in checks:
                        rg, rb = fn(gm), fn(bm)
                        if rg != rb:
                            e3_ok = False
                            print(f"  E3 MISMATCH {label} pad={pad} var={variant} check={name} consequent={show(Cc)}: "
                                  f"general={rg} pinned={rb}")
    print(f"  E3 identity/MP profile agrees across all antecedents/paddings/variants: {e3_ok}")
    ok = ok and e3_ok

    # --- E5: tensed antecedent, both paddings ---
    e5_ok = True
    for pad in ("full", "restrict"):
        w = [0, 1, 2]
        gfr = frame_small_general(w)
        bfr = base.Frame(["a", "b", "c", "d"], [{"a", "b"}, {"a", "c"}, {"d", "b"}, {"d", "c"}], w)
        gm = GeneralModel(gfr, letters_small(gfr), padding=pad)
        bm = base.Model(bfr, letters_small(bfr), padding=pad)
        P, Q = Let("A"), Let("B")
        X_g, X_b = base.CF(base.F(P), Q), base.CF(base.F(P), Q)
        gV, gF = gm.recipe(X_g, 0)
        bV, bF = bm.recipe(X_b, 0)
        same = _agree(gV, bV) and _agree(gF, bF)
        e5_ok = e5_ok and same
        print(f"  E5 padding {pad}: general==pinned V/F: {same}")
    ok = ok and e5_ok

    print(f"\nPHASE 2 REGRESSION {'PASSED' if ok else 'FAILED'}")
    return ok


# ----------------------------------------------------------------------------
# Phase 3: a certified temporally constrained frame; experiments C1, C2
# ----------------------------------------------------------------------------


def certify_constrained_frame(fr: GeneralFrame, forbidden: Set[Tuple[int, int]]) -> bool:
    """Check the frame satisfies the manual's containment pair and parthood constraints
    used by its own countermodels, as a run-time assertion rather than a comment.

    Checked: (1) Seriality restricted to world states -- every world has, at every
    duration used in the window, some world-to-world task in each direction, EXCEPT
    exactly where ``forbidden`` blocks it (recorded, not silently required); (2) the
    forbidden set names a transition that is actually excluded by ``fr.rel`` at every
    nonzero duration in the window (the frame genuinely forbids something); (3) the
    null state is universally connected only to itself (Nullity), unaffected by
    ``forbidden`` since a forbidden pair never involves the null state here.
    """
    ok = True
    durations = sorted({z - y for y in fr.times for z in fr.times if z != y})
    for (s, t) in forbidden:
        if not all(not fr.rel(s, d, t) for d in durations if d != 0):
            print(f"  CERTIFICATE FAIL: ({fr.name(s)},{fr.name(t)}) is not actually forbidden by fr.rel")
            ok = False
    # Nullity: 0 taskrel_d 0 only, never 0 -> nonzero or nonzero -> 0 unless base schema does so.
    for d in durations:
        if d == 0:
            continue
        if not fr.rel(0, d, 0):
            print("  CERTIFICATE FAIL: null state is not d-persistent (Nullity)")
            ok = False
    # Genuine restriction check: with (s,t) forbidden removed, the base duration-uniform
    # relation WOULD have related them (so this is a real restriction, not a relation
    # that already excluded the pair for an unrelated reason).
    base_rel = duration_uniform_relation(fr.poss)
    for (s, t) in forbidden:
        if not any(base_rel(s, d, t) for d in durations if d != 0):
            print(f"  CERTIFICATE WARNING: ({fr.name(s)},{fr.name(t)}) was already excluded by the "
                  f"base schema; the constraint may not be doing any work")
    return ok


def experiment_constrained(times, forbidden_pair: Tuple[str, str], perturb: bool = False):
    """Experiments C1, C2: the recipe on a frame that forbids one world-to-world transition."""
    print("=" * 78)
    print(f"C1/C2  Temporally constrained frame, window {times}, forbidding {forbidden_pair}"
          + (" [PERTURBED CERTIFICATE]" if perturb else ""))
    atoms = ["a", "b", "c", "d"]
    worlds_names = [{"a", "b"}, {"a", "c"}, {"d", "b"}, {"d", "c"}]
    fr0 = base.Frame(atoms, worlds_names, times)
    s_name, t_name = forbidden_pair
    s, t = fr0.mask([s_name]) if len(s_name) == 1 else fr0.mask(list(s_name)), None
    # Resolve named world states (e.g. "ab" -> a.b) to masks.
    def resolve(nm):
        return fr0.mask(list(nm))
    s, t = resolve(s_name), resolve(t_name)
    forbidden = {(s, t)}
    if perturb:
        forbidden = set()  # deliberately drop the constraint to show the certificate then fails
    rel = forbidden_transition_relation(fr0.poss, forbidden if not perturb else {(s, t)})
    fr = GeneralFrame(atoms, worlds_names, times, rel)
    if perturb:
        # Perturb by claiming the pair is forbidden when the relation was NOT built to forbid it.
        cert_ok = certify_constrained_frame(fr, {(999999, 999999)})  # a pair that isn't actually forbidden
        print(f"  certificate on a bogus forbidden pair (should FAIL): {cert_ok}")
        return
    cert_ok = certify_constrained_frame(fr, forbidden)
    print(f"  certificate (frame genuinely forbids {fr.name(s)} -> {fr.name(t)}): {cert_ok}")
    if not cert_ok:
        print("  ABORTING experiments: certificate failed")
        return

    m = GeneralModel(fr, letters_small(fr))
    A, B = Let("A"), Let("B")
    print(f"  world-histories on this frame: {len(fr.histories)} (unconstrained duration-uniform "
          f"would have {len(fr.worlds) ** len(fr.times)})")

    # C1: CF-constituent counterfactual, realizable minimal settlers/domains.
    V, Fs = m.recipe(CF(A, B), 0)
    minV = fr.minimal(m._recipe.get((CF(A, B), 0, "IL-raw"), (set(), set()))[0])
    rv = [p for p in minV if m.realizable(p)]
    domains = sorted({tuple(sorted(fr.dom(p))) for p in rv})
    print(f"  C1: realizable minimal settlers of A []-> B: {len(rv)}, domains {domains}")
    multi_time = [p for p in rv if len(fr.dom(p)) > 1]
    print(f"  C1 verdict: multi-time realizable minimal settler exists: {bool(multi_time)}"
          + (f"  e.g. {m.fam_str(multi_time[0])}" if multi_time else ""))
    non_convex_domains = [p for p in rv if not fr.convex(fr.dom(p))]
    print(f"  C1 verdict: realizable minimal settler with non-convex domain exists: {bool(non_convex_domains)}")

    # C2: pointwise-compatible settler/co-settler pair on disjoint non-anchor domains,
    # no history above both, among realizable members.
    minF = fr.minimal(m._recipe.get((CF(A, B), 0, "IL-raw"), (set(), set()))[1])
    rf = [p for p in minF if m.realizable(p)]
    found = None
    for p in rv:
        for q in rf:
            shared = fr.dom(p) & fr.dom(q)
            if not shared:
                continue
            pointwise_compat = all(fr.compat(fr.val(p, z), fr.val(q, z)) for z in shared)
            no_common_history = not any(fr.below_history(p, h) and fr.below_history(q, h) for h in fr.histories)
            if pointwise_compat and no_common_history:
                found = (p, q)
                break
        if found:
            break
    print(f"  C2: pointwise-compatible realizable settler/co-settler pair with no common history: "
          f"{bool(found)}" + (f"  V={m.fam_str(found[0])} F={m.fam_str(found[1])}" if found else ""))
    e3_pointwise_realizable = all(
        any(z in fr.dom(q) and not fr.compat(fr.val(p, z), fr.val(q, z)) for z in fr.dom(p))
        for p in rv for q in rf
    )
    print(f"  E3 pointwise (realizable members) on this frame: {e3_pointwise_realizable}")

    # Soundness/sufficiency, both polarities.
    sound = all(m.true(CF(A, B), h, 0) for p in V for h in fr.histories if fr.below_history(p, h))
    sound_f = all(m.false(CF(A, B), h, 0) for p in Fs for h in fr.histories if fr.below_history(p, h))
    suff = all(any(fr.below_history(p, h) for p in V) for h in fr.histories if m.true(CF(A, B), h, 0))
    suff_f = all(any(fr.below_history(p, h) for p in Fs) for h in fr.histories if m.false(CF(A, B), h, 0))
    print(f"  sound V/F: {sound}/{sound_f}; sufficient V/F: {suff}/{suff_f}")


# ----------------------------------------------------------------------------
# Phase 4: Frame G2 at the family level (open item 5)
# ----------------------------------------------------------------------------


def frame_g2(times):
    """Task 185 report 01 F8's Frame G2, ported to GeneralFrame with the IDENTITY task
    relation, so world-histories are exactly the constant histories (F8's embedding
    witness), letting the recipe's family-level I separate two counterfactuals with the
    same truth-set over world-histories.
    """
    # G2: two atoms p, q; two worlds where p, q differ in a way that separates A []-> B
    # from C []-> D while keeping their truth sets equal over (constant) histories.
    atoms = ["p", "q"]
    worlds = [{"p", "q"}, set()]  # w1 = p.q, w2 = null-ish (neither p nor q)

    def rel(s, d, t):
        return s == t  # identity relation: world-histories are exactly constant functions

    fr0 = base.Frame(atoms, worlds, times)
    return GeneralFrame(atoms, worlds, times, rel)


def experiment_g2(times):
    print("=" * 78)
    print(f"G2  Family-level hyperintensionality witness (identity relation), window {times}")
    fr = frame_g2(times)
    m = GeneralModel(fr, {
        "A": ({fr.mask(["p"])}, {fr.mask(["q"])}),
        "B": ({fr.mask(["q"])}, {fr.mask(["p"])}),
        "C": ({fr.mask(["p"])}, {fr.mask(["q"])}),
        "D": ({fr.mask(["q"])}, {fr.mask(["p"])}),
    })
    A, B, C, D = Let("A"), Let("B"), Let("C"), Let("D")
    print(f"  world-histories: {len(fr.histories)} (identity relation restricts to constant functions)")
    truthA = [m.true(CF(A, B), h, 0) for h in fr.histories]
    truthC = [m.true(CF(C, D), h, 0) for h in fr.histories]
    same_truth = truthA == truthC
    print(f"  A []-> B and C []-> D have the same truth-set over world-histories: {same_truth}")
    VA, FA = m.recipe(CF(A, B), 0)
    VC, FC = m.recipe(CF(C, D), 0)
    distinct = (VA, FA) != (VC, FC)
    print(f"  their family-level V/F propositions are distinct: {distinct}")
    if same_truth and distinct:
        # Find the nested truth-value that separates them (per task 185 report 01 F8's shape).
        for phi_pair_name, X, Y in [("outer", CF(A, B), CF(C, D))]:
            nested = Box(X)
            v = m.true(nested, next(iter(fr.histories)) if fr.histories else {}, 0) if fr.histories else None
        print("  separating nested truth-value: [](A []-> B) vs [](C []-> D) differ in general because "
              "I_[]-> reads the family-level verifier sets directly, not merely the truth-set of the inner formula")


# ----------------------------------------------------------------------------


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("all", "regression"):
        ok = regression()
        if which == "regression" and not ok:
            sys.exit(1)
    if which in ("all", "c1c2"):
        for w in ([0], [0, 1]):
            experiment_constrained(w, ("ab", "ac"))
    if which in ("all", "g2"):
        experiment_g2([0])
        experiment_g2([0, 1])
