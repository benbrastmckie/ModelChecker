"""Exploration of the exact-imposition verifier family for A []-> B.

Builds on the committed frame_oracle (candidates SQ, SQpy, I, W, L, M, MC, IL)
and adds:

Exact family (consequent VERIFIED by a designated part, s COMPOSED of those parts):
  XS   base = s itself:      s = ⊔ b(a,u),  u ∈ Alt(s,a), b ∈ V_B, b ⊑ u
  XSr  base = s, + remainder: s = ⊔ (b(a,u) ⊔ r(a,u)),  r ∈ [s]_a, a⊔r ⊑ u
  XPe  base = some world w ⊒ s: ∃w ⊒ s. s = ⊔_{(a,u)∈P(w)} b(a,u)
  XPer same with remainders r ∈ [w]_a
  XPa  base = every world w ⊒ s: ∀w ⊒ s. ∃ composition of s over P(w)
  XPar same with remainders
  XSx  existential: s = b for some b ∈ V_B, b ⊑ u, u ∈ Alt(s,a), some a
  XE   context-dependent baseline: base = evaluation world
Falsifier duals: s composed of B-falsifiers d ⊑ u over a NONEMPTY subset of the
alternatives (existential over alternatives), same base rule.

Settler-selection family (sound by construction; settler-hood stated via imposition
on every world containing s):
  SB   settler ∧ s ∈ closure(V_B)
  SAB  settler ∧ s ∈ closure(V_A ∪ V_B)
  SX   settler ∧ XPe
  SXr  settler ∧ XPer
  SXC  fusion closure of SX
  SR   settler ∧ ∃w ⊒ s. s = ⊔_a r_a, r_a ∈ [w]_a   (fusion of surviving remainders)
  ILC  fusion closure of IL
"""
import sys, itertools, json, random, time, collections
sys.path.insert(0, '/home/benjamin/Projects/ModelChecker/code/src')
import model_checker.theory_lib.logos.subtheories.counterfactual.frame_oracle as fo
from model_checker.theory_lib.logos.subtheories.counterfactual.frame_oracle import (
    Frame, Interpretation, Evaluator, CF, Atom, Neg, And, Or, Box, Top, Implies, Might,
    fusion_closure, is_part_of, measure, enumerate_models, minimal_elements,
)

X_KEYS = ("XS", "XSr", "XPe", "XPer", "XPa", "XPar", "XSx")
S_KEYS = ("SB", "SAB", "SX", "SXr", "SXC", "SR", "SRC", "ILC", "ILM", "ILMC")
BASE_KEYS = ("I", "W", "L", "M", "MC", "IL")
NEW_KEYS = X_KEYS + S_KEYS
ALL = BASE_KEYS + NEW_KEYS


def composable(s, slots):
    """Is s the fusion of one option per slot?  Options are pre-filtered to parts of s."""
    if any(not opts for opts in slots):
        return False
    if not slots:
        return s == 0
    slots = sorted(slots, key=len)
    seen = set()

    def rec(i, covered):
        if i == len(slots):
            return covered == s
        key = (i, covered)
        if key in seen:
            return False
        seen.add(key)
        for o in slots[i]:
            if rec(i + 1, covered | o):
                return True
        return False
    return rec(0, 0)


def composable_subset(s, slots):
    """Is s the fusion of one option each from a NONEMPTY subset of the slots?"""
    if s == 0:
        return any(0 in opts for opts in slots)
    opts_all = sorted({o for opts in slots for o in opts if is_part_of(o, s)})
    # need a selection from distinct slots; but since any option may be chosen from
    # whichever slot offers it, the subset condition reduces to: s is a fusion of
    # some nonempty set of offered options (each option tagged by its slot; a
    # state offered by two slots can be used once, which is enough).
    return s in fusion_closure(opts_all) if opts_all else False


class XEvaluator(Evaluator):
    def pairs(self, base, VA):
        return [(a, u) for a in VA for u in self.frame.alternatives(base, a)]

    def b_options(self, s, u, VB):
        return [b for b in VB if is_part_of(b, u) and is_part_of(b, s)]

    def br_options(self, s, base, a, u, VB):
        rs = [r for r in self.frame.max_compatible_parts(base, a) if is_part_of(a | r, u) and is_part_of(r, s)]
        return sorted({b | r for b in VB if is_part_of(b, u) and is_part_of(b, s) for r in rs})

    def comp_at(self, s, base, VA, VB, FB, with_r):
        """(verifies, falsifies) for s composed over the alternatives of `base`."""
        P = self.pairs(base, VA)
        if with_r:
            vslots = [self.br_options(s, base, a, u, VB) for a, u in P]
            fslots = [self.br_options(s, base, a, u, FB) for a, u in P]
        else:
            vslots = [self.b_options(s, u, VB) for a, u in P]
            fslots = [self.b_options(s, u, FB) for a, u in P]
        return composable(s, vslots), composable_subset(s, fslots)

    def counterfactual_proposition(self, key, left, right):
        if key not in NEW_KEYS and key != "XE":
            return super().counterfactual_proposition(key, left, right)
        frame = self.frame
        VA = self.proposition(left)[0]
        VB, FB = self.proposition(right)
        states = frame.states
        true_w = frozenset(w for w in frame.worlds if self.cf_true(left, right, w))
        false_w = frozenset(w for w in frame.worlds if self.cf_false(left, right, w))
        LV, LF = self.settlers(true_w, false_w)

        def part_e(with_r, settle=False):
            v, f = set(), set()
            for s in states:
                above = frame.worlds_above(s)
                if settle and s not in LV and s not in LF:
                    continue
                for w in above:
                    cv, cf = self.comp_at(s, w, VA, VB, FB, with_r)
                    if cv and (not settle or s in LV):
                        v.add(s)
                    if cf and (not settle or s in LF):
                        f.add(s)
            return frozenset(v), frozenset(f)

        if key in ("XS", "XSr"):
            v, f = set(), set()
            for s in states:
                cv, cf = self.comp_at(s, s, VA, VB, FB, key == "XSr")
                if cv: v.add(s)
                if cf: f.add(s)
            return frozenset(v), frozenset(f)
        if key == "XE":
            w = self.eval_world
            v, f = set(), set()
            for s in states:
                cv, cf = self.comp_at(s, w, VA, VB, FB, False)
                if cv: v.add(s)
                if cf: f.add(s)
            return frozenset(v), frozenset(f)
        if key in ("XPe", "XPer"):
            return part_e(key == "XPer")
        if key in ("XPa", "XPar"):
            v, f = set(), set()
            for s in states:
                above = frame.worlds_above(s)
                res = [self.comp_at(s, w, VA, VB, FB, key == "XPar") for w in above]
                if all(cv for cv, _ in res): v.add(s)
                if all(cf for _, cf in res): f.add(s)
            return frozenset(v), frozenset(f)
        if key == "XSx":
            v, f = set(), set()
            for s in states:
                P = self.pairs(s, VA)
                if s in VB and any(is_part_of(s, u) for _, u in P): v.add(s)
                if s in FB and any(is_part_of(s, u) for _, u in P): f.add(s)
            return frozenset(v), frozenset(f)
        if key == "SB":
            cb, cf_ = fusion_closure(VB), fusion_closure(FB)
            return LV & cb, LF & cf_
        if key == "SAB":
            cb, cf_ = fusion_closure(VA | VB), fusion_closure(VA | FB)
            return LV & cb, LF & cf_
        if key in ("SX", "SXr"):
            return part_e(key == "SXr", settle=True)
        if key == "SXC":
            v, f = part_e(False, settle=True)
            return fusion_closure(v) if v else v, fusion_closure(f) if f else f
        if key in ("SR", "SRC"):
            v, f = set(), set()
            for s in states:
                if s not in LV and s not in LF:
                    continue
                for w in frame.worlds_above(s):
                    slots = [[r for r in frame.max_compatible_parts(w, a) if is_part_of(r, s)] for a in VA if frame.alternatives(w, a)]
                    if composable(s, slots):
                        if s in LV: v.add(s)
                        if s in LF: f.add(s)
            if key == "SRC":
                return (fusion_closure(v) if v else frozenset(v)), (fusion_closure(f) if f else frozenset(f))
            return frozenset(v), frozenset(f)
        if key in ("ILC", "ILM", "ILMC"):
            iv, if_ = self.imposition_local(left, right)
            v, f = iv & LV, if_ & LF
            if key == "ILC":
                return fusion_closure(v) if v else v, fusion_closure(f) if f else f
            v, f = minimal_elements(v), minimal_elements(f)
            if key == "ILM":
                return v, f
            return fusion_closure(v) if v else v, fusion_closure(f) if f else f
        raise ValueError(key)


fo.Evaluator = XEvaluator  # measure() looks the name up at call time

A, B, C, D = Atom("A"), Atom("B"), Atom("C"), Atom("D")


def f3_frame():
    names = ["a", "a'", "p", "p'", "q", "q'", "b", "b'"]
    bit = {n: 1 << i for i, n in enumerate(names)}
    st = lambda *xs: sum(bit[x] for x in xs)
    w0 = st("a'", "p", "p'", "q", "q'", "b"); w1 = st("a", "p", "p'", "b")
    w2 = st("a", "q", "q'", "b"); w3 = st("a", "p", "q", "b'")
    frame = Frame.from_worlds(8, [w0, w1, w2, w3], names)
    interp = Interpretation({"A": ({st("a")}, {st("a'")}), "B": ({st("b")}, {st("b'")})})
    return frame, interp, (w0, w1, w2, w3)


PROPS = ("closure_V", "closure_F", "exclusive_possible", "exclusive_compat", "exhaustive",
         "bridge_sound_V", "bridge_sound_F", "bridge_sufficient_V", "bridge_sufficient_F",
         "impossible_harmless_V", "impossible_harmless_F")


def describe_model(frame, interp):
    return json.dumps(fo.model_to_dict(frame, interp), ensure_ascii=False)


def structure_sweep(models, keys, label):
    """Per candidate: count of models failing each property, first witness, proper-verifier stats."""
    fails = {k: collections.Counter() for k in keys}
    witness = {k: {} for k in keys}
    proper = {k: collections.Counter() for k in keys}
    n = 0
    t0 = time.time()
    for frame, interp in models:
        n += 1
        for k in keys:
            rec = measure(k, A, B, frame, interp)
            for p in PROPS:
                if rec[p] is False:
                    fails[k][p] += 1
                    witness[k].setdefault(p, (describe_model(frame, interp), {q: rec[q] for q in rec if q.endswith("witness") or q in ("verifiers", "falsifiers", "true_worlds")}))
            if rec["contingent"]:
                proper[k]["contingent_models"] += 1
                if rec["proper_possible_V"]:
                    proper[k]["contingent_with_proper_V"] += 1
                if rec["proper_possible_F"]:
                    proper[k]["contingent_with_proper_F"] += 1
                if rec["proper_possible_V"] and all(rec[p] for p in PROPS):
                    proper[k]["contingent_proper_V_and_all_props"] += 1
            if not rec["verifiers"] and not rec["falsifiers"]:
                proper[k]["empty_proposition"] += 1
    print(f"\n=== STRUCTURE {label}: {n} models, {time.time()-t0:.1f}s ===")
    print(f"{'key':6s} " + " ".join(f"{p[:14]:>14s}" for p in PROPS) + "   contingent proper_V proper_F properV&ok empty")
    for k in keys:
        row = " ".join(f"{fails[k][p]:>14d}" for p in PROPS)
        pc = proper[k]
        print(f"{k:6s} {row}   {pc['contingent_models']:>6d} {pc['contingent_with_proper_V']:>8d} {pc['contingent_with_proper_F']:>8d} {pc['contingent_proper_V_and_all_props']:>10d} {pc['empty_proposition']:>5d}")
    return fails, witness, proper


def logic_sweep(models, keys, label):
    """Nested-antecedent principles per candidate; counts of models with a failing world."""
    names = ("identity", "modus_ponens", "strengthening", "strict_to_cf", "cf_to_strict",
             "might_identity", "mp_falsity_form")
    fails = {k: collections.Counter() for k in keys}
    witness = {k: {} for k in keys}
    n = 0
    t0 = time.time()
    for frame, interp in models:
        n += 1
        for k in keys:
            ev = XEvaluator(frame, interp)
            X = CF(k, A, B)
            XM = Might(k, A, B)
            idn = CF(k, X, X)
            xc = CF(k, X, C)
            xdc = CF(k, And(X, D), C)
            strict = Box(Implies(X, C))
            midn = CF(k, XM, XM)
            res = {nm: True for nm in names}
            for w in frame.worlds:
                if not ev.truth(idn, w): res["identity"] = False
                if ev.truth(X, w) and ev.truth(xc, w) and not ev.truth(C, w): res["modus_ponens"] = False
                if ev.truth(xc, w) and not ev.truth(xdc, w): res["strengthening"] = False
                if ev.truth(strict, w) and not ev.truth(xc, w): res["strict_to_cf"] = False
                if ev.truth(xc, w) and not ev.truth(strict, w): res["cf_to_strict"] = False
                if not ev.truth(midn, w): res["might_identity"] = False
                if ev.truth(X, w) and ev.truth(xc, w) and ev.falsity(C, w): res["mp_falsity_form"] = False
            for nm in names:
                if not res[nm]:
                    fails[k][nm] += 1
                    witness[k].setdefault(nm, describe_model(frame, interp))
    print(f"\n=== LOGIC {label}: {n} models, {time.time()-t0:.1f}s (count of models with a failing world) ===")
    print(f"{'key':6s} " + " ".join(f"{nm:>14s}" for nm in names))
    for k in keys:
        print(f"{k:6s} " + " ".join(f"{fails[k][nm]:>14d}" for nm in names))
    return fails, witness


def hyper_sweep(models, keys, label):
    """Same truth-set, different proposition: A []-> B vs C []-> D."""
    counts = {k: collections.Counter() for k in keys}
    witness = {k: None for k in keys}
    n = 0
    for frame, interp in models:
        n += 1
        for k in keys:
            ev = XEvaluator(frame, interp)
            X, Y = CF(k, A, B), CF(k, C, D)
            if ev.truth_set(X) == ev.truth_set(Y):
                counts[k]["same_truth_set"] += 1
                pv, pf = ev.proposition(X); qv, qf = ev.proposition(Y)
                poss = frame.possible
                if (pv, pf) != (qv, qf):
                    counts[k]["distinct_props"] += 1
                if (pv & poss, pf & poss) != (qv & poss, qf & poss):
                    counts[k]["distinct_on_possible"] += 1
                    if witness[k] is None:
                        witness[k] = (describe_model(frame, interp), frame.fmt_set(pv), frame.fmt_set(qv), frame.fmt_set(ev.truth_set(X)))
    print(f"\n=== HYPERINTENSIONALITY {label}: {n} models ===")
    print(f"{'key':6s} same_truth_set distinct_props distinct_on_possible")
    for k in keys:
        c = counts[k]
        print(f"{k:6s} {c['same_truth_set']:>14d} {c['distinct_props']:>14d} {c['distinct_on_possible']:>20d}")
    return counts, witness



def random_models(n, letters, limit, seed):
    """Random frames on n atoms with random letter propositions meeting the letter constraints."""
    rng = random.Random(seed)
    out = []
    tries = 0
    while len(out) < limit and tries < limit * 200:
        tries += 1
        k = rng.randint(2, min(6, n + 2))
        cand = [rng.randint(1, (1 << n) - 1) for _ in range(k)]
        worlds = [w for w in cand if not any(w != v and is_part_of(w, v) for v in cand)]
        worlds = list(set(worlds))
        if len(worlds) < 2:
            continue
        try:
            frame = Frame.from_worlds(n, worlds)
        except ValueError:
            continue
        poss = [s for s in frame.possible if s]
        props = {}
        ok = True
        for L in letters:
            found = None
            for _ in range(60):
                gv = rng.sample(poss, rng.randint(1, 2)); gf = rng.sample(poss, rng.randint(1, 2))
                v, f = fusion_closure(gv), fusion_closure(gf)
                if fo.letter_constraints_hold(frame, v, f):
                    found = (v, f); break
            if found is None:
                ok = False; break
            props[L] = found
        if not ok:
            continue
        out.append((frame, Interpretation(props)))
    return out


def frame_g():
    """Seven-atom frame separating IL from L on possible states."""
    names = ["a", "a'", "x", "y", "c", "b", "b'"]
    bit = {nm: 1 << i for i, nm in enumerate(names)}
    st = lambda *xs: sum(bit[x] for x in xs)
    u = st("a", "x", "b'"); u2 = st("a", "x", "c", "b"); w = st("x", "y", "c", "b", "a'")
    frame = Frame.from_worlds(7, [u, u2, w], names)
    interp = Interpretation({"A": ({st("a")}, {st("a'")}), "B": ({st("b")}, {st("b'")}),
                             "C": ({st("c")}, {st("y")}), "D": ({st("b")}, {st("b'")})})
    return frame, interp, (u, u2, w)


def characterize_exact_sufficiency(models):
    """XPe has a verifier below T-world w iff every alternative of w carries a B-verifier already in w."""
    mismatches = 0; checked = 0
    for frame, interp in models:
        ev = XEvaluator(frame, interp)
        VA = ev.proposition(A)[0]; VB = ev.proposition(B)[0]
        v, _ = ev.proposition(CF("XPe", A, B))
        for w in frame.worlds:
            if not ev.cf_true(A, B, w):
                continue
            checked += 1
            has = any(is_part_of(s, w) for s in v)
            pred = all(any(is_part_of(b, u) and is_part_of(b, w) for b in VB) for a in VA for u in frame.alternatives(w, a))
            if has != pred:
                mismatches += 1
    print(f"exact-sufficiency characterization: {checked} true worlds checked, {mismatches} mismatches")


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "f3"
    if which == "f3":
        frame, interp, (w0, w1, w2, w3) = f3_frame()
        print("F3 frame: worlds", frame.fmt_set(frame.worlds))
        for k in ("SQpy",) + ALL:
            rec = measure(k, A, B, frame, interp)
            flags = "".join("." if rec[p] else "X" for p in PROPS)
            print(f"{k:6s} {flags}  V={rec['verifiers']}\n        F={rec['falsifiers']}\n        properV={rec['proper_possible_V']} properF={rec['proper_possible_F']}")
        print("props order:", PROPS)
        # nested identity etc on F3
        ev = XEvaluator(frame, interp)
        for k in ALL:
            X = CF(k, A, B)
            idn = [ev.truth(CF(k, X, X), w) for w in (w0, w1, w2, w3)]
            xc = [ev.truth(CF(k, X, B), w) for w in (w0, w1, w2, w3)]
            print(f"{k:6s} identity@w0..w3={idn}  (X[]->B)@w0..w3={xc}")
    elif which == "g":
        frame, interp, (u, u2, w) = frame_g()
        print("Frame G worlds:", frame.fmt_set(frame.worlds))
        for k in ("I", "L", "IL", "M", "MC", "ILC", "ILM", "ILMC", "XPa", "SB"):
            rec = measure(k, A, B, frame, interp)
            flags = "".join("." if rec[p] else "X" for p in PROPS)
            print(f"{k:5s} {flags} T={rec['true_worlds']} properV={rec['proper_possible_V']} properF={rec['proper_possible_F']}")
        ev = XEvaluator(frame, interp)
        for k in ("L", "IL", "ILC", "MC", "ILMC"):
            X, Y = CF(k, A, B), CF(k, C, D)
            print(k, "truth sets", frame.fmt_set(ev.truth_set(X)), frame.fmt_set(ev.truth_set(Y)),
                  "V_X∩poss", frame.fmt_set(ev.proposition(X)[0] & frame.possible), "V_Y∩poss", frame.fmt_set(ev.proposition(Y)[0] & frame.possible))
            xc = CF(k, X, C); strict = Box(Implies(X, C))
            print("   X[]->C:", [ev.truth(xc, z) for z in (u, u2, w)], " strict:", [ev.truth(strict, z) for z in (u, u2, w)],
                  " identity:", [ev.truth(CF(k, X, X), z) for z in (u, u2, w)])
    elif which == "charx":
        models = list(enumerate_models(3, ("A", "B")))
        characterize_exact_sufficiency(models)
        characterize_exact_sufficiency(random_models(5, ("A", "B"), 300, 5))
    elif which.startswith("rstruct"):
        n = int(sys.argv[2]); limit = int(sys.argv[3])
        keys = tuple(sys.argv[4].split(",")) if len(sys.argv) > 4 else ALL
        models = random_models(n, ("A", "B"), limit, seed=101 + n)
        structure_sweep(models, keys, f"random n={n} limit={limit}")
    elif which.startswith("rlogic"):
        n = int(sys.argv[2]); limit = int(sys.argv[3])
        keys = tuple(sys.argv[4].split(",")) if len(sys.argv) > 4 else ALL
        models = random_models(n, ("A", "B", "C", "D"), limit, seed=201 + n)
        logic_sweep(models, keys, f"random n={n} limit={limit}")
    elif which.startswith("rhyper"):
        n = int(sys.argv[2]); limit = int(sys.argv[3])
        keys = tuple(sys.argv[4].split(",")) if len(sys.argv) > 4 else ALL
        models = random_models(n, ("A", "B", "C", "D"), limit, seed=301 + n)
        counts, witness = hyper_sweep(models, keys, f"random n={n} limit={limit}")
        for k in keys:
            if witness[k] and k in ("ILC", "ILMC", "MC"):
                print(k, "witness:", witness[k][1], witness[k][2], "truth", witness[k][3])
                print("   model:", witness[k][0][:600])
    elif which.startswith("struct"):
        n = int(sys.argv[2]); limit = int(sys.argv[3]) if len(sys.argv) > 3 else None
        keys = tuple(sys.argv[4].split(",")) if len(sys.argv) > 4 else ALL
        models = list(enumerate_models(n, ("A", "B"), limit=limit, seed=11))
        fails, witness, proper = structure_sweep(models, keys, f"n={n} limit={limit}")
        out = {k: {"fails": dict(fails[k]), "proper": dict(proper[k]), "witness": witness[k]} for k in keys}
        json.dump(out, open(f"/tmp/struct_n{n}_{limit}.json", "w"), indent=1, ensure_ascii=False)
    elif which.startswith("logic"):
        n = int(sys.argv[2]); limit = int(sys.argv[3]) if len(sys.argv) > 3 else None
        keys = tuple(sys.argv[4].split(",")) if len(sys.argv) > 4 else ALL
        models = list(enumerate_models(n, ("A", "B", "C", "D"), limit=limit, seed=23))
        fails, witness = logic_sweep(models, keys, f"n={n} limit={limit}")
        json.dump({k: {"fails": dict(fails[k]), "witness": witness[k]} for k in keys},
                  open(f"/tmp/logic_n{n}_{limit}.json", "w"), indent=1, ensure_ascii=False)
    elif which.startswith("hyper"):
        n = int(sys.argv[2]); limit = int(sys.argv[3]) if len(sys.argv) > 3 else None
        keys = tuple(sys.argv[4].split(",")) if len(sys.argv) > 4 else ALL
        models = list(enumerate_models(n, ("A", "B", "C", "D"), limit=limit, seed=37))
        counts, witness = hyper_sweep(models, keys, f"n={n} limit={limit}")
        json.dump({k: {"counts": dict(counts[k]), "witness": witness[k]} for k in keys},
                  open(f"/tmp/hyper_n{n}_{limit}.json", "w"), indent=1, ensure_ascii=False)
