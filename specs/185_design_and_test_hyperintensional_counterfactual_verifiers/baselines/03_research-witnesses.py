import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from importlib import import_module; globals().update(vars(import_module("03_research-exploration")))  # from explore import *

def show(k, rec):
    flags = "".join("." if rec[p] else "X" for p in PROPS)
    print(f"  {k:5s} {flags} V∩poss={[x for x in rec['verifiers'] if x in rec.get('_poss', rec['verifiers'])]}")

# (a) Frame G2: same truth-set, different IL propositions
names = ["a", "a'", "x", "x'", "y", "c", "b", "b'"]
bit = {nm: 1 << i for i, nm in enumerate(names)}
st = lambda *xs: sum(bit[q] for q in xs)
u = st("a", "x", "b'"); u2 = st("a", "x", "c", "b"); w = st("x", "y", "c", "b", "a'"); v = st("x'", "a", "b")
frame = Frame.from_worlds(8, [u, u2, w, v], names)
interp = Interpretation({"A": ({st("a")}, {st("a'")}), "B": ({st("b")}, {st("b'")}),
                         "C": ({st("x")}, {st("x'")}), "D": ({st("b")}, {st("b'")})})
print("Frame G2 worlds:", frame.fmt_set(frame.worlds))
for L_ in ("A", "B", "C", "D"):
    print("  letter", L_, "constraints hold:", fo.letter_constraints_hold(frame, *interp[L_]))
ev = XEvaluator(frame, interp)
X, Y = CF("ILC", A, B), CF("ILC", C, D)
print("  truth sets X, Y:", frame.fmt_set(ev.truth_set(X)), frame.fmt_set(ev.truth_set(Y)))
poss = frame.possible
for k in ("L", "MC", "IL", "ILC", "ILM", "ILMC"):
    X, Y = CF(k, A, B), CF(k, C, D)
    vx, fx = ev.proposition(X); vy, fy = ev.proposition(Y)
    print(f"  {k:5s} V_X∩poss={frame.fmt_set(vx & poss)}\n        V_Y∩poss={frame.fmt_set(vy & poss)}\n        F_X∩poss={frame.fmt_set(fx & poss)}  F_Y∩poss={frame.fmt_set(fy & poss)}  distinct={ (vx,fx)!=(vy,fy) }")
    recx = measure(k, A, B, frame, interp); recy = measure(k, C, D, frame, interp)
    print(f"        props X: {''.join('.' if recx[p] else 'X' for p in PROPS)}  props Y: {''.join('.' if recy[p] else 'X' for p in PROPS)}")
# nested: does (A[]->B) []-> E differ from (C[]->D) []-> E for some E under ILC? use E = C-ish letter y? Use Neg(A) as consequent.
for k in ("ILC", "ILMC", "MC", "L"):
    X, Y = CF(k, A, B), CF(k, C, D)
    for E, nm in ((Neg(A), "¬A"), (Atom("C"), "C"), (Neg(Atom("C")), "¬C")):
        tx = [ev.truth(CF(k, X, E), z) for z in (u, u2, w, v)]
        ty = [ev.truth(CF(k, Y, E), z) for z in (u, u2, w, v)]
        if tx != ty:
            print(f"  {k}: (A[]->B) []-> {nm} = {tx}  vs (C[]->D) []-> {nm} = {ty}   [u,u2,w,v]")

# (b) F3 + z: SR verifier-sufficiency failure
names = ["a", "a'", "p", "p'", "q", "q'", "b", "b'", "z"]
bit = {nm: 1 << i for i, nm in enumerate(names)}
st = lambda *xs: sum(bit[q] for q in xs)
w0 = st("a'", "p", "p'", "q", "q'", "b"); w1 = st("a", "p", "p'", "b"); w2 = st("a", "q", "q'", "b"); w3 = st("a", "p", "q", "b'"); w4 = st("a'", "p", "p'", "b", "z")
frame = Frame.from_worlds(9, [w0, w1, w2, w3, w4], names)
interp = Interpretation({"A": ({st("a")}, {st("a'")}), "B": ({st("b")}, {st("b'")})})
print("\nFrame F3z worlds:", frame.fmt_set(frame.worlds))
for k in ("L", "MC", "ILC", "ILMC", "SR", "SRC", "XPa"):
    rec = measure(k, A, B, frame, interp)
    print(f"  {k:5s} {''.join('.' if rec[p] else 'X' for p in PROPS)} T={rec['true_worlds']} suffV_witness={rec['bridge_sufficient_V_witness']} properV={rec['proper_possible_V']} properF={rec['proper_possible_F']}")
ev = XEvaluator(frame, interp)
print("  [w4]_a =", frame.fmt_set(frame.max_compatible_parts(w4, st("a"))), " worlds above p.p'.b =", frame.fmt_set(frame.worlds_above(st("p","p'","b"))))

# (c) the n=4 random model where SRC's falsifier side is insufficient
for frame, interp in random_models(4, ("A", "B"), 400, seed=105):
    rec = measure("SRC", A, B, frame, interp)
    if not rec["bridge_sufficient_F"]:
        print("\nSRC falsifier-insufficient model:", describe_model(frame, interp))
        print("  false worlds:", rec["false_worlds"], " F=", rec["falsifiers"], " witness world:", rec["bridge_sufficient_F_witness"])
        ev = XEvaluator(frame, interp)
        VA = ev.proposition(A)[0]
        wf = next(w for w in frame.worlds if frame.fmt(w) == rec["bridge_sufficient_F_witness"])
        for a in VA:
            print("   a=", frame.fmt(a), "[w]_a=", frame.fmt_set(frame.max_compatible_parts(wf, a)), "Alt=", frame.fmt_set(frame.alternatives(wf, a)))
        recL = measure("L", A, B, frame, interp)
        print("  L falsifiers:", recL["falsifiers"], " MC falsifiers:", measure("MC", A, B, frame, interp)["falsifiers"])
        break
