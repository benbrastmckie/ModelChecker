"""Family-level settler-recipe oracle for the Logos manual's dynamics chapter.

Pure-Python, no Z3.  Implements the manual's family-level machinery over a
finite time window on the *duration-uniform* task-relation schema the manual
itself uses for its countermodels (03-dynamics.typ, the schema shared by
@ex-frame-r and @ex-frame-symmetric):

    s ->_0 t   iff  s = t and s possible
    s ->_d t   iff  s, t possible and (s = null iff t = null)      (d > 0)

Under this schema a thread on a domain of size >= 2 is: convex domain, all
values possible, all-null or none-null; at a singleton domain every family is
a thread (@rem-strict-coherence).  World-histories are exactly the
world-valued total functions (the manual proves this for both frames).

The recipe under test (task 185 report 02, lifted to families):

    V_x(phi) = closure_ext( Min { pi x-anchored | I_phi(pi) and L_phi(pi) } )

with L_phi(pi) := every world-history beta with pi <= beta makes phi true at
(beta, x), and I_phi(pi) := phi's own truth clause read with pi in the
history slot (antecedent verifiers restricted to those whose domain fits in
dom(pi); imposition on pi via the maximal compatible subevolutions of pi's
restriction, condition (a)-(d) of @def-maximal-compatible-subevolutions read
for an arbitrary bounding family).  Falsifiers dually.  ILC := closure(IL)
without the minimality step is computed alongside for the strictness
comparison.

Run:  python 01_family-recipe-oracle.py
"""
from __future__ import annotations

import itertools
import sys
from functools import lru_cache
from typing import Dict, FrozenSet, Iterable, List, Set, Tuple

Family = FrozenSet[Tuple[int, int]]  # frozenset of (time, state)

# ----------------------------------------------------------------------------
# Frame
# ----------------------------------------------------------------------------


class Frame:
    def __init__(self, atoms: List[str], worlds: List[Set[str]], times: List[int]):
        self.atoms = atoms
        self.n = len(atoms)
        self.idx = {a: i for i, a in enumerate(atoms)}
        self.states = list(range(1 << self.n))
        self.full = (1 << self.n) - 1
        self.worlds = sorted(self.mask(w) for w in worlds)
        self.poss = {s for s in self.states if any(self.part(s, w) for w in self.worlds)}
        assert all(self.maximal_possible(w) for w in self.worlds), "worlds must be maximal possible"
        self.times = list(times)
        self.histories: List[Dict[int, int]] = [
            dict(zip(self.times, vals)) for vals in itertools.product(self.worlds, repeat=len(self.times))
        ]

    # -- states ---------------------------------------------------------------
    def mask(self, names: Iterable[str]) -> int:
        m = 0
        for a in names:
            m |= 1 << self.idx[a]
        return m

    def name(self, s: int) -> str:
        return ".".join(a for a in self.atoms if s & (1 << self.idx[a])) or "null"

    @staticmethod
    def part(s: int, t: int) -> bool:
        return s & t == s

    def compat(self, s: int, t: int) -> bool:
        return (s | t) in self.poss

    def maximal_possible(self, w: int) -> bool:
        return w in self.poss and all(not (self.part(w, u) and u != w) for u in self.poss)

    def max_compat_parts(self, s: int, t: int) -> List[int]:
        cands = [r for r in self.states if self.part(r, s) and self.compat(r, t)]
        return [r for r in cands if not any(self.part(r, r2) and r2 != r for r2 in cands)]

    # -- families -------------------------------------------------------------
    @staticmethod
    def dom(pi: Family) -> Set[int]:
        return {t for t, _ in pi}

    @staticmethod
    def val(pi: Family, t: int) -> int:
        for u, s in pi:
            if u == t:
                return s
        raise KeyError(t)

    @staticmethod
    def fam(d: Dict[int, int]) -> Family:
        return frozenset(d.items())

    def convex(self, d: Set[int]) -> bool:
        lo, hi = min(d), max(d)
        return all(t in d for t in self.times if lo <= t <= hi)

    def thread(self, pi: Family) -> bool:
        d = self.dom(pi)
        if len(d) == 1:
            return True
        vals = [s for _, s in pi]
        if not self.convex(d):
            return False
        if any(s not in self.poss for s in vals):
            return False
        nulls = [s == 0 for s in vals]
        return all(nulls) or not any(nulls)

    def fam_part(self, pi: Family, f: Family) -> bool:
        """Evolution parthood: dom(pi) subset dom(f) and pointwise parthood."""
        fd = dict(f)
        return all(t in fd and self.part(s, fd[t]) for t, s in pi)

    def below_history(self, pi: Family, h: Dict[int, int]) -> bool:
        return all(self.part(s, h[t]) for t, s in pi)

    def ext_fusion(self, a: Family, b: Family) -> Family:
        d = dict(a)
        for t, s in b:
            d[t] = d.get(t, 0) | s
        return self.fam(d)

    def closure_ext(self, fams: Set[Family]) -> Set[Family]:
        out = set(fams)
        frontier = set(fams)
        while frontier:
            new = set()
            for a in frontier:
                for b in list(out):
                    c = self.ext_fusion(a, b)
                    if c not in out:
                        new.add(c)
            out |= new
            frontier = new
        return out

    def minimal(self, fams: Set[Family]) -> Set[Family]:
        return {p for p in fams if not any(q != p and self.fam_part(q, p) for q in fams)}

    def candidates(self, x: int) -> List[Family]:
        out = []
        others = [t for t in self.times if t != x]
        for k in range(len(others) + 1):
            for extra in itertools.combinations(others, k):
                d = [x, *extra]
                for vals in itertools.product(self.states, repeat=len(d)):
                    out.append(self.fam(dict(zip(d, vals))))
        return out


# ----------------------------------------------------------------------------
# Model: letters and formulas
# ----------------------------------------------------------------------------

TOP = ("top",)
BOT = ("bot",)


def Let(n):
    return ("let", n)


def Not(p):
    return ("not", p)


def And(p, q):
    return ("and", p, q)


def Or(p, q):
    return ("or", p, q)


def F(p):  # top until p
    return ("F", p)


def G(p):
    return Not(F(Not(p)))


def CF(a, b):
    return ("cf", a, b)


def Box(p):
    return CF(TOP, p)


def Might(a, b):
    return Not(CF(a, Not(b)))


def Dia(p):
    return Might(TOP, p)


def S(p):
    return ("S", p)


def Id(a, b):
    return ("id", a, b)


def show(phi) -> str:
    k = phi[0]
    if k == "let":
        return phi[1]
    if k == "top":
        return "T"
    if k == "bot":
        return "_|_"
    if k == "not":
        return "~" + show(phi[1])
    if k == "and":
        return f"({show(phi[1])} & {show(phi[2])})"
    if k == "or":
        return f"({show(phi[1])} v {show(phi[2])})"
    if k == "F":
        return f"F{show(phi[1])}"
    if k == "cf":
        if phi[1] == TOP:
            return f"[]{show(phi[2])}"
        return f"({show(phi[1])} []-> {show(phi[2])})"
    if k == "S":
        return f"S{show(phi[1])}"
    if k == "id":
        return f"({show(phi[1])} == {show(phi[2])})"
    raise ValueError(phi)


class Model:
    def __init__(self, frame: Frame, letters: Dict[str, Tuple[Set[int], Set[int]]], variant: str = "ILMC",
                 padding: str = "full"):
        self.fr = frame
        self.letters = letters
        self.variant = variant  # "ILMC" (minimal) or "ILC" (no minimality step)
        # How I_phi reads a candidate family pi outside dom(pi):
        #   "full":     the bounding family is pi padded by the full state (constrains nothing there;
        #               imposing t on the full state yields exactly the worlds containing t)
        #   "restrict": only antecedent verifiers with dom(pi') within dom(pi) are imposed
        self.padding = padding
        self._ev: Dict = {}
        self._recipe: Dict = {}
        for name, (V, Fs) in letters.items():
            self._check_letter(name, V, Fs)

    def _check_letter(self, name, V, Fs):
        fr = self.fr
        for a in V:
            for b in V:
                assert (a | b) in V, f"{name}: verifier closure"
        for a in Fs:
            for b in Fs:
                assert (a | b) in Fs, f"{name}: falsifier closure"
        for a in V:
            for b in Fs:
                assert (a | b) not in fr.poss, f"{name}: exclusivity"
        for p in fr.poss:
            assert any(fr.compat(p, s) for s in V | Fs), f"{name}: exhaustivity"

    # -- state-level verification for CF formulas -----------------------------
    def sv(self, phi) -> Tuple[Set[int], Set[int]]:
        fr = self.fr
        k = phi[0]
        if k == "let":
            return self.letters[phi[1]]
        if k == "top":
            return set(fr.states), {fr.full}
        if k == "bot":
            return set(), {0}
        if k == "not":
            V, Fs = self.sv(phi[1])
            return Fs, V
        if k == "and":
            V1, F1 = self.sv(phi[1])
            V2, F2 = self.sv(phi[2])
            return {a | b for a in V1 for b in V2}, F1 | F2 | {a | b for a in F1 for b in F2}
        if k == "or":
            V1, F1 = self.sv(phi[1])
            V2, F2 = self.sv(phi[2])
            return V1 | V2 | {a | b for a in V1 for b in V2}, {a | b for a in F1 for b in F2}
        if k == "id":
            holds = self.sv(phi[1]) == self.sv(phi[2])
            return ({0}, set()) if holds else (set(), {0})
        raise ValueError(f"not a CF formula: {show(phi)}")

    def is_cf(self, phi) -> bool:
        k = phi[0]
        if k in ("let", "top", "bot", "id"):
            return True
        if k == "not":
            return self.is_cf(phi[1])
        if k in ("and", "or"):
            return self.is_cf(phi[1]) and self.is_cf(phi[2])
        return False

    # -- truth at world-histories ---------------------------------------------
    def true(self, phi, h: Dict[int, int], x: int) -> bool:
        fr = self.fr
        k = phi[0]
        if k in ("let", "top", "bot", "id") or (self.is_cf(phi) and k in ("not", "and", "or")):
            V, _ = self.sv(phi)
            return any(fr.part(s, h[x]) for s in V)
        if k == "not":
            return self.false(phi[1], h, x)
        if k == "and":
            return self.true(phi[1], h, x) and self.true(phi[2], h, x)
        if k == "or":
            return self.true(phi[1], h, x) or self.true(phi[2], h, x)
        if k == "F":
            return any(self.true(phi[1], h, z) for z in fr.times if z > x)
        if k == "cf":
            return self.cf_true(phi[1], phi[2], fr.fam(h), x, fit_only=False)
        if k == "S":
            return all(self.true(phi[1], a, x) for a in fr.histories if a[x] == h[x])
        raise ValueError(phi)

    def false(self, phi, h: Dict[int, int], x: int) -> bool:
        fr = self.fr
        k = phi[0]
        if k in ("let", "top", "bot", "id") or (self.is_cf(phi) and k in ("not", "and", "or")):
            _, Fs = self.sv(phi)
            return any(fr.part(s, h[x]) for s in Fs)
        if k == "not":
            return self.true(phi[1], h, x)
        if k == "and":
            return self.false(phi[1], h, x) or self.false(phi[2], h, x)
        if k == "or":
            return self.false(phi[1], h, x) and self.false(phi[2], h, x)
        if k == "F":
            return all(self.false(phi[1], h, z) for z in fr.times if z > x)
        if k == "cf":
            return self.cf_false(phi[1], phi[2], fr.fam(h), x, fit_only=False)
        if k == "S":
            return any(self.false(phi[1], a, x) for a in fr.histories if a[x] == h[x])
        raise ValueError(phi)

    # -- imposition on an arbitrary bounding family -----------------------------
    def mcs(self, g: Family, pi: Family) -> List[Family]:
        """Maximal pi-compatible subevolutions of the bounding family g (dom(pi) = dom(g)).

        Under the duration-uniform schema a thread couples points only through
        null/non-null, so the maximal threads are the products of pointwise
        maximal compatible parts, unless some point admits only the null part,
        in which case the constant-null family is the unique maximal thread
        (when pi is pointwise possible) and otherwise there is none.
        """
        fr = self.fr
        gd, pd = dict(g), dict(pi)
        X = sorted(pd)
        if not fr.convex(set(X)):
            return []
        if any(pd[z] not in fr.poss for z in X):
            return []  # impossible value: nothing is compatible (@prop-counterpossible-vacuity)
        per_point = [fr.max_compat_parts(gd[z], pd[z]) for z in X]
        if len(X) == 1:
            return [fr.fam({X[0]: r}) for r in per_point[0]]
        if any(all(r == 0 for r in mp) for mp in per_point):
            return [fr.fam({z: 0 for z in X})]
        out = []
        for combo in itertools.product(*per_point):
            rho = fr.fam(dict(zip(X, combo)))
            if fr.thread(rho):
                out.append(rho)
        return out

    def alt(self, g: Family, pi: Family) -> List[Dict[int, int]]:
        fr = self.fr
        X = fr.dom(pi)
        gd = dict(g)
        g_restricted = fr.fam({z: gd.get(z, fr.full) for z in X})
        out = []
        for rho in self.mcs(g_restricted, pi):
            fused = fr.ext_fusion(pi, rho)
            if not fr.thread(fused):
                continue
            for beta in fr.histories:
                if fr.below_history(fused, beta) and beta not in out:
                    out.append(beta)
        return out

    def cf_true(self, A, B, g: Family, x: int, fit_only: bool) -> bool:
        fr = self.fr
        gdom = fr.dom(g)
        for pi in self.ev(A, x):
            if fit_only and self.padding == "restrict" and not fr.dom(pi) <= gdom:
                continue
            for beta in self.alt(g, pi):
                if not self.true(B, beta, x):
                    return False
        return True

    def cf_false(self, A, B, g: Family, x: int, fit_only: bool) -> bool:
        fr = self.fr
        gdom = fr.dom(g)
        for pi in self.ev(A, x):
            if fit_only and self.padding == "restrict" and not fr.dom(pi) <= gdom:
                continue
            for beta in self.alt(g, pi):
                if self.false(B, beta, x):
                    return True
        return False

    # -- event verification -----------------------------------------------------
    def ev(self, phi, x: int) -> Set[Family]:
        return self._event(phi, x)[0]

    def ef(self, phi, x: int) -> Set[Family]:
        return self._event(phi, x)[1]

    def _event(self, phi, x: int) -> Tuple[Set[Family], Set[Family]]:
        key = (phi, x)
        if key in self._ev:
            return self._ev[key]
        fr = self.fr
        k = phi[0]
        if k in ("let", "top", "bot", "id"):
            V, Fs = self.sv(phi)
            res = ({fr.fam({x: s}) for s in V}, {fr.fam({x: s}) for s in Fs})
        elif k == "not":
            V, Fs = self._event(phi[1], x)
            res = (Fs, V)
        elif k == "and":
            V1, F1 = self._event(phi[1], x)
            V2, F2 = self._event(phi[2], x)
            res = ({fr.ext_fusion(a, b) for a in V1 for b in V2},
                   F1 | F2 | {fr.ext_fusion(a, b) for a in F1 for b in F2})
        elif k == "or":
            V1, F1 = self._event(phi[1], x)
            V2, F2 = self._event(phi[2], x)
            res = (V1 | V2 | {fr.ext_fusion(a, b) for a in V1 for b in V2},
                   {fr.ext_fusion(a, b) for a in F1 for b in F2})
        elif k == "F":
            res = self._event_F(phi[1], x)
        elif k in ("cf", "S"):
            res = self.recipe(phi, x)
        else:
            raise ValueError(phi)
        self._ev[key] = res
        return res

    def _event_F(self, psi, x: int) -> Tuple[Set[Family], Set[Family]]:
        """@def-event-until at guard top: verifiers dom [x,z] u dom(rho), rho(z) = pi(z) exact,
        interior values arbitrary (every state inexactly verifies top), pi(x) = null by
        @rem-event-anchor-convention; falsifiers on the whole forward ray."""
        fr = self.fr
        V: Set[Family] = set()
        for z in fr.times:
            if z <= x:
                continue
            for rho in self.ev(psi, z):
                rd = dict(rho)
                interior = [y for y in fr.times if x < y < z]
                free = [y for y in interior if y not in rd] + [y for y in rd if y != z and y not in interior and y != x]
                fixed = {x: 0, z: rd[z]}
                for y in rd:
                    if y != z:
                        fixed.setdefault(y, rd[y])
                # points in dom(rho) other than z: pi(y) any state above rho(y)
                above = [y for y in rd if y != z]
                free_pts = sorted(set(interior) - set(rd))
                for vals in itertools.product(fr.states, repeat=len(free_pts)):
                    for ups in itertools.product(fr.states, repeat=len(above)):
                        d = dict(fixed)
                        for y, s in zip(free_pts, vals):
                            d[y] = s
                        ok = True
                        for y, s in zip(above, ups):
                            if not fr.part(rd[y], s):
                                ok = False
                                break
                            d[y] = s
                        if ok and 0 not in d:
                            d[x] = 0
                        if ok:
                            V.add(fr.fam(d))
        Fs: Set[Family] = set()
        ray = [t for t in fr.times if t >= x]
        later = [t for t in ray if t > x]
        exact_f = {z: {fr.val(r, z) for r in self.ef(psi, z) if fr.dom(r) == {z}} for z in later}
        for vals in itertools.product(fr.states, repeat=len(later)):
            d = {x: 0, **dict(zip(later, vals))}
            good = True
            for z in later:
                if d[z] in exact_f[z]:
                    continue
                if any(d[y] == fr.full for y in later if x < y < z):
                    continue
                good = False
                break
            if good:
                Fs.add(fr.fam(d))
        return V, Fs

    # -- the settler recipe -----------------------------------------------------
    def I_clauses(self, phi, pi: Family, x: int) -> Tuple[bool, bool]:
        """(I_phi(pi), I-_phi(pi)): the operator's own truth/falsity clause read at pi."""
        fr = self.fr
        k = phi[0]
        if k == "cf":
            return (self.cf_true(phi[1], phi[2], pi, x, fit_only=True),
                    self.cf_false(phi[1], phi[2], pi, x, fit_only=True))
        if k == "S":
            # @def-stability-truth pins alpha(x) = tau(x); at a world-history this is
            # equivalent (by world-state maximality) to alpha(x) >= tau(x), and only the
            # containment form is meaningful at a non-maximal candidate value.
            v = fr.val(pi, x)
            alphas = [a for a in fr.histories if fr.part(v, a[x])]
            return (all(self.true(phi[1], a, x) for a in alphas),
                    any(self.false(phi[1], a, x) for a in alphas))
        if k == "id":
            holds = self.sv(phi[1]) == self.sv(phi[2])
            return holds, not holds
        raise ValueError(phi)

    def L_clauses(self, phi, pi: Family, x: int) -> Tuple[bool, bool, int]:
        fr = self.fr
        above = [h for h in fr.histories if fr.below_history(pi, h)]
        return (all(self.true(phi, h, x) for h in above),
                all(self.false(phi, h, x) for h in above),
                len(above))

    def recipe(self, phi, x: int, variant: str = None) -> Tuple[Set[Family], Set[Family]]:
        variant = variant or self.variant
        key = (phi, x, variant)
        if key in self._recipe:
            return self._recipe[key]
        fr = self.fr
        ILV, ILF = set(), set()
        for pi in fr.candidates(x):
            L, Lneg, _ = self.L_clauses(phi, pi, x)
            if not (L or Lneg):
                continue
            I, Ineg = self.I_clauses(phi, pi, x)
            if I and L:
                ILV.add(pi)
            if Ineg and Lneg:
                ILF.add(pi)
        if variant == "ILMC":
            V, Fs = fr.closure_ext(fr.minimal(ILV)), fr.closure_ext(fr.minimal(ILF))
        else:
            V, Fs = fr.closure_ext(ILV), fr.closure_ext(ILF)
        self._recipe[key] = (V, Fs)
        self._recipe[(phi, x, "IL-raw")] = (ILV, ILF)
        return V, Fs

    # -- state-level ILMC for cross-checking (task 185 clause) ---------------------
    def state_ilmc(self, A, B) -> Tuple[Set[int], Set[int]]:
        fr = self.fr
        VA, _ = self.sv(A)
        VB, FB = self.sv(B)

        def T(w):
            return all(any(fr.part(b, u) for b in VB)
                       for a in VA for r in fr.max_compat_parts(w, a) for u in fr.worlds if fr.part(a | r, u))

        def Tf(w):
            return any(any(fr.part(b, u) for b in FB)
                       for a in VA for r in fr.max_compat_parts(w, a) for u in fr.worlds if fr.part(a | r, u))

        IL = {t for t in fr.states if T(t) and all(T(w) for w in fr.worlds if fr.part(t, w))}
        ILf = {t for t in fr.states if Tf(t) and all(Tf(w) for w in fr.worlds if fr.part(t, w))}

        def minimal(S):
            return {t for t in S if not any(u != t and fr.part(u, t) for u in S)}

        def closure(S):
            out = set(S)
            changed = True
            while changed:
                changed = False
                for a in list(out):
                    for b in list(out):
                        if (a | b) not in out:
                            out.add(a | b)
                            changed = True
            return out

        return closure(minimal(IL)), closure(minimal(ILf))

    # -- reporting helpers --------------------------------------------------------
    def fam_str(self, pi: Family) -> str:
        return "{" + ", ".join(f"{t}:{self.fr.name(s)}" for t, s in sorted(pi)) + "}"

    def realizable(self, pi: Family) -> bool:
        return any(self.fr.below_history(pi, h) for h in self.fr.histories)

    def valid(self, phi, x: int) -> Tuple[bool, List[Dict[int, int]]]:
        bad = [h for h in self.fr.histories if not self.true(phi, h, x)]
        return not bad, bad

    def entails(self, premises, concl, x: int):
        bad = [h for h in self.fr.histories
               if all(self.true(p, h, x) for p in premises) and not self.true(concl, h, x)]
        return not bad, bad


# ----------------------------------------------------------------------------
# Experiments
# ----------------------------------------------------------------------------


def hist_str(fr: Frame, h: Dict[int, int]) -> str:
    return "<" + ", ".join(fr.name(h[t]) for t in fr.times) + ">"


def report_event(m: Model, phi, x: int, label: str = "", show_all: bool = False):
    fr = m.fr
    V, Fs = m.ev(phi, x), m.ef(phi, x)
    ILV, ILF = m._recipe.get((phi, x, "IL-raw"), (set(), set()))
    print(f"\n[{label or show(phi)}] at anchor {x}, variant {m.variant}")
    print(f"  IL members: V {len(ILV)}, F {len(ILF)}; after min+closure: V {len(V)}, F {len(Fs)}")
    minV, minF = fr.minimal(ILV), fr.minimal(ILF)
    rv = [p for p in minV if m.realizable(p)]
    rf = [p for p in minF if m.realizable(p)]
    print(f"  minimal settlers: {len(minV)} (realizable {len(rv)}); minimal co-settlers: {len(minF)} (realizable {len(rf)})")
    print(f"  domains of realizable minimal settlers: {sorted({tuple(sorted(fr.dom(p))) for p in rv})}")
    print(f"  domains of realizable minimal co-settlers: {sorted({tuple(sorted(fr.dom(p))) for p in rf})}")
    if show_all or len(rv) <= 12:
        print("  realizable minimal settlers: " + ", ".join(m.fam_str(p) for p in sorted(rv, key=sorted)))
    if show_all or len(rf) <= 12:
        print("  realizable minimal co-settlers: " + ", ".join(m.fam_str(p) for p in sorted(rf, key=sorted)))
    # bridge checks
    sound = all(m.true(phi, h, x) for p in V for h in fr.histories if fr.below_history(p, h))
    sound_f = all(m.false(phi, h, x) for p in Fs for h in fr.histories if fr.below_history(p, h))
    suff = all(any(fr.below_history(p, h) for p in V) for h in fr.histories if m.true(phi, h, x))
    suff_f = all(any(fr.below_history(p, h) for p in Fs) for h in fr.histories if m.false(phi, h, x))
    # E3 pointwise
    e3 = all(any(t in fr.dom(q) and not fr.compat(fr.val(p, t), fr.val(q, t)) for t in fr.dom(p))
             for p in V for q in Fs)
    # E3 history form
    e3h = all(not (fr.below_history(p, h) and fr.below_history(q, h)) for p in V for q in Fs for h in fr.histories)
    convex_ok = all(fr.convex(fr.dom(p)) for p in V | Fs)
    rV = [p for p in V if m.realizable(p)]
    rF = [p for p in Fs if m.realizable(p)]
    e3r = all(any(t in fr.dom(q) and not fr.compat(fr.val(p, t), fr.val(q, t)) for t in fr.dom(p))
              for p in rV for q in rF)
    bad = [(p, q) for p in V for q in Fs
           if not any(t in fr.dom(q) and not fr.compat(fr.val(p, t), fr.val(q, t)) for t in fr.dom(p))]
    print(f"  sound V/F: {sound}/{sound_f}; sufficient V/F: {suff}/{suff_f}")
    print(f"  E3 pointwise (all members): {e3}; E3 pointwise (realizable members): {e3r}; "
          f"E3 history-form: {e3h}; all domains convex: {convex_ok}")
    if bad:
        p, q = bad[0]
        print(f"  pointwise-E3 witness: V {m.fam_str(p)} (realizable {m.realizable(p)}) vs F {m.fam_str(q)} (realizable {m.realizable(q)})")
    return V, Fs


def frame_f3(times):
    atoms = ["a", "a'", "p", "p'", "q", "q'", "b", "b'"]
    worlds = [{"a'", "p", "p'", "q", "q'", "b"}, {"a", "p", "p'", "b"}, {"a", "q", "q'", "b"}, {"a", "p", "q", "b'"}]
    return Frame(atoms, worlds, times)


def frame_small(times):
    """4-atom frame with a contingent counterfactual and proper-part settlers."""
    atoms = ["a", "b", "c", "d"]
    worlds = [{"a", "b"}, {"a", "c"}, {"d", "b"}, {"d", "c"}]
    return Frame(atoms, worlds, times)


def letters_small(fr: Frame):
    m = fr.mask
    return {
        "A": ({m("a")}, {m("d")}),
        "B": ({m("b")}, {m("c")}),
        "C": ({m("c")}, {m("b")}),
        "D": ({m("d")}, {m("a")}),
    }


def letters_f3(fr: Frame):
    m = fr.mask
    return {
        "A": ({m(["a"])}, {m(["a'"])}),
        "B": ({m(["b"])}, {m(["b'"])}),
    }


def experiment_alignment(times, padding="full"):
    print("=" * 78)
    print(f"E1  CF-constituent counterfactual: family recipe vs state-level ILMC, window {times}, padding {padding}")
    fr = frame_small(times)
    m = Model(fr, letters_small(fr), padding=padding)
    A, B = Let("A"), Let("B")
    V, Fs = m.recipe(CF(A, B), 0)
    sV, sF = m.state_ilmc(A, B)
    emb = lambda S: {fr.fam({0: s}) for s in S}
    print(f"  state-level ILMC V = {{{', '.join(fr.name(s) for s in sorted(sV))}}}, F = {{{', '.join(fr.name(s) for s in sorted(sF))}}}")
    print(f"  family V restricted to dom {{0}} == embedding of state V: {({p for p in V if fr.dom(p) == {0}} == emb(sV))}")
    print(f"  family F restricted to dom {{0}} == embedding of state F: {({p for p in Fs if fr.dom(p) == {0}} == emb(sF))}")
    extra = [p for p in V | Fs if fr.dom(p) != {0} and m.realizable(p)]
    print(f"  realizable members with larger domain: {len(extra)}"
          + ("" if not extra else "  e.g. " + ", ".join(m.fam_str(p) for p in extra[:6])))
    report_event(m, CF(A, B), 0)


def experiment_null_family(times):
    print("=" * 78)
    print(f"E2  Null-family derivations (identity, necessity), window {times}")
    fr = frame_small(times)
    m = Model(fr, letters_small(fr))
    A, B, C = Let("A"), Let("B"), Let("C")
    for phi in [Id(A, A), Id(A, B), Box(Or(A, Not(A))), Box(A), Box(Or(Or(A, B), Or(C, Let("D")))), S(A), S(Or(A, Not(A)))]:
        V, Fs = m.recipe(phi, 0)
        nullfam = fr.fam({0: 0})
        rv = sorted(m.fam_str(p) for p in V if m.realizable(p))
        rf = sorted(m.fam_str(p) for p in Fs if m.realizable(p))
        print(f"  {show(phi):28s} realizable V = {rv[:5]}{'...' if len(rv) > 5 else ''}  "
              f"realizable F = {rf[:5]}{'...' if len(rf) > 5 else ''}"
              f"   [V=={{null}}: {V == {nullfam}}, F=={{null}}: {Fs == {nullfam}}]")


def experiment_nested(times, antecedent_builder, label, paddings=("full", "restrict")):
    print("=" * 78)
    print(f"E3  Nested logic at a recipe-governed antecedent: {label}, window {times}")
    fr = frame_small(times)
    A, B, C, D = Let("A"), Let("B"), Let("C"), Let("D")
    consequents = [A, B, C, D, Not(A), Not(B), Not(C), Not(D), And(A, C), Or(B, D)]
    for padding in paddings:
        for variant in ("ILMC", "ILC"):
            m = Model(fr, letters_small(fr), variant=variant, padding=padding)
            X = antecedent_builder()
            V, Fs = m.recipe(X, 0)
            rv = [p for p in V if m.realizable(p)]
            print(f"  padding {padding}, variant {variant}: |V_X| = {len(V)} (realizable {len(rv)}: "
                  f"{', '.join(m.fam_str(p) for p in sorted(rv, key=sorted)[:6])}{'...' if len(rv) > 6 else ''}), "
                  f"|F_X| = {len(Fs)}, X true at {sum(m.true(X, h, 0) for h in fr.histories)}/{len(fr.histories)} histories")
            names = ["identity", "MP", "strict->cf", "cf->strict", "AS", "ReadingB(S)", "might-id"]
            fails = {n: [] for n in names}
            for Cc in consequents:
                checks = [
                    ("identity", m.valid(CF(X, X), 0)),
                    ("MP", m.entails([X, CF(X, Cc)], Cc, 0)),
                    ("strict->cf", m.entails([Box(Or(Not(X), Cc))], CF(X, Cc), 0)),
                    ("cf->strict", m.entails([CF(X, Cc)], Box(Or(Not(X), Cc)), 0)),
                    ("AS", m.entails([CF(X, Cc)], CF(And(X, D), Cc), 0)),
                    ("ReadingB(S)", m.valid(And(Or(Not(CF(X, Cc)), S(Cc)), Or(Not(S(Cc)), CF(X, Cc))), 0)),
                    ("might-id", m.valid(Might(X, X), 0)),
                ]
                for n, (ok, bad) in checks:
                    if not ok:
                        fails[n].append((show(Cc), hist_str(fr, bad[0])))
            for n in names:
                if fails[n]:
                    c, h = fails[n][0]
                    print(f"    {n:12s} FAILS for {len(fails[n])}/{len(consequents)} consequents; e.g. consequent {c} at history {h}")
                else:
                    print(f"    {n:12s} valid for all {len(consequents)} consequents")


def experiment_f3(times, padding="full"):
    print("=" * 78)
    print(f"E4  Report-02 frame F3 at the family level (window {times}, padding {padding}): realizable minimal settlers")
    fr = frame_f3(times)
    m = Model(fr, letters_f3(fr), padding=padding)
    A, B = Let("A"), Let("B")
    V, Fs = report_event(m, CF(A, B), 0, show_all=True)
    sV, sF = m.state_ilmc(A, B)
    print(f"  state-level ILMC possible verifiers: {sorted(fr.name(s) for s in sV if s in fr.poss)}")
    print(f"  state-level ILMC possible falsifiers: {sorted(fr.name(s) for s in sF if s in fr.poss)}")


def experiment_tensed(times, padding="full"):
    print("=" * 78)
    print(f"E5  Tensed antecedent (F P) []-> Q and its settlers, window {times}, padding {padding}")
    fr = frame_small(times)
    m = Model(fr, letters_small(fr), padding=padding)
    P, Q = Let("A"), Let("B")
    X = CF(F(P), Q)
    evs = m.ev(F(P), 0)
    print(f"  event verifiers of F{show(P)} at 0: {len(evs)}; domains {sorted({tuple(sorted(fr.dom(p))) for p in evs})}")
    truth = [m.true(X, h, 0) for h in fr.histories]
    qtruth = [m.true(Q, h, 0) for h in fr.histories]
    print(f"  X true at {sum(truth)}/{len(truth)} histories; agrees with Q at anchor everywhere: {truth == qtruth}")
    report_event(m, X, 0, show_all=True)


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("all", "e1"):
        for pad in ("full", "restrict"):
            experiment_alignment([0], pad)
            experiment_alignment([0, 1], pad)
    if which in ("all", "e2"):
        experiment_null_family([0, 1])
    if which in ("all", "e3"):
        experiment_nested([0, 1], lambda: CF(Let("A"), Let("B")), "X = A []-> B")
        experiment_nested([0, 1], lambda: CF(F(Let("A")), Let("B")), "X = (F A) []-> B")
        experiment_nested([0, 1], lambda: S(Let("B")), "X = S B", paddings=("full",))
    if which in ("all", "e5"):
        for pad in ("full", "restrict"):
            experiment_tensed([0, 1, 2], pad)
    if which in ("all", "e4"):
        experiment_f3([0])
        experiment_f3([0, 1])
