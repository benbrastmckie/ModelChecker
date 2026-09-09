"""Pure-Python frame oracle for counterfactual verifier clauses.

This module evaluates candidate verification clauses for the counterfactual
conditional over explicit finite frames without Z3.  It exists because the
Z3 layer expands every quantifier finitely (``model_checker.utils.ForAll``),
which makes frames with more than four atoms impractical there, while the
refutation frame in the provenance research has eight atoms.

States are integers read as bitmasks over ``n`` atoms; parthood is bitwise
inclusion and fusion is bitwise or, exactly as in the bit-vector semantics.
A ``Frame`` fixes the possible states (a downward-closed set) and derives the
world states as the maximal possible states.  An ``Interpretation`` assigns
verifier and falsifier sets to sentence letters.  Formulas are small frozen
dataclasses; ``Evaluator`` computes truth at worlds by the same recursive
clauses the Z3 operators use, and computes the verifier/falsifier sets of a
counterfactual under each candidate clause:

- ``SQ``: the status quo Z3-side clause, ``{w}`` at evaluation world ``w``
  when the counterfactual is true there (context-dependent).
- ``SQpy``: the status quo Python-side clause, every world where the
  counterfactual is true (context-free, not closed under fusion).
- ``I``: imposition-local, ``s`` verifies iff every ``A``-verifier imposed on
  ``s`` reaches only ``B``-worlds.
- ``W``: fusion closure of the worlds where the counterfactual is true.
- ``L``: settlers, states every world above which makes it true.
- ``M``: parthood-minimal settlers.
- ``MC``: fusion closure of the minimal settlers.
- ``IL``: imposition-local settlers, ``V_I`` intersected with ``V_L``.
- ``ILC``: fusion closure of ``IL``; ``ILM``: parthood-minimal members of
  ``IL``; ``ILMC``: fusion closure of ``ILM`` (the exact clause: minimal
  settled-imposition verifiers, fused).
- ``SR``: settler that is a fusion of maximal antecedent-compatible parts
  (one per antecedent verifier with alternatives) of some world containing
  it; ``SRC``: its fusion closure.
- Exact-imposition family, in which the consequent must be *verified* at each
  alternative by a designated part and the candidate is the fusion of those
  parts: ``XS`` (alternatives taken to the candidate itself), ``XSr`` (with
  the surviving remainder fused in), ``XPe`` (alternatives taken to some
  world containing the candidate), ``XPer``, ``XPa`` (to every such world),
  ``XPar``, ``XSx`` (a single consequent verifier below some alternative).
- Settled variants of the exact family: ``SB`` (settler in the closure of the
  consequent's verifiers), ``SAB`` (settler in the closure of antecedent and
  consequent verifiers), ``SX``/``SXr`` (settler and ``XPe``/``XPer``),
  ``SXC`` (closure of ``SX``).
- ``XE``: the exact composition over the alternatives of the evaluation world
  (context-dependent, like ``SQ``).

Falsifier sets are the polarity duals stated per clause in ``proposition``;
for the exact family a falsifier is a fusion of consequent-falsifiers over a
nonempty subset of the alternatives.
"""

from __future__ import annotations

import itertools
import random
from dataclasses import dataclass
from typing import Any, Callable, Dict, FrozenSet, Iterable, Iterator, List, Optional, Sequence, Set, Tuple

#: Truth-set baselines (disqualified as candidates; comparison columns only).
BASELINE_KEYS: Tuple[str, ...] = ("W", "L", "M", "MC")
#: Clauses built from imposition on the candidate state.
IMPOSITION_KEYS: Tuple[str, ...] = ("I", "IL", "ILC", "ILM", "ILMC")
#: Settlers composed from surviving antecedent-compatible remainders.
REMAINDER_KEYS: Tuple[str, ...] = ("SR", "SRC")
#: Exact-imposition family (consequent verified by a designated part).
EXACT_KEYS: Tuple[str, ...] = ("XS", "XSr", "XPe", "XPer", "XPa", "XPar", "XSx")
#: Settler-guarded members of the exact family.
SETTLED_EXACT_KEYS: Tuple[str, ...] = ("SB", "SAB", "SX", "SXr", "SXC")
CANDIDATE_KEYS: Tuple[str, ...] = (
    IMPOSITION_KEYS + BASELINE_KEYS + REMAINDER_KEYS + EXACT_KEYS + SETTLED_EXACT_KEYS
)
#: Clauses whose verifier set depends on the evaluation world.
CONTEXT_DEPENDENT_KEYS: Tuple[str, ...] = ("SQ", "XE")
STATUS_QUO_KEYS: Tuple[str, ...] = ("SQ", "SQpy")
ALL_KEYS: Tuple[str, ...] = STATUS_QUO_KEYS + ("XE",) + CANDIDATE_KEYS

StateSet = FrozenSet[int]


# ---------------------------------------------------------------------------
# Lattice primitives
# ---------------------------------------------------------------------------

def is_part_of(s: int, t: int) -> bool:
    """``s`` is a part of ``t``."""
    return s & t == s


def is_proper_part_of(s: int, t: int) -> bool:
    """``s`` is a part of ``t`` and distinct from it."""
    return s & t == s and s != t


def fusion(s: int, t: int) -> int:
    """The fusion of two states."""
    return s | t


def atoms_of(s: int) -> List[int]:
    """The atomic (single-bit) parts of ``s``."""
    return [1 << i for i in range(s.bit_length()) if s >> i & 1]


def fusion_closure(states: Iterable[int]) -> StateSet:
    """The set of fusions of nonempty subsets of ``states``."""
    closed: Set[int] = set(states)
    frontier = list(closed)
    while frontier:
        new: List[int] = []
        for s in frontier:
            for t in list(closed):
                u = s | t
                if u not in closed:
                    closed.add(u)
                    new.append(u)
        frontier = new
    return frozenset(closed)


def minimal_elements(states: Iterable[int]) -> StateSet:
    """The parthood-minimal members of ``states``."""
    pool = set(states)
    return frozenset(s for s in pool if not any(is_proper_part_of(t, s) for t in pool))


def is_fusion_closed(states: Iterable[int]) -> Optional[Tuple[int, int]]:
    """``None`` when closed under fusion, else a witness pair whose fusion is missing."""
    pool = set(states)
    for s in pool:
        for t in pool:
            if s | t not in pool:
                return (s, t)
    return None


def composable(s: int, slots: Sequence[Sequence[int]]) -> bool:
    """``s`` is the fusion of one option drawn from every slot.

    Options are expected to be parts of ``s`` already; an empty slot makes
    composition impossible, and with no slots only the null state composes.
    """
    if any(not options for options in slots):
        return False
    if not slots:
        return s == 0
    ordered = sorted(slots, key=len)
    seen: Set[Tuple[int, int]] = set()

    def extend(i: int, covered: int) -> bool:
        if i == len(ordered):
            return covered == s
        key = (i, covered)
        if key in seen:
            return False
        seen.add(key)
        return any(extend(i + 1, covered | option) for option in ordered[i])

    return extend(0, 0)


def composable_subset(s: int, slots: Sequence[Sequence[int]]) -> bool:
    """``s`` is the fusion of one option each from a *nonempty* subset of the slots.

    Because any option may be taken from whichever slot offers it, this is
    membership of ``s`` in the fusion closure of the offered parts of ``s``.
    """
    if s == 0:
        return any(0 in options for options in slots)
    offered = sorted({o for options in slots for o in options if is_part_of(o, s)})
    return s in fusion_closure(offered) if offered else False


# ---------------------------------------------------------------------------
# Frames and interpretations
# ---------------------------------------------------------------------------

class Frame:
    """A finite state space with a downward-closed set of possible states.

    World states are the maximal possible states.  Every possible state is a
    part of some world (the lattice is finite), which the measurements rely
    on when they say a possible non-world verifier is a *proper* part of a
    world.
    """

    def __init__(self, n: int, possible: Iterable[int], atom_names: Optional[Sequence[str]] = None) -> None:
        if n < 1:
            raise ValueError("a frame needs at least one atom")
        self.n = n
        self.size = 1 << n
        self.states: Tuple[int, ...] = tuple(range(self.size))
        self.possible: StateSet = frozenset(possible)
        if 0 not in self.possible:
            raise ValueError("the null state must be possible")
        for s in self.possible:
            if s >= self.size:
                raise ValueError(f"state {s} lies outside a {n}-atom frame")
            for t in self.states:
                if is_part_of(t, s) and t not in self.possible:
                    raise ValueError(f"possibility is not downward closed at {t} < {s}")
        self.worlds: StateSet = frozenset(
            w for w in self.possible
            if not any(is_proper_part_of(w, v) for v in self.possible)
        )
        if atom_names is None:
            atom_names = [chr(ord('a') + i) for i in range(n)]
        if len(atom_names) != n:
            raise ValueError("one name per atom is required")
        self.atom_names = tuple(atom_names)
        self._mcp_cache: Dict[Tuple[int, int], StateSet] = {}
        self._alt_cache: Dict[Tuple[int, int], StateSet] = {}

    @classmethod
    def from_worlds(cls, n: int, worlds: Iterable[int], atom_names: Optional[Sequence[str]] = None) -> "Frame":
        """The frame whose possible states are the parts of the given worlds."""
        possible = {t for w in worlds for t in range(1 << n) if is_part_of(t, w)}
        frame = cls(n, possible, atom_names)
        declared = frozenset(worlds)
        if frame.worlds != declared:
            raise ValueError(
                f"declared worlds {sorted(declared)} are not the maximal possible states {sorted(frame.worlds)}"
            )
        return frame

    def state(self, *atoms: str) -> int:
        """The state that is the fusion of the named atoms."""
        s = 0
        for name in atoms:
            s |= 1 << self.atom_names.index(name)
        return s

    def fmt(self, s: int) -> str:
        """Render a state as a dotted list of atom names (``□`` for the null state)."""
        if s == 0:
            return "□"
        return ".".join(self.atom_names[i] for i in range(self.n) if s >> i & 1)

    def fmt_set(self, states: Iterable[int]) -> List[str]:
        return [self.fmt(s) for s in sorted(states)]

    def is_possible(self, s: int) -> bool:
        return s in self.possible

    def compatible(self, s: int, t: int) -> bool:
        return (s | t) in self.possible

    def max_compatible_parts(self, s: int, a: int) -> StateSet:
        """The maximal parts of ``s`` compatible with ``a``: ``[s]_a``."""
        key = (s, a)
        if key not in self._mcp_cache:
            parts = [r for r in self.states if is_part_of(r, s) and self.compatible(r, a)]
            self._mcp_cache[key] = frozenset(
                r for r in parts if not any(is_proper_part_of(r, q) for q in parts)
            )
        return self._mcp_cache[key]

    def alternatives(self, s: int, a: int) -> StateSet:
        """The worlds containing ``a`` fused with some maximal ``a``-compatible part of ``s``."""
        key = (s, a)
        if key not in self._alt_cache:
            parts = self.max_compatible_parts(s, a)
            self._alt_cache[key] = frozenset(
                u for u in self.worlds
                if is_part_of(a, u) and any(is_part_of(r, u) for r in parts)
            )
        return self._alt_cache[key]

    def worlds_above(self, s: int) -> StateSet:
        return frozenset(w for w in self.worlds if is_part_of(s, w))

    def to_dict(self) -> Dict[str, Any]:
        return {
            "n": self.n,
            "atoms": list(self.atom_names),
            "worlds": self.fmt_set(self.worlds),
            "possible": self.fmt_set(self.possible),
        }


class Interpretation:
    """Verifier and falsifier sets for sentence letters."""

    def __init__(self, letters: Dict[str, Tuple[Iterable[int], Iterable[int]]]) -> None:
        self.letters: Dict[str, Tuple[StateSet, StateSet]] = {
            name: (frozenset(v), frozenset(f)) for name, (v, f) in letters.items()
        }

    def __getitem__(self, name: str) -> Tuple[StateSet, StateSet]:
        return self.letters[name]

    def to_dict(self, frame: Frame) -> Dict[str, Any]:
        return {
            name: {"verifiers": frame.fmt_set(v), "falsifiers": frame.fmt_set(f)}
            for name, (v, f) in self.letters.items()
        }


def letter_constraints_hold(frame: Frame, v: Iterable[int], f: Iterable[int],
                            contingent: bool = True, non_null: bool = True) -> bool:
    """The classical constraints the logos proposition class imposes on a letter.

    Fusion closure of each set, no verifier compatible with a falsifier, every
    possible state compatible with a verifier or a falsifier, and (optionally)
    a possible verifier, a possible falsifier, and no null member.
    """
    vs, fs = frozenset(v), frozenset(f)
    if is_fusion_closed(vs) is not None or is_fusion_closed(fs) is not None:
        return False
    if any(frame.compatible(x, y) for x in vs for y in fs):
        return False
    pool = vs | fs
    for s in frame.possible:
        if not any(frame.compatible(s, y) for y in pool):
            return False
    if contingent and (not any(x in frame.possible for x in vs) or not any(y in frame.possible for y in fs)):
        return False
    if non_null and 0 in pool:
        return False
    return True


# ---------------------------------------------------------------------------
# Formulas
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Atom:
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Neg:
    arg: Any

    def __str__(self) -> str:
        return f"¬{self.arg}"


@dataclass(frozen=True)
class And:
    left: Any
    right: Any

    def __str__(self) -> str:
        return f"({self.left} ∧ {self.right})"


@dataclass(frozen=True)
class Or:
    left: Any
    right: Any

    def __str__(self) -> str:
        return f"({self.left} ∨ {self.right})"


@dataclass(frozen=True)
class Top:
    def __str__(self) -> str:
        return "⊤"


@dataclass(frozen=True)
class Bot:
    def __str__(self) -> str:
        return "⊥"


@dataclass(frozen=True)
class Box:
    arg: Any

    def __str__(self) -> str:
        return f"□{self.arg}"


@dataclass(frozen=True)
class CF:
    """``left □→ right`` whose *verifier* clause is the candidate named by ``key``."""
    key: str
    left: Any
    right: Any

    def __str__(self) -> str:
        return f"({self.left} □→[{self.key}] {self.right})"


def Diamond(arg: Any) -> Any:
    return Neg(Box(Neg(arg)))


def Might(key: str, left: Any, right: Any) -> Any:
    """``left ◇→ right`` as ``¬(left □→ ¬right)``, the defined might-counterfactual."""
    return Neg(CF(key, left, Neg(right)))


def Implies(left: Any, right: Any) -> Any:
    return Or(Neg(left), right)


# ---------------------------------------------------------------------------
# Evaluation
# ---------------------------------------------------------------------------

class Evaluator:
    """Truth and verifier/falsifier computation over one frame and interpretation.

    ``eval_world`` is only consulted by the status-quo clause ``SQ``, whose
    verifier set depends on it; every candidate clause ignores it.
    """

    def __init__(self, frame: Frame, interp: Interpretation, eval_world: Optional[int] = None) -> None:
        self.frame = frame
        self.interp = interp
        self.eval_world = eval_world
        self._prop_cache: Dict[Any, Tuple[StateSet, StateSet]] = {}
        self._truth_cache: Dict[Tuple[Any, int], bool] = {}
        self._false_cache: Dict[Tuple[Any, int], bool] = {}

    # -- truth clauses ----------------------------------------------------

    def truth(self, phi: Any, w: int) -> bool:
        """``phi`` is true at ``w`` by the recursive truth clauses."""
        key = (phi, w)
        if key in self._truth_cache:
            return self._truth_cache[key]
        frame = self.frame
        if isinstance(phi, Atom):
            result = any(is_part_of(v, w) for v in self.interp[phi.name][0])
        elif isinstance(phi, Neg):
            result = self.falsity(phi.arg, w)
        elif isinstance(phi, And):
            result = self.truth(phi.left, w) and self.truth(phi.right, w)
        elif isinstance(phi, Or):
            result = self.truth(phi.left, w) or self.truth(phi.right, w)
        elif isinstance(phi, Top):
            result = True
        elif isinstance(phi, Bot):
            result = False
        elif isinstance(phi, Box):
            result = all(self.truth(phi.arg, u) for u in frame.worlds)
        elif isinstance(phi, CF):
            result = self.cf_true(phi.left, phi.right, w)
        else:
            raise TypeError(f"unknown formula {phi!r}")
        self._truth_cache[key] = result
        return result

    def falsity(self, phi: Any, w: int) -> bool:
        """``phi`` is false at ``w`` by the recursive falsity clauses."""
        key = (phi, w)
        if key in self._false_cache:
            return self._false_cache[key]
        frame = self.frame
        if isinstance(phi, Atom):
            result = any(is_part_of(f, w) for f in self.interp[phi.name][1])
        elif isinstance(phi, Neg):
            result = self.truth(phi.arg, w)
        elif isinstance(phi, And):
            result = self.falsity(phi.left, w) or self.falsity(phi.right, w)
        elif isinstance(phi, Or):
            result = self.falsity(phi.left, w) and self.falsity(phi.right, w)
        elif isinstance(phi, Top):
            result = False
        elif isinstance(phi, Bot):
            result = True
        elif isinstance(phi, Box):
            result = any(self.falsity(phi.arg, u) for u in frame.worlds)
        elif isinstance(phi, CF):
            result = self.cf_false(phi.left, phi.right, w)
        else:
            raise TypeError(f"unknown formula {phi!r}")
        self._false_cache[key] = result
        return result

    def cf_true(self, left: Any, right: Any, s: int) -> bool:
        """The counterfactual truth clause with ``s`` in the world slot.

        For every verifier ``a`` of ``left`` and every world ``u`` in
        ``Alt(s, a)``, ``right`` is true at ``u``.  At a world this is the
        shared truth clause; at an arbitrary state it is Reading I.
        """
        verifiers = self.proposition(left)[0]
        return all(
            self.truth(right, u)
            for a in verifiers
            for u in self.frame.alternatives(s, a)
        )

    def cf_false(self, left: Any, right: Any, s: int) -> bool:
        """The dual of ``cf_true``: some imposition reaches a world falsifying ``right``."""
        verifiers = self.proposition(left)[0]
        return any(
            self.falsity(right, u)
            for a in verifiers
            for u in self.frame.alternatives(s, a)
        )

    def truth_set(self, phi: Any) -> StateSet:
        return frozenset(w for w in self.frame.worlds if self.truth(phi, w))

    def falsity_set(self, phi: Any) -> StateSet:
        return frozenset(w for w in self.frame.worlds if self.falsity(phi, w))

    # -- verifier clauses -------------------------------------------------

    def proposition(self, phi: Any) -> Tuple[StateSet, StateSet]:
        """The verifier and falsifier sets of ``phi``."""
        if phi in self._prop_cache:
            return self._prop_cache[phi]
        frame = self.frame
        if isinstance(phi, Atom):
            result = self.interp[phi.name]
        elif isinstance(phi, Neg):
            v, f = self.proposition(phi.arg)
            result = (f, v)
        elif isinstance(phi, And):
            lv, lf = self.proposition(phi.left)
            rv, rf = self.proposition(phi.right)
            result = (product(lv, rv), coproduct(lf, rf))
        elif isinstance(phi, Or):
            lv, lf = self.proposition(phi.left)
            rv, rf = self.proposition(phi.right)
            result = (coproduct(lv, rv), product(lf, rf))
        elif isinstance(phi, Top):
            result = (frozenset(frame.states), frozenset())
        elif isinstance(phi, Bot):
            result = (frozenset(), frozenset({0}))
        elif isinstance(phi, Box):
            holds = all(self.truth(phi.arg, u) for u in frame.worlds)
            result = (frozenset({0}), frozenset()) if holds else (frozenset(), frozenset({0}))
        elif isinstance(phi, CF):
            result = self.counterfactual_proposition(phi.key, phi.left, phi.right)
        else:
            raise TypeError(f"unknown formula {phi!r}")
        self._prop_cache[phi] = result
        return result

    def counterfactual_proposition(self, key: str, left: Any, right: Any) -> Tuple[StateSet, StateSet]:
        """Verifiers and falsifiers of ``left □→ right`` under candidate ``key``."""
        frame = self.frame
        if key in CONTEXT_DEPENDENT_KEYS:
            return self.context_dependent_proposition(key, left, right)
        true_worlds = frozenset(w for w in frame.worlds if self.cf_true(left, right, w))
        false_worlds = frozenset(w for w in frame.worlds if self.cf_false(left, right, w))
        if key == "SQpy":
            return true_worlds, false_worlds
        if key == "I":
            return self.imposition_local(left, right)
        if key == "W":
            return fusion_closure(true_worlds), fusion_closure(false_worlds)
        if key == "L":
            return self.settlers(true_worlds, false_worlds)
        if key == "M":
            lv, lf = self.settlers(true_worlds, false_worlds)
            return minimal_elements(lv), minimal_elements(lf)
        if key == "MC":
            lv, lf = self.settlers(true_worlds, false_worlds)
            return closure_or_empty(minimal_elements(lv)), closure_or_empty(minimal_elements(lf))
        if key in ("IL", "ILC", "ILM", "ILMC"):
            iv, if_ = self.imposition_local(left, right)
            lv, lf = self.settlers(true_worlds, false_worlds)
            v, f = iv & lv, if_ & lf
            if key == "IL":
                return v, f
            if key == "ILC":
                return closure_or_empty(v), closure_or_empty(f)
            v, f = minimal_elements(v), minimal_elements(f)
            if key == "ILM":
                return v, f
            return closure_or_empty(v), closure_or_empty(f)
        if key in REMAINDER_KEYS:
            return self.remainder_proposition(key, left, true_worlds, false_worlds)
        if key in EXACT_KEYS or key in SETTLED_EXACT_KEYS:
            return self.exact_proposition(key, left, right, true_worlds, false_worlds)
        raise ValueError(f"unknown candidate {key!r}")

    def context_dependent_proposition(self, key: str, left: Any, right: Any) -> Tuple[StateSet, StateSet]:
        """``SQ`` and ``XE``: clauses that read the evaluation world."""
        w = self.eval_world
        if w is None:
            raise ValueError(f"the context-dependent clause {key!r} needs an evaluation world")
        if key == "SQ":
            v = frozenset({w}) if self.cf_true(left, right, w) else frozenset()
            f = frozenset({w}) if self.cf_false(left, right, w) else frozenset()
            return v, f
        va = self.proposition(left)[0]
        vb, fb = self.proposition(right)
        v, f = set(), set()
        for s in self.frame.states:
            cv, cf = self.composed_at(s, w, va, vb, fb, False)
            if cv:
                v.add(s)
            if cf:
                f.add(s)
        return frozenset(v), frozenset(f)

    # -- exact-imposition composition ---------------------------------------

    def imposition_pairs(self, base: int, va: StateSet) -> List[Tuple[int, int]]:
        """``P(base)``: every ``(a, u)`` with ``a`` an antecedent verifier and ``u ∈ Alt(base, a)``."""
        return [(a, u) for a in va for u in self.frame.alternatives(base, a)]

    def consequent_options(self, s: int, u: int, vb: StateSet) -> List[int]:
        """Consequent verifiers (or falsifiers) below both the alternative ``u`` and ``s``."""
        return [b for b in vb if is_part_of(b, u) and is_part_of(b, s)]

    def consequent_remainder_options(self, s: int, base: int, a: int, u: int, vb: StateSet) -> List[int]:
        """``consequent_options`` each fused with a surviving remainder ``r ∈ [base]_a`` below ``s``."""
        remainders = [
            r for r in self.frame.max_compatible_parts(base, a)
            if is_part_of(a | r, u) and is_part_of(r, s)
        ]
        return sorted({
            b | r
            for b in vb if is_part_of(b, u) and is_part_of(b, s)
            for r in remainders
        })

    def composed_at(self, s: int, base: int, va: StateSet, vb: StateSet, fb: StateSet,
                    with_remainder: bool) -> Tuple[bool, bool]:
        """``(verifies, falsifies)``: ``s`` composed over the alternatives of ``base``.

        Verification composes one consequent verifier per alternative;
        falsification composes consequent falsifiers over a nonempty subset
        of the alternatives.
        """
        pairs = self.imposition_pairs(base, va)
        if with_remainder:
            v_slots = [self.consequent_remainder_options(s, base, a, u, vb) for a, u in pairs]
            f_slots = [self.consequent_remainder_options(s, base, a, u, fb) for a, u in pairs]
        else:
            v_slots = [self.consequent_options(s, u, vb) for _, u in pairs]
            f_slots = [self.consequent_options(s, u, fb) for _, u in pairs]
        return composable(s, v_slots), composable_subset(s, f_slots)

    def exact_proposition(self, key: str, left: Any, right: Any,
                          true_worlds: StateSet, false_worlds: StateSet) -> Tuple[StateSet, StateSet]:
        """The exact-imposition family and its settler-guarded variants."""
        frame = self.frame
        states = frame.states
        va = self.proposition(left)[0]
        vb, fb = self.proposition(right)
        lv, lf = self.settlers(true_worlds, false_worlds)

        def composed_below_some_world(with_remainder: bool, settle: bool) -> Tuple[StateSet, StateSet]:
            v, f = set(), set()
            for s in states:
                if settle and s not in lv and s not in lf:
                    continue
                for w in frame.worlds_above(s):
                    cv, cf = self.composed_at(s, w, va, vb, fb, with_remainder)
                    if cv and (not settle or s in lv):
                        v.add(s)
                    if cf and (not settle or s in lf):
                        f.add(s)
            return frozenset(v), frozenset(f)

        if key in ("XS", "XSr"):
            v, f = set(), set()
            for s in states:
                cv, cf = self.composed_at(s, s, va, vb, fb, key == "XSr")
                if cv:
                    v.add(s)
                if cf:
                    f.add(s)
            return frozenset(v), frozenset(f)
        if key in ("XPe", "XPer"):
            return composed_below_some_world(key == "XPer", settle=False)
        if key in ("XPa", "XPar"):
            v, f = set(), set()
            for s in states:
                results = [self.composed_at(s, w, va, vb, fb, key == "XPar") for w in frame.worlds_above(s)]
                if all(cv for cv, _ in results):
                    v.add(s)
                if all(cf for _, cf in results):
                    f.add(s)
            return frozenset(v), frozenset(f)
        if key == "XSx":
            v, f = set(), set()
            for s in states:
                pairs = self.imposition_pairs(s, va)
                if s in vb and any(is_part_of(s, u) for _, u in pairs):
                    v.add(s)
                if s in fb and any(is_part_of(s, u) for _, u in pairs):
                    f.add(s)
            return frozenset(v), frozenset(f)
        if key == "SB":
            return lv & fusion_closure(vb), lf & fusion_closure(fb)
        if key == "SAB":
            return lv & fusion_closure(va | vb), lf & fusion_closure(va | fb)
        if key in ("SX", "SXr"):
            return composed_below_some_world(key == "SXr", settle=True)
        if key == "SXC":
            v, f = composed_below_some_world(False, settle=True)
            return closure_or_empty(v), closure_or_empty(f)
        raise ValueError(f"unknown exact clause {key!r}")

    def remainder_proposition(self, key: str, left: Any,
                              true_worlds: StateSet, false_worlds: StateSet) -> Tuple[StateSet, StateSet]:
        """``SR``/``SRC``: settlers composed of surviving antecedent-compatible remainders."""
        frame = self.frame
        va = self.proposition(left)[0]
        lv, lf = self.settlers(true_worlds, false_worlds)
        v, f = set(), set()
        for s in frame.states:
            if s not in lv and s not in lf:
                continue
            for w in frame.worlds_above(s):
                slots = [
                    [r for r in frame.max_compatible_parts(w, a) if is_part_of(r, s)]
                    for a in va if frame.alternatives(w, a)
                ]
                if composable(s, slots):
                    if s in lv:
                        v.add(s)
                    if s in lf:
                        f.add(s)
        if key == "SRC":
            return closure_or_empty(v), closure_or_empty(f)
        return frozenset(v), frozenset(f)

    def identical_proposition(self, phi: Any, psi: Any) -> bool:
        """``phi ≡ psi``: the same verifier set and the same falsifier set."""
        return self.proposition(phi) == self.proposition(psi)

    def imposition_local(self, left: Any, right: Any) -> Tuple[StateSet, StateSet]:
        """Reading I over every state."""
        v = frozenset(s for s in self.frame.states if self.cf_true(left, right, s))
        f = frozenset(s for s in self.frame.states if self.cf_false(left, right, s))
        return v, f

    def settlers(self, true_worlds: StateSet, false_worlds: StateSet) -> Tuple[StateSet, StateSet]:
        """Reading L: states all of whose world-completions are true (dually, false) worlds."""
        frame = self.frame
        v = frozenset(s for s in frame.states if all(w in true_worlds for w in frame.worlds_above(s)))
        f = frozenset(s for s in frame.states if all(w in false_worlds for w in frame.worlds_above(s)))
        return v, f


def product(xs: Iterable[int], ys: Iterable[int]) -> StateSet:
    """All pairwise fusions."""
    return frozenset(x | y for x in xs for y in ys)


def coproduct(xs: Iterable[int], ys: Iterable[int]) -> StateSet:
    """Union plus all pairwise fusions."""
    xs, ys = frozenset(xs), frozenset(ys)
    return xs | ys | product(xs, ys)


def closure_or_empty(states: Iterable[int]) -> StateSet:
    """Fusion closure, with the empty set closed to itself."""
    pool = frozenset(states)
    return fusion_closure(pool) if pool else pool


# ---------------------------------------------------------------------------
# Measurement
# ---------------------------------------------------------------------------

def measure(key: str, left: Any, right: Any, frame: Frame, interp: Interpretation,
            eval_world: Optional[int] = None) -> Dict[str, Any]:
    """Measure the structural properties of ``left □→ right`` under candidate ``key``.

    Every entry that can fail carries a witness (rendered with atom names)
    or ``None``.  Exclusivity is reported in two strengths: over possible
    states (no possible state both verifies and falsifies) and in the
    compatibility form the logos letter constraints use (no verifier is
    compatible with any falsifier).
    """
    ev = Evaluator(frame, interp, eval_world)
    phi = CF(key, left, right)
    v, f = ev.proposition(phi)
    true_worlds = frozenset(w for w in frame.worlds if ev.cf_true(left, right, w))
    false_worlds = frozenset(w for w in frame.worlds if ev.cf_false(left, right, w))
    fmt, fmt_set = frame.fmt, frame.fmt_set
    possible = frame.possible

    def pair(p: Optional[Tuple[int, int]]) -> Optional[List[str]]:
        return None if p is None else [fmt(p[0]), fmt(p[1])]

    closure_v = is_fusion_closed(v)
    closure_f = is_fusion_closed(f)

    impossible_v = frozenset(s for s in v if s not in possible)
    impossible_f = frozenset(s for s in f if s not in possible)
    impossible_all = frozenset(s for s in frame.states if s not in possible)

    excl_possible = next((s for s in (v & f) if s in possible), None)
    excl_compat = next(((x, y) for x in v for y in f if frame.compatible(x, y)), None)

    exhaustive_witness = next(
        (w for w in frame.worlds
         if not any(is_part_of(x, w) for x in v) and not any(is_part_of(y, w) for y in f)),
        None,
    )

    bridge_v = next(((x, w) for x in v for w in frame.worlds_above(x) if w not in true_worlds), None)
    bridge_f = next(((y, w) for y in f for w in frame.worlds_above(y) if w not in false_worlds), None)
    suff_v = next((w for w in true_worlds if not any(is_part_of(x, w) for x in v)), None)
    suff_f = next((w for w in false_worlds if not any(is_part_of(y, w) for y in f)), None)
    glut_worlds = frozenset(
        w for w in frame.worlds
        if any(is_part_of(x, w) for x in v) and any(is_part_of(y, w) for y in f)
    )

    proper_v = frozenset(x for x in v if x in possible and x not in frame.worlds)
    proper_f = frozenset(y for y in f if y in possible and y not in frame.worlds)

    bivalent = all((w in true_worlds) != (w in false_worlds) for w in frame.worlds)
    contingent = bool(true_worlds) and bool(false_worlds)

    return {
        "candidate": key,
        "formula": str(phi),
        "eval_world": None if eval_world is None else fmt(eval_world),
        "true_worlds": fmt_set(true_worlds),
        "false_worlds": fmt_set(false_worlds),
        "bivalent_at_worlds": bivalent,
        "contingent": contingent,
        "verifiers": fmt_set(v),
        "falsifiers": fmt_set(f),
        "closure_V": closure_v is None,
        "closure_V_witness": pair(closure_v),
        "closure_F": closure_f is None,
        "closure_F_witness": pair(closure_f),
        "impossible_V_count": len(impossible_v),
        "impossible_F_count": len(impossible_f),
        "impossible_vacuous_V": impossible_all <= v,
        "impossible_vacuous_F": impossible_all <= f,
        "impossible_harmless_V": not any(frame.worlds_above(s) for s in impossible_v),
        "impossible_harmless_F": not any(frame.worlds_above(s) for s in impossible_f),
        "exclusive_possible": excl_possible is None,
        "exclusive_possible_witness": None if excl_possible is None else fmt(excl_possible),
        "exclusive_compat": excl_compat is None,
        "exclusive_compat_witness": pair(excl_compat),
        "exhaustive": exhaustive_witness is None,
        "exhaustive_witness": None if exhaustive_witness is None else fmt(exhaustive_witness),
        "bridge_sound_V": bridge_v is None,
        "bridge_sound_V_witness": pair(bridge_v),
        "bridge_sound_F": bridge_f is None,
        "bridge_sound_F_witness": pair(bridge_f),
        "bridge_sufficient_V": suff_v is None,
        "bridge_sufficient_V_witness": None if suff_v is None else fmt(suff_v),
        "bridge_sufficient_F": suff_f is None,
        "bridge_sufficient_F_witness": None if suff_f is None else fmt(suff_f),
        "bridge_glut": bool(glut_worlds),
        "bridge_glut_worlds": fmt_set(glut_worlds),
        "proper_possible_V": fmt_set(proper_v),
        "proper_possible_F": fmt_set(proper_f),
    }


PROPERTY_NAMES: Tuple[str, ...] = (
    "closure_V", "closure_F",
    "impossible_vacuous_V", "impossible_vacuous_F",
    "impossible_harmless_V", "impossible_harmless_F",
    "exclusive_possible", "exclusive_compat", "exhaustive",
    "bridge_sound_V", "bridge_sound_F",
    "bridge_sufficient_V", "bridge_sufficient_F",
)


#: The properties a structure sweep counts failures of, in table order.
SWEEP_PROPERTIES: Tuple[str, ...] = (
    "closure_V", "closure_F", "exclusive_possible", "exclusive_compat", "exhaustive",
    "bridge_sound_V", "bridge_sound_F", "bridge_sufficient_V", "bridge_sufficient_F",
    "impossible_harmless_V", "impossible_harmless_F",
)


def structure_sweep(models: Iterable[Tuple["Frame", "Interpretation"]], keys: Sequence[str],
                    left: Any, right: Any) -> Dict[str, Dict[str, Any]]:
    """Per key: how many models fail each property, proper-verifier tallies, first witnesses.

    Returns ``{key: {"models": n, "fails": {property: count}, "proper": {...},
    "witness": {property: serialized model}}}``.  ``proper`` counts the
    contingent models (true and false somewhere) and, among them, those with
    a possible verifier / falsifier properly below a world, those whose
    proper verifier comes with every property intact, and the models on
    which the proposition is empty.
    """
    result: Dict[str, Dict[str, Any]] = {
        key: {
            "models": 0,
            "fails": {prop: 0 for prop in SWEEP_PROPERTIES},
            "proper": {
                "contingent_models": 0,
                "contingent_with_proper_V": 0,
                "contingent_with_proper_F": 0,
                "contingent_proper_V_and_all_props": 0,
                "empty_proposition": 0,
            },
            "witness": {},
        }
        for key in keys
    }
    for frame, interp in models:
        for key in keys:
            entry = result[key]
            entry["models"] += 1
            record = measure(key, left, right, frame, interp)
            for prop in SWEEP_PROPERTIES:
                if record[prop] is False:
                    entry["fails"][prop] += 1
                    entry["witness"].setdefault(prop, {
                        "model": model_to_dict(frame, interp),
                        "verifiers": record["verifiers"],
                        "falsifiers": record["falsifiers"],
                        "true_worlds": record["true_worlds"],
                        "witness": record.get(prop + "_witness"),
                    })
            proper = entry["proper"]
            if record["contingent"]:
                proper["contingent_models"] += 1
                if record["proper_possible_V"]:
                    proper["contingent_with_proper_V"] += 1
                if record["proper_possible_F"]:
                    proper["contingent_with_proper_F"] += 1
                if record["proper_possible_V"] and all(record[prop] for prop in SWEEP_PROPERTIES):
                    proper["contingent_proper_V_and_all_props"] += 1
            if not record["verifiers"] and not record["falsifiers"]:
                proper["empty_proposition"] += 1
    return result


def exact_sufficiency_mismatches(models: Iterable[Tuple["Frame", "Interpretation"]],
                                 left: Any, right: Any, key: str = "XPe") -> Tuple[int, int]:
    """``(true worlds checked, mismatches)`` for the exact-family characterization.

    Claim: an exact clause has a verifier below a true world ``w`` iff every
    ``(a, u)`` in ``P(w)`` has a consequent verifier that is part of both
    ``u`` and ``w``.
    """
    checked = mismatches = 0
    for frame, interp in models:
        ev = Evaluator(frame, interp)
        va = ev.proposition(left)[0]
        vb = ev.proposition(right)[0]
        v, _ = ev.proposition(CF(key, left, right))
        for w in frame.worlds:
            if not ev.cf_true(left, right, w):
                continue
            checked += 1
            has_verifier = any(is_part_of(s, w) for s in v)
            predicted = all(
                any(is_part_of(b, u) and is_part_of(b, w) for b in vb)
                for a in va for u in frame.alternatives(w, a)
            )
            if has_verifier != predicted:
                mismatches += 1
    return checked, mismatches


#: Nested-antecedent principles, with ``X := left □→ right`` under the candidate.
LOGIC_PRINCIPLES: Tuple[str, ...] = (
    "identity",        # X □→ X
    "modus_ponens",    # X, X □→ C ⊢ C
    "strengthening",   # X □→ C ⊢ (X ∧ D) □→ C
    "strict_to_cf",    # □(X → C) ⊢ X □→ C
    "cf_to_strict",    # X □→ C ⊢ □(X → C)
    "might_identity",  # (left ◇→ right) □→ (left ◇→ right)
)


def logic_failures(key: str, frame: "Frame", interp: "Interpretation",
                   left: Any, right: Any, c: Any, d: Any) -> Dict[str, bool]:
    """Which nested-antecedent principles fail at some world of one model."""
    ev = Evaluator(frame, interp)
    x = CF(key, left, right)
    x_might = Might(key, left, right)
    identity = CF(key, x, x)
    x_c = CF(key, x, c)
    xd_c = CF(key, And(x, d), c)
    strict = Box(Implies(x, c))
    might_identity = CF(key, x_might, x_might)
    failed = {name: False for name in LOGIC_PRINCIPLES}
    for w in frame.worlds:
        if not ev.truth(identity, w):
            failed["identity"] = True
        if ev.truth(x, w) and ev.truth(x_c, w) and not ev.truth(c, w):
            failed["modus_ponens"] = True
        if ev.truth(x_c, w) and not ev.truth(xd_c, w):
            failed["strengthening"] = True
        if ev.truth(strict, w) and not ev.truth(x_c, w):
            failed["strict_to_cf"] = True
        if ev.truth(x_c, w) and not ev.truth(strict, w):
            failed["cf_to_strict"] = True
        if not ev.truth(might_identity, w):
            failed["might_identity"] = True
    return failed


def logic_sweep(models: Iterable[Tuple["Frame", "Interpretation"]], keys: Sequence[str],
                left: Any, right: Any, c: Any, d: Any) -> Dict[str, Dict[str, Any]]:
    """Per key: count of models with a world at which each principle fails, with first witnesses."""
    result: Dict[str, Dict[str, Any]] = {
        key: {"models": 0, "fails": {name: 0 for name in LOGIC_PRINCIPLES}, "witness": {}}
        for key in keys
    }
    for frame, interp in models:
        for key in keys:
            entry = result[key]
            entry["models"] += 1
            failed = logic_failures(key, frame, interp, left, right, c, d)
            for name, did_fail in failed.items():
                if did_fail:
                    entry["fails"][name] += 1
                    entry["witness"].setdefault(name, model_to_dict(frame, interp))
    return result


def hyperintensionality_sweep(models: Iterable[Tuple["Frame", "Interpretation"]], keys: Sequence[str],
                              first: Tuple[Any, Any], second: Tuple[Any, Any]) -> Dict[str, Dict[str, Any]]:
    """Per key: same-truth-set pairs ``first □→`` vs ``second □→`` with distinct propositions."""
    result: Dict[str, Dict[str, Any]] = {
        key: {"models": 0, "same_truth_set": 0, "distinct_props": 0, "distinct_on_possible": 0, "witness": None}
        for key in keys
    }
    for frame, interp in models:
        for key in keys:
            entry = result[key]
            entry["models"] += 1
            ev = Evaluator(frame, interp)
            x, y = CF(key, *first), CF(key, *second)
            if ev.truth_set(x) != ev.truth_set(y):
                continue
            entry["same_truth_set"] += 1
            pv, pf = ev.proposition(x)
            qv, qf = ev.proposition(y)
            if (pv, pf) != (qv, qf):
                entry["distinct_props"] += 1
            poss = frame.possible
            if (pv & poss, pf & poss) != (qv & poss, qf & poss):
                entry["distinct_on_possible"] += 1
                if entry["witness"] is None:
                    entry["witness"] = {
                        "model": model_to_dict(frame, interp),
                        "truth_set": frame.fmt_set(ev.truth_set(x)),
                        "first_verifiers": frame.fmt_set(pv),
                        "second_verifiers": frame.fmt_set(qv),
                    }
    return result


# ---------------------------------------------------------------------------
# Small-N enumeration
# ---------------------------------------------------------------------------

def antichains(elements: Sequence[int]) -> Iterator[FrozenSet[int]]:
    """Every nonempty antichain (under parthood) drawn from ``elements``."""
    ordered = sorted(elements, key=lambda s: (bin(s).count("1"), s))

    def extend(start: int, chosen: List[int]) -> Iterator[FrozenSet[int]]:
        if chosen:
            yield frozenset(chosen)
        for i in range(start, len(ordered)):
            s = ordered[i]
            if any(is_part_of(t, s) or is_part_of(s, t) for t in chosen):
                continue
            chosen.append(s)
            yield from extend(i + 1, chosen)
            chosen.pop()

    yield from extend(0, [])


def enumerate_frames(n: int) -> Iterator[Frame]:
    """Every frame on ``n`` atoms whose worlds are nonzero states.

    A frame is determined by its world set, which may be any nonempty
    antichain of nonzero states; the null-state-only frame is excluded
    because no contingent letter can live on it.
    """
    nonzero = list(range(1, 1 << n))
    for worlds in antichains(nonzero):
        yield Frame.from_worlds(n, worlds)


def enumerate_letter_propositions(frame: Frame, contingent: bool = True, non_null: bool = True) -> List[Tuple[StateSet, StateSet]]:
    """Every ``(V, F)`` pair satisfying the letter constraints on ``frame``.

    Fusion-closed sets are generated from antichains of nonzero states, so
    the enumeration is exhaustive over fusion-closed non-null sets.
    """
    nonzero = list(range(1, frame.size))
    closed_sets = sorted({fusion_closure(gen) for gen in antichains(nonzero)}, key=sorted)
    if not non_null:
        closed_sets = closed_sets + [cs | {0} for cs in closed_sets] + [frozenset({0})]
    results: List[Tuple[StateSet, StateSet]] = []
    for v in closed_sets:
        for f in closed_sets:
            if letter_constraints_hold(frame, v, f, contingent=contingent, non_null=non_null):
                results.append((v, f))
    return results


def enumerate_models(n: int, letters: Sequence[str] = ("A", "B"), limit: Optional[int] = None,
                     seed: Optional[int] = None) -> Iterator[Tuple[Frame, Interpretation]]:
    """Frames on ``n`` atoms with an interpretation for each letter.

    Exhaustive when ``limit`` is ``None``; otherwise a reproducible random
    sample of ``limit`` models drawn with ``seed``.
    """
    frames = list(enumerate_frames(n))
    per_frame = [(frame, enumerate_letter_propositions(frame)) for frame in frames]
    per_frame = [(frame, props) for frame, props in per_frame if props]
    if limit is None:
        for frame, props in per_frame:
            for combo in itertools.product(props, repeat=len(letters)):
                yield frame, Interpretation(dict(zip(letters, combo)))
        return
    rng = random.Random(seed)
    for _ in range(limit):
        frame, props = rng.choice(per_frame)
        combo = [rng.choice(props) for _ in letters]
        yield frame, Interpretation(dict(zip(letters, combo)))


def search(n: int, predicate: Callable[[Frame, Interpretation], bool], letters: Sequence[str] = ("A", "B"),
           limit: Optional[int] = None, seed: Optional[int] = None) -> Tuple[Optional[Tuple[Frame, Interpretation]], int]:
    """First model on which ``predicate`` holds, with the number of models examined."""
    count = 0
    for frame, interp in enumerate_models(n, letters, limit, seed):
        count += 1
        if predicate(frame, interp):
            return (frame, interp), count
    return None, count


def model_to_dict(frame: Frame, interp: Interpretation) -> Dict[str, Any]:
    return {"frame": frame.to_dict(), "interpretation": interp.to_dict(frame)}


# ---------------------------------------------------------------------------
# Bridges to the Z3 model checker
# ---------------------------------------------------------------------------

def frame_from_model_structure(structure: Any) -> Frame:
    """Extract the frame of a solved ``LogosModelStructure``."""
    n = structure.semantics.N
    possible = {int(s.as_long()) for s in structure.z3_possible_states}
    frame = Frame(n, possible)
    worlds = frozenset(int(w.as_long()) for w in structure.z3_world_states)
    if frame.worlds != worlds:
        raise ValueError(f"model worlds {sorted(worlds)} differ from maximal possible states {sorted(frame.worlds)}")
    return frame


def interpretation_from_model_structure(structure: Any, syntax: Any) -> Interpretation:
    """Read the verify/falsify tables of every sentence letter from a solved model."""
    semantics = structure.semantics
    evaluate = structure.z3_model.evaluate
    letters: Dict[str, Tuple[Set[int], Set[int]]] = {}
    for sentence in syntax.sentence_letters:
        atom = sentence.sentence_letter
        v = {int(s.as_long()) for s in structure.all_states if bool(evaluate(semantics.verify(s, atom)))}
        f = {int(s.as_long()) for s in structure.all_states if bool(evaluate(semantics.falsify(s, atom)))}
        letters[sentence.name] = (v, f)
    return Interpretation(letters)


_OPERATOR_NAMES = {
    "\\neg": Neg,
    "\\wedge": And,
    "\\vee": Or,
    "\\Box": Box,
}


def formula_from_sentence(sentence: Any) -> Any:
    """Translate a parsed model-checker sentence (in primitive form) to an oracle formula.

    Counterfactual operators are recognised by name: ``\\boxright`` is the
    status quo ``SQ``; ``\\boxright{K}`` is candidate ``K``.
    """
    if sentence.sentence_letter is not None:
        return Atom(sentence.name)
    name = sentence.operator.name
    args = [formula_from_sentence(arg) for arg in (sentence.arguments or [])]
    if name == "\\top":
        return Top()
    if name == "\\bot":
        return Bot()
    if name in _OPERATOR_NAMES:
        return _OPERATOR_NAMES[name](*args)
    if name.startswith("\\boxright"):
        key = name[len("\\boxright"):] or "SQ"
        return CF(key, *args)
    raise ValueError(f"no oracle translation for operator {name!r}")
