"""Hand-built witness frames for the counterfactual verifier-clause measurements.

Every frame here is too large for the Z3 layer (7-9 atoms) and lives only in
the pure-Python oracle.  Each builder returns ``(Frame, Interpretation)`` with
named atoms, so tests address states as ``frame.state("a", "p'")``.

- ``frame_f3``: the eight-atom, four-world frame of the provenance research
  (report ``02_context-free-counterfactual-verifiers.md``, F3.1) that refutes
  Reading I.
- ``frame_g``: seven atoms, three worlds; separates the imposition-local
  settlers ``IL`` from the settlers ``L`` on possible states (the settlers
  ``y`` and ``a'`` survive no imposition of the antecedent verifier).
- ``frame_g2``: Frame G plus an atom ``x'`` and a world ``a.x'.b``, with
  letters ``C``, ``D`` such that ``A []-> B`` and ``C []-> D`` share a
  truth-set; separates the ``IL``-based propositions from the settler-based
  ones.
- ``frame_f3z``: Frame F3 plus an atom ``z`` and a world ``a'.p.p'.b.z`` at
  which the counterfactual is true but the only surviving remainder settles
  nothing (holism); the remainder clauses ``SR``/``SRC`` have no verifier.
- ``src_null_remainder_model``: four atoms, three worlds; at world ``d`` the
  antecedent verifier ``b`` is incompatible with ``d``, the remainder is the
  null state, and ``SR``/``SRC`` have no falsifier.
"""

from typing import Tuple

from model_checker.theory_lib.logos.subtheories.counterfactual.frame_oracle import (
    Frame,
    Interpretation,
)

F3_ATOMS = ["a", "a'", "p", "p'", "q", "q'", "b", "b'"]
G_ATOMS = ["a", "a'", "x", "y", "c", "b", "b'"]
G2_ATOMS = ["a", "a'", "x", "x'", "y", "c", "b", "b'"]
F3Z_ATOMS = F3_ATOMS + ["z"]


def _states(names):
    bit = {name: 1 << i for i, name in enumerate(names)}

    def st(*atoms):
        s = 0
        for atom in atoms:
            s |= bit[atom]
        return s

    return st


def frame_f3() -> Tuple[Frame, Interpretation]:
    """Report 02's F3.1 frame: worlds ``a'.p.p'.q.q'.b``, ``a.p.p'.b``, ``a.q.q'.b``, ``a.p.q.b'``."""
    st = _states(F3_ATOMS)
    worlds = [
        st("a'", "p", "p'", "q", "q'", "b"),
        st("a", "p", "p'", "b"),
        st("a", "q", "q'", "b"),
        st("a", "p", "q", "b'"),
    ]
    frame = Frame.from_worlds(8, worlds, F3_ATOMS)
    interp = Interpretation({
        "A": ({st("a")}, {st("a'")}),
        "B": ({st("b")}, {st("b'")}),
    })
    return frame, interp


def f3_worlds(frame: Frame) -> Tuple[int, int, int, int]:
    """``(w0, w1, w2, w3)`` of the F3 frame in the report's numbering."""
    return (
        frame.state("a'", "p", "p'", "q", "q'", "b"),
        frame.state("a", "p", "p'", "b"),
        frame.state("a", "q", "q'", "b"),
        frame.state("a", "p", "q", "b'"),
    )


def frame_g() -> Tuple[Frame, Interpretation]:
    """Seven atoms, worlds ``a.x.b'``, ``a.x.c.b``, ``a'.x.y.c.b``; separates ``IL`` from ``L``."""
    st = _states(G_ATOMS)
    worlds = [st("a", "x", "b'"), st("a", "x", "c", "b"), st("x", "y", "c", "b", "a'")]
    frame = Frame.from_worlds(7, worlds, G_ATOMS)
    # Only A and B: the research script's extra letters on this frame
    # (``C = ({c},{y})``) violate the letter constraints (``b'`` is
    # compatible with neither), so the same-truth-set comparison lives on
    # Frame G2, where every letter is compliant.
    interp = Interpretation({
        "A": ({st("a")}, {st("a'")}),
        "B": ({st("b")}, {st("b'")}),
    })
    return frame, interp


def frame_g2() -> Tuple[Frame, Interpretation]:
    """Frame G plus atom ``x'`` and world ``a.x'.b``; ``A []-> B`` and ``C []-> D`` share a truth-set."""
    st = _states(G2_ATOMS)
    worlds = [
        st("a", "x", "b'"),
        st("a", "x", "c", "b"),
        st("x", "y", "c", "b", "a'"),
        st("x'", "a", "b"),
    ]
    frame = Frame.from_worlds(8, worlds, G2_ATOMS)
    interp = Interpretation({
        "A": ({st("a")}, {st("a'")}),
        "B": ({st("b")}, {st("b'")}),
        "C": ({st("x")}, {st("x'")}),
        "D": ({st("b")}, {st("b'")}),
    })
    return frame, interp


def frame_f3z() -> Tuple[Frame, Interpretation]:
    """Frame F3 plus atom ``z`` and world ``a'.p.p'.b.z`` (the holistic true world)."""
    st = _states(F3Z_ATOMS)
    worlds = [
        st("a'", "p", "p'", "q", "q'", "b"),
        st("a", "p", "p'", "b"),
        st("a", "q", "q'", "b"),
        st("a", "p", "q", "b'"),
        st("a'", "p", "p'", "b", "z"),
    ]
    frame = Frame.from_worlds(9, worlds, F3Z_ATOMS)
    interp = Interpretation({
        "A": ({st("a")}, {st("a'")}),
        "B": ({st("b")}, {st("b'")}),
    })
    return frame, interp


def src_null_remainder_model() -> Tuple[Frame, Interpretation]:
    """Four atoms, worlds ``a.b``, ``b.c``, ``d``; ``|A| = ({b},{d})``, ``|B| = ({a,d,a.d},{c})``."""
    names = ["a", "b", "c", "d"]
    st = _states(names)
    worlds = [st("a", "b"), st("b", "c"), st("d")]
    frame = Frame.from_worlds(4, worlds, names)
    interp = Interpretation({
        "A": ({st("b")}, {st("d")}),
        "B": ({st("a"), st("d"), st("a", "d")}, {st("c")}),
    })
    return frame, interp


WITNESS_BUILDERS = {
    "F3": frame_f3,
    "G": frame_g,
    "G2": frame_g2,
    "F3z": frame_f3z,
    "SRC_null": src_null_remainder_model,
}

#: Declared world lists per witness frame, as dotted atom names.
DECLARED_WORLDS = {
    "F3": ["a'.p.p'.q.q'.b", "a.p.p'.b", "a.q.q'.b", "a.p.q.b'"],
    "G": ["a.x.b'", "a.x.c.b", "a'.x.y.c.b"],
    "G2": ["a.x.b'", "a.x.c.b", "a'.x.y.c.b", "a.x'.b"],
    "F3z": ["a'.p.p'.q.q'.b", "a.p.p'.b", "a.q.q'.b", "a.p.q.b'", "a'.p.p'.b.z"],
    "SRC_null": ["a.b", "b.c", "d"],
}
