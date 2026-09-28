"""Compile-once, interpret-many solver-free evaluator for the certificate encoder's emitted Z3
constraint list (`docs/ADEQUACY.md` section 7.3's leg (i)/(iii) A2-triangle differential; the
implementation plan for strengthening that comparison to per-candidate).

Sibling of `_lean_check.py`: a test-support module, not production `theory_lib` code, imported
by `tests/unit/test_pinned_eval.py` and by `tests/integration/test_certificate_a2_triangle.py`.

## Closed operator set

The encoder (`witness_constraints.py`'s `local_coherence_constraints`, `target_constraints`,
`fulfilment_constraints`, `box_faithfulness_constraints`, and `core.py`'s `_premise_behavior`/
`_conclusion_behavior`) emits exactly six kinds of Z3 `BoolRef` node: `And`, `Or`, `Not`,
`Implies`, `BoolRef == BoolRef` (`Z3_OP_EQ` -- Python's `==` on two `BoolRef`s, not `Z3_OP_IFF`),
and `AtMost` (`Z3_OP_PB_AT_MOST`). `compile_constraints` below handles exactly these, plus the
two leaf cases (a Z3 `True`/`False` constant, and a named Boolean atom). Any other node --
`Ite`, an arithmetic term, a quantifier, or one of the other pseudo-Boolean kinds (`AtLeast`,
`PbEq`, `PbGe`, `PbLe`) the encoder never emits -- raises `UnsupportedOperatorError`, never
silently defaults.

Every leaf atom belongs to exactly one of three families, matching `WitnessRegistry.bit`/
`WitnessRegistry.guess` (`witness_registry.py`) and `WitnessConstraintGenerator.sel`
(`witness_constraints.py`):

- `lab_{lasso}_{slot}_{formula!r}` -- is `formula` in the label at position-slot `slot` of
  lasso `lasso`;
- `bx_{formula!r}` -- the box guess for `formula` (always the child of a `Box` closure member);
- `sel_{t}` -- the one-hot target-position selector at raw position `t`.

## Compile-once, interpret-many

`compile_constraints` walks each `BoolRef` tree exactly once, interning every leaf atom's Z3
declaration name into an integer index (`CompiledConstraints.atom_index`), and builds one Python
closure per top-level constraint over that index. The hot per-candidate path
(`CompiledConstraints.evaluate_all`/`first_false`) touches only list indexing and native `bool`
operators -- no Z3 API call -- so its per-candidate cost is in the same order as
`certificate.recheck`'s, rather than paying a Z3 Python/C-API call per AST node per candidate.

`PinnedAssignmentBuilder` builds the pinned assignment row for one candidate directly from its
own data (`WitnessFamily`, `target_time`) -- the exact inverse of
`BimodalSemantics.extract_certificate` (`core.py:352-412`) -- and projects it into a preallocated
list indexed by the same `atom_index`, so the per-candidate path allocates no dict and hashes no
strings once `compile_and_bind` has run.

## Loud failure, never silent defaulting

- An atom index the compiled constraints reference but a candidate's assignment never populated
  reads as a sentinel `None` and raises `AtomNotAssignedError` on read, not `False`.
- Two distinct writes to the same atom name that disagree (e.g. two distinct closure formulas
  sharing an identical `repr()`) raise `AssignmentCollisionError` rather than silently keeping
  one value.
- `check_coverage` asserts, once per structure, that the assignment builder's produced key set
  is exactly the compiled constraints' `atom_index` key set -- neither a stray key nor a missing
  one -- raising `CoverageError` naming the mismatch.

## Coordination note: a future promotion

This module stays inside `tests/` (implementation plan Phase 2's declined-reorganization
record, `tests/README.md`'s "Declined Reorganizations" section): it already matches this
tree's own precedent of a leading-underscore, non-test, library-like module living alongside
the tests that import it, the same way `_lean_check.py` does. If a separately-tracked
trust-boundary decision promotes a checker built on this module's machinery onto the production
path, the natural destination is alongside `semantic/certificate.py` in `semantic/` (mirroring
that module's own home), with a narrowed public surface -- this module's existing explicit
`__all__` above already lists every name deliberately, which would ease that future move. Stated
here for coordination only; no promotion decision is made and no location is changed here.
"""

from __future__ import annotations

from typing import Callable, Dict, List, Mapping, Optional, Sequence, Tuple

import z3

from model_checker.theory_lib.bimodal.semantic.certificate import WitnessFamily
from model_checker.theory_lib.bimodal.semantic.formula import Formula

__all__ = [
    "UnsupportedOperatorError",
    "AtomNotAssignedError",
    "AssignmentCollisionError",
    "CoverageError",
    "CompiledConstraints",
    "PinnedAssignmentBuilder",
    "compile_constraints",
    "builder_for",
    "full_constraints",
    "compile_and_bind",
    "check_coverage",
]


class UnsupportedOperatorError(TypeError):
    """A Z3 AST node outside the closed six-operator set (see module docstring)."""


class AtomNotAssignedError(RuntimeError):
    """The hot-path evaluator read an atom index the assignment builder never populated."""


class AssignmentCollisionError(RuntimeError):
    """Two distinct writes to the same atom name disagreed for one candidate."""


class CoverageError(RuntimeError):
    """The assignment builder's produced key set does not exactly match `atom_index`'s."""


# An assignment "row": one entry per interned atom index, `None` where unpopulated.
Row = Sequence[Optional[bool]]
_Fn = Callable[[Row], bool]


def _atom_reader(index: int, name: str) -> _Fn:
    def _read(row: Row) -> bool:
        value = row[index]
        if value is None:
            raise AtomNotAssignedError(
                f"atom {name!r} (index {index}) was never populated by the assignment "
                "builder for this candidate -- refusing to default it to False"
            )
        return value

    return _read


def _intern(name: str, atom_index: Dict[str, int]) -> int:
    index = atom_index.get(name)
    if index is None:
        index = len(atom_index)
        atom_index[name] = index
    return index


def _compile_node(e: "z3.BoolRef", atom_index: Dict[str, int]) -> _Fn:
    """Compile one Z3 `BoolRef` AST node into a Python closure over an assignment `Row`,
    interning any leaf atom encountered into `atom_index`. Recurses into children exactly once
    -- called only from `compile_constraints`'s top-level loop, never from the hot path."""
    if z3.is_true(e):
        return lambda row: True
    if z3.is_false(e):
        return lambda row: False
    if z3.is_not(e):
        (child,) = e.children()
        child_fn = _compile_node(child, atom_index)
        return lambda row: not child_fn(row)
    if z3.is_and(e):
        child_fns = [_compile_node(c, atom_index) for c in e.children()]
        return lambda row: all(fn(row) for fn in child_fns)
    if z3.is_or(e):
        child_fns = [_compile_node(c, atom_index) for c in e.children()]
        return lambda row: any(fn(row) for fn in child_fns)
    if z3.is_implies(e):
        lhs, rhs = e.children()
        lhs_fn = _compile_node(lhs, atom_index)
        rhs_fn = _compile_node(rhs, atom_index)
        return lambda row: (not lhs_fn(row)) or rhs_fn(row)
    if z3.is_eq(e):
        lhs, rhs = e.children()
        lhs_fn = _compile_node(lhs, atom_index)
        rhs_fn = _compile_node(rhs, atom_index)
        return lambda row: lhs_fn(row) == rhs_fn(row)
    if z3.is_app(e) and e.decl().kind() == z3.Z3_OP_PB_AT_MOST:
        child_fns = [_compile_node(c, atom_index) for c in e.children()]
        bound = e.params()[0]
        return lambda row: sum(1 for fn in child_fns if fn(row)) <= bound
    if z3.is_const(e) and z3.is_app(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED and z3.is_bool(e):
        name = e.decl().name()
        index = _intern(name, atom_index)
        return _atom_reader(index, name)
    # A quantifier (QuantifierRef) is not a Z3 "application" node -- `.decl()` raises on it
    # rather than returning something to report, so the diagnostic below is built without
    # assuming `.decl()` is safe to call.
    if z3.is_app(e):
        detail = f"decl={e.decl()!r}, kind={e.decl().kind()!r}"
    else:
        detail = f"non-application node (e.g. a quantifier): {type(e).__name__}"
    raise UnsupportedOperatorError(
        f"unsupported Z3 node outside the closed operator set: {e!r} ({detail}) -- extend the "
        "compiler rather than loosening this check (implementation plan Phase 2 contingency)"
    )


class CompiledConstraints:
    """The result of `compile_constraints`: one compiled closure per top-level constraint, plus
    the interned `atom_index` they were compiled against."""

    def __init__(
        self,
        atom_index: Dict[str, int],
        fns: List[_Fn],
        sources: List["z3.BoolRef"],
    ) -> None:
        self.atom_index = atom_index
        self._fns = fns
        self._sources = sources

    @property
    def size(self) -> int:
        """The number of distinct interned atoms -- the length every assignment `Row` must be."""
        return len(self.atom_index)

    def evaluate_all(self, row: Row) -> bool:
        """`True` iff every compiled top-level constraint evaluates `True` under `row`.
        Short-circuits on the first `False`."""
        for fn in self._fns:
            if not fn(row):
                return False
        return True

    def first_false(self, row: Row) -> Optional[int]:
        """The index of the first compiled constraint that evaluates `False` under `row`, or
        `None` if every constraint holds."""
        for i, fn in enumerate(self._fns):
            if not fn(row):
                return i
        return None

    def describe(self, index: int) -> str:
        """The offending constraint's text -- called only on the failure path, never in the hot
        loop, so it costs nothing there."""
        return str(self._sources[index])


def compile_constraints(constraints: Sequence["z3.BoolRef"]) -> CompiledConstraints:
    """Walk each `BoolRef` in `constraints` exactly once, interning every leaf atom into a
    shared integer index and emitting one compiled closure per top-level constraint."""
    atom_index: Dict[str, int] = {}
    fns: List[_Fn] = []
    sources: List["z3.BoolRef"] = []
    for constraint in constraints:
        fns.append(_compile_node(constraint, atom_index))
        sources.append(constraint)
    return CompiledConstraints(atom_index=atom_index, fns=fns, sources=sources)


# ---------------------------------------------------------------------------
# Candidate-to-assignment builder (Phase 2): the exact inverse of
# `BimodalSemantics.extract_certificate`.
# ---------------------------------------------------------------------------


_AtomResolver = Callable[[WitnessFamily, int], bool]


class PinnedAssignmentBuilder:
    """Bound once per structure: builds the pinned assignment row for a candidate directly from
    its own data (`WitnessFamily`, `target_time`), the exact inverse of
    `BimodalSemantics.extract_certificate` (`core.py:352-412`).

    **Driven by `atom_index`, not by the full lasso x slot x closure product.** The encoder does
    not reference every (lasso, slot, formula) combination -- e.g. a plain `Atom` is never
    referenced at a position directly, only as an `Untl`/`Snce` neighbour or a premise/conclusion
    target -- so a builder that wrote every combination would produce *stray* keys the compiled
    constraints never asked for. Instead, this builder parses each of `atom_index`'s own key
    strings back into a typed resolver exactly once, at construction time (the same
    compile-once, interpret-many split `compile_constraints` uses on the constraint side), so the
    per-candidate hot path (`assign`) does no string parsing at all -- only closure calls over
    already-typed data. This also makes coverage exact by construction: the produced key set is
    always precisely `atom_index`'s key set.

    Holds only plain data read from the structure at construction time (`builder_for` is the
    usual way to build one) -- never a live reference to the structure itself, so it stays valid
    across the whole enumeration even if the structure's own mutable state changes.
    """

    def __init__(
        self,
        atom_index: Mapping[str, int],
        active_lassos: Sequence[int],
        nb: int,
        nm: int,
        nf: int,
        closure: Sequence[Formula],
        target_window: Sequence[int],
    ) -> None:
        self.atom_index = atom_index
        self.size = len(atom_index)
        self.active_lassos = list(active_lassos)
        self.nb = nb
        self.nm = nm
        self.nf = nf
        self.closure = list(closure)
        self.target_window = list(target_window)
        self._lasso_position: Dict[int, int] = {
            lasso_index: j for j, lasso_index in enumerate(self.active_lassos)
        }

        # Collision guard, checked once per structure: two distinct (non-equal) closure formulas
        # sharing an identical repr() would be indistinguishable once encoded into an atom name.
        self._formula_by_repr: Dict[str, Formula] = {}
        for formula in self.closure:
            key = repr(formula)
            existing = self._formula_by_repr.get(key)
            if existing is not None and existing != formula:
                raise AssignmentCollisionError(
                    f"two distinct closure formulas share repr() {key!r}: {existing!r} and "
                    f"{formula!r} -- their lab_/bx_ atom names would be indistinguishable"
                )
            self._formula_by_repr[key] = formula

        # Parse every interned atom name into a typed resolver exactly once (compile-once,
        # interpret-many on the assignment side too).
        self._entries: List[Tuple[str, int, _AtomResolver]] = [
            (name, index, self._parse_atom(name)) for name, index in atom_index.items()
        ]

    def _segment_for_slot(self, slot: int) -> Tuple[str, int]:
        """Map a wrapped slot index to `(segment_attr, offset_within_segment)`, agreeing with
        `WitnessRegistry.wrap`'s own back-then-mid-then-fwd layout."""
        if slot < self.nb:
            return "back", slot
        if slot < self.nb + self.nm:
            return "mid", slot - self.nb
        return "fwd", slot - self.nb - self.nm

    def _lookup_formula(self, formula_repr: str, atom_name: str) -> Formula:
        formula = self._formula_by_repr.get(formula_repr)
        if formula is None:
            raise ValueError(
                f"atom {atom_name!r} names a formula not in this structure's closure: "
                f"{formula_repr!r}"
            )
        return formula

    def _parse_atom(self, name: str) -> _AtomResolver:
        """Parse one interned atom name into a `(family, target_time) -> bool` resolver, per the
        three closed atom families (module docstring). Raises `ValueError` -- loudly, at
        construction time -- on anything outside those three families or an out-of-range lasso
        index, rather than deferring the failure into the hot loop."""
        if name.startswith("bx_"):
            formula = self._lookup_formula(name[len("bx_"):], name)
            return lambda family, target_time: family.bx_of(formula)

        if name.startswith("sel_"):
            t = int(name[len("sel_"):])
            return lambda family, target_time: target_time == t

        if name.startswith("lab_"):
            rest = name[len("lab_"):]
            lasso_str, slot_str, formula_repr = rest.split("_", 2)
            lasso_index = int(lasso_str)
            slot = int(slot_str)
            formula = self._lookup_formula(formula_repr, name)
            j = self._lasso_position.get(lasso_index)
            if j is None:
                raise ValueError(
                    f"atom {name!r} references lasso index {lasso_index}, which is not among "
                    f"this structure's active lassos {self.active_lassos!r}"
                )
            segment_attr, offset = self._segment_for_slot(slot)

            def _resolve(family: WitnessFamily, target_time: int) -> bool:
                lasso = family.lassos[j]
                label = getattr(lasso, segment_attr)[offset]
                return formula in label

            return _resolve

        raise ValueError(
            f"atom name {name!r} is outside the three closed families (lab_/bx_/sel_)"
        )

    def build_names(self, family: WitnessFamily, target_time: int) -> Dict[str, bool]:
        """Build the full `name -> value` dict for one candidate, driven by `atom_index` -- used
        by the unit tests and by `check_coverage`; the hot path uses `assign` instead."""
        if len(family.lassos) != len(self.active_lassos):
            raise ValueError(
                f"family carries {len(family.lassos)} lasso(s) but this structure has "
                f"{len(self.active_lassos)} active lasso(s)"
            )
        return {name: resolver(family, target_time) for name, _, resolver in self._entries}

    def assign(self, family: WitnessFamily, target_time: int) -> List[Optional[bool]]:
        """Project the candidate's data into a preallocated `Row` indexed by `atom_index` -- the
        per-candidate hot path: no dict allocation, no string parsing, only the resolvers
        precomputed at construction time."""
        if len(family.lassos) != len(self.active_lassos):
            raise ValueError(
                f"family carries {len(family.lassos)} lasso(s) but this structure has "
                f"{len(self.active_lassos)} active lasso(s)"
            )
        row: List[Optional[bool]] = [None] * self.size
        for _, index, resolver in self._entries:
            row[index] = resolver(family, target_time)
        return row


def builder_for(structure, atom_index: Mapping[str, int]) -> PinnedAssignmentBuilder:
    """Build a `PinnedAssignmentBuilder` bound to `structure` (a `BimodalStructure`, already
    past `finalize_certificate()` -- true of any structure returned by `_build`/`BuildExample`),
    reading its registry shape and closure directly rather than duplicating them."""
    semantics = structure.semantics
    registry = semantics.witness_registry
    return PinnedAssignmentBuilder(
        atom_index=atom_index,
        active_lassos=semantics._active_lassos,
        nb=registry.nb,
        nm=registry.nm,
        nf=registry.nf,
        closure=sorted(registry.closure, key=repr),
        target_window=list(registry.target_window()),
    )


def full_constraints(structure) -> List["z3.BoolRef"]:
    """The complete Z3 constraint set actually given to the solver for `structure`.

    HISTORY: this helper originally existed because `structure.model_constraints.all_constraints`
    was stale by construction for this theory. `ModelConstraints.__init__` (`models/constraints.py`)
    used to compute `all_constraints` once, via
    `frame_constraints + model_constraints + premise_constraints + conclusion_constraints` -- a
    list `+`, which snapshotted `frame_constraints`'s *contents at that moment*.
    `BimodalSemantics.finalize_certificate()` (local coherence, fulfilment, box faithfulness, and
    the target selector's exactly-one constraint -- the bulk of the real encoding) runs later,
    from `BimodalStructure._setup_solver`'s override, and extends `semantics.frame_constraints`
    *in place*. `ModelConstraints.frame_constraints` is the *same list object* (confirmed: `is`,
    not `==`), so it did pick up those later additions, but the already-concatenated
    `all_constraints` list did not -- it stayed frozen at whatever `frame_constraints` held before
    `finalize_certificate` ran (empty, for every case in this module, since `_build` constructs
    `ModelConstraints` before any `BimodalStructure` exists).

    `all_constraints` is now a computed, read-only property on `ModelConstraints` -- a live view
    of the same four component lists this helper re-concatenates -- so the production attribute
    has caught up: this function is now a named alias for callers in this module, not a
    workaround. Equivalence proven directly (element-for-element `is` identity, not just `==`,
    on a real bimodal solve) before this delegation replaced the manual re-concatenation.
    """
    return list(structure.model_constraints.all_constraints)


def compile_and_bind(structure) -> Tuple[CompiledConstraints, PinnedAssignmentBuilder]:
    """Compile `full_constraints(structure)` once and bind an assignment builder to the same
    structure -- the pairing the Tier 1 hot loop needs, built exactly once before the
    enumeration starts."""
    compiled = compile_constraints(full_constraints(structure))
    builder = builder_for(structure, compiled.atom_index)
    return compiled, builder


def check_coverage(names: Mapping[str, bool], atom_index: Mapping[str, int]) -> None:
    """Assert `names`' key set (from `PinnedAssignmentBuilder.build_names`) is exactly
    `atom_index`'s key set (from `CompiledConstraints.atom_index`) -- neither an unpopulated
    referenced atom nor a stray key. Raises `CoverageError` naming both mismatches; call once
    per structure, not per candidate."""
    produced = set(names.keys())
    expected = set(atom_index.keys())
    missing = expected - produced
    stray = produced - expected
    if missing or stray:
        raise CoverageError(
            f"assignment builder coverage mismatch: missing={sorted(missing)!r} "
            f"stray={sorted(stray)!r}"
        )
