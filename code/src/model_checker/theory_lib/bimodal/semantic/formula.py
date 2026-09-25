"""Lean-mirroring `Formula` ADT, subformula closure, and the certificate wire-format codec.

This module gives ModelChecker's bimodal theory a Python value structurally identical to
BimodalLogic's `FormalSystem.Syntax.Formula`
(`~/Projects/BimodalLogic/FormalSystem/Syntax/Formula.lean:76`), because the witness-family
certificate search is a search over *this* closure, not over ModelChecker's richer sentence AST
-- see `docs/ADEQUACY.md` and the implementation plan's decision D1: "the label domain is
exactly the Lean closure."

## The six constructors

`atom | bot | imp | box | untl | snce` -- nothing else. In particular there is no primitive
`neg`/`and`/`or`/`future`/`past`: those are all encoded via `imp`/`bot`/`untl`/`snce` by
`semantic.formula.translate` (added by a later phase of this plan), exactly mirroring how the
Lean development derives them (`Formula.lean`'s "Naming Convention" section).

`Untl`/`Snce` are **guard-first**, matching the Lean constructor
(`untl : Formula -> Formula -> Formula`, "Argument 1 is the guard, argument 2 is the event",
`Formula.lean:86-95`). This is the opposite order from ModelChecker's own `UntilOperator`/
`SinceOperator`, which are event-first (`operators.py`'s `true_at(self, event_arg, guard_arg,
eval_point)`) -- translation must swap, and that swap belongs to the translation phase, not here.

## Closure

`subformula_closure` mirrors `FormalSystem.Syntax.subformulaClosure`
(`Syntax/SubformulaClosure/Closure.lean`), itself built from the plain recursive
`Formula.subformulas` (`Syntax/Subformulas.lean`): the formula together with the (recursively
closed) subformulas of its immediate children. `closure_of` mirrors the set-level
`FormalSystem.Metalogic.Decidability.closureOf`
(`Metalogic/Decidability/WitnessFamily/Closure.lean`): the union of `subformula_closure` over a
list ("context") of formulas -- the shape a certificate's premises-plus-conclusions closure needs.

## Wire format

`to_json`/`from_json` mirror `Formula.toJson` / `pFormula`
(`~/Projects/BimodalLogic/BimodalTools/DataExport.lean:109-121`,
`~/Projects/BimodalLogic/BimodalTools/JsonParse.lean`), documented as a fixed external contract
in `~/Projects/BimodalLogic/BimodalTools/README.md`'s "Certificate re-verification protocol":
tag vocabulary `atom` (`name`), `bot`, `imp` (`left`, `right`), `box` (`child`), `untl`/`snce`
(`event`, `guard`). `to_json` returns a plain (`dict`/`list`/`str`/`bool`)-only structure, ready
for `json.dumps`.

**Fresh atoms never reach the wire.** `Formula.toJson` emits only `Atom.base`, silently dropping
`Atom.freshIndex` -- the README states this is why a fresh-indexed atom "would silently change
identity" and "is therefore rejected outright rather than decoded." `to_json` raises `ValueError`
on any `Atom` whose `fresh_index` is not `None`, anywhere in the tree, rather than silently
exporting a formula the Lean side would treat as a different one.

## Sentence-to-Formula translation

`translate` converts a ModelChecker `syntactic.Sentence` (after `Sentence.update_types`, i.e.
already primitive -- see `Syntax.initialize_sentences`'s `initialize_types`, which recurses
`DefinedOperator.derived_definition` all the way down) into a `Formula`. It only needs rules for
the 9 primitive operators bimodal declares as `syntactic.Operator` (`\\neg`, `\\wedge`, `\\vee`,
`\\bot`, `\\Box`, `\\Future`, `\\Past`, `\\Until`, `\\Since`); the 8 `DefinedOperator` subclasses
(`\\rightarrow`, `\\leftrightarrow`, `\\top`, `\\Diamond`, `\\future`, `\\past`, `\\next`,
`\\prev`) never reach it, having already been rewritten into primitives.

**The Until/Since guard/event swap.** ModelChecker's `UntilOperator`/`SinceOperator` are
event-first (`true_at(self, event_arg, guard_arg, eval_point)`, `operators.py`), so
`sentence.arguments[0]` is the event and `sentence.arguments[1]` is the guard. `Untl`/`Snce` are
guard-first. `translate` swaps: `Untl(guard=translate(arguments[1]), event=translate(arguments[0]))`.

**`\\Future`/`\\Past`.** These are ModelChecker *primitives* meaning "always in the future/past"
(G/H, not F/P), so they are encoded via the Lean-derived double-negation identity
`G A = ¬F(¬A)` (and its past mirror), using `Untl`/`Snce` with a trivial (`⊤ = Imp(Bot, Bot)`)
guard -- exactly `future φ := ⊤ until φ` / `past φ := ⊤ since φ` composed with negation.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, FrozenSet, Iterable, Optional, Union

__all__ = [
    "Atom",
    "Bot",
    "Imp",
    "Box",
    "Untl",
    "Snce",
    "Formula",
    "subformula_closure",
    "closure_of",
    "to_json",
    "from_json",
    "translate",
]


@dataclass(frozen=True)
class Atom:
    """A propositional atom, mirroring `FormalSystem.Syntax.Atom`
    (`base : String`, `freshIndex : Option Nat`).

    `fresh_index` defaults to `None` (an ordinary, exportable atom). A non-`None` value marks an
    internally generated fresh/Skolem atom; see the module docstring's "Fresh atoms never reach
    the wire" section.
    """

    base: str
    fresh_index: Optional[int] = None


@dataclass(frozen=True)
class Bot:
    """Bottom (falsum), mirroring `Formula.bot`."""


@dataclass(frozen=True)
class Imp:
    """Implication, mirroring `Formula.imp : Formula -> Formula -> Formula`."""

    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Box:
    """Modal necessity, mirroring `Formula.box : Formula -> Formula`."""

    child: "Formula"


@dataclass(frozen=True)
class Untl:
    """Until, mirroring `Formula.untl : Formula -> Formula -> Formula`.

    **Guard-first**: argument 1 is the guard, argument 2 is the event (Formula.lean:86-95).
    """

    guard: "Formula"
    event: "Formula"


@dataclass(frozen=True)
class Snce:
    """Since, mirroring `Formula.snce : Formula -> Formula -> Formula`.

    **Guard-first**: argument 1 is the guard, argument 2 is the event (Formula.lean:97-104).
    """

    guard: "Formula"
    event: "Formula"


Formula = Union[Atom, Bot, Imp, Box, Untl, Snce]


# ---------------------------------------------------------------------------
# Subformula closure
# ---------------------------------------------------------------------------


def subformula_closure(formula: Formula) -> FrozenSet[Formula]:
    """The subformula closure of a single formula, including the formula itself.

    Mirrors `FormalSystem.Syntax.subformulaClosure`, itself the `Finset` conversion of the plain
    recursive `Formula.subformulas` (`Syntax/Subformulas.lean:44-49`):

    - `atom`, `bot`: just the formula itself.
    - `imp l r`: itself plus the closures of `l` and `r`.
    - `box c`: itself plus the closure of `c`.
    - `untl g e` / `snce g e`: itself plus the closures of `g` and `e`.
    """
    if isinstance(formula, (Atom, Bot)):
        return frozenset({formula})
    if isinstance(formula, Imp):
        return frozenset({formula}) | subformula_closure(formula.left) | subformula_closure(
            formula.right
        )
    if isinstance(formula, Box):
        return frozenset({formula}) | subformula_closure(formula.child)
    if isinstance(formula, (Untl, Snce)):
        return frozenset({formula}) | subformula_closure(formula.guard) | subformula_closure(
            formula.event
        )
    raise TypeError(f"not a Formula: {formula!r}")


def closure_of(context: Iterable[Formula]) -> FrozenSet[Formula]:
    """The set-level subformula closure of a context (list of formulas).

    Mirrors `FormalSystem.Metalogic.Decidability.closureOf`: the union of `subformula_closure`
    over every member of `context`. `closure_of([])` is the empty set, matching the Lean
    definition's `foldr (· ∪ ·) ∅` over the empty list.
    """
    result: FrozenSet[Formula] = frozenset()
    for member in context:
        result |= subformula_closure(member)
    return result


# ---------------------------------------------------------------------------
# Wire-format codec
# ---------------------------------------------------------------------------


def _reject_fresh_atoms(formula: Formula) -> None:
    """Raise `ValueError` if `formula` contains an `Atom` with `fresh_index is not None`.

    Called before any `to_json` emission: `Formula.toJson` drops `Atom.freshIndex`, so exporting
    a fresh atom would silently rename it into an ordinary atom of the same base name on the
    Lean side -- a distinct formula, decoded as if it were this one.
    """
    if isinstance(formula, Atom):
        if formula.fresh_index is not None:
            raise ValueError(
                f"cannot export fresh atom {formula.base!r} (fresh_index="
                f"{formula.fresh_index!r}) to the certificate wire format: Formula.toJson drops "
                "Atom.freshIndex, which would silently change this atom's identity on the "
                "Lean side (see BimodalTools/README.md, 'Atom names round-trip on Atom.base "
                "only')"
            )
        return
    if isinstance(formula, Bot):
        return
    if isinstance(formula, Imp):
        _reject_fresh_atoms(formula.left)
        _reject_fresh_atoms(formula.right)
        return
    if isinstance(formula, Box):
        _reject_fresh_atoms(formula.child)
        return
    if isinstance(formula, (Untl, Snce)):
        _reject_fresh_atoms(formula.guard)
        _reject_fresh_atoms(formula.event)
        return
    raise TypeError(f"not a Formula: {formula!r}")


def to_json(formula: Formula) -> Dict[str, object]:
    """Serialize `formula` to the plain-dict wire shape `Formula.toJson` emits.

    Tag vocabulary: `atom` (`name`), `bot`, `imp` (`left`, `right`), `box` (`child`), `untl`/
    `snce` (`event`, `guard` -- note `event` is the *second* Lean constructor argument and
    `guard` the *first*, per `DataExport.lean:119-121`). Raises `ValueError` if `formula`
    contains a fresh-indexed atom anywhere (see `_reject_fresh_atoms`).
    """
    _reject_fresh_atoms(formula)
    return _to_json_unchecked(formula)


def _to_json_unchecked(formula: Formula) -> Dict[str, object]:
    if isinstance(formula, Atom):
        return {"tag": "atom", "name": formula.base}
    if isinstance(formula, Bot):
        return {"tag": "bot"}
    if isinstance(formula, Imp):
        return {
            "tag": "imp",
            "left": _to_json_unchecked(formula.left),
            "right": _to_json_unchecked(formula.right),
        }
    if isinstance(formula, Box):
        return {"tag": "box", "child": _to_json_unchecked(formula.child)}
    if isinstance(formula, Untl):
        return {
            "tag": "untl",
            "event": _to_json_unchecked(formula.event),
            "guard": _to_json_unchecked(formula.guard),
        }
    if isinstance(formula, Snce):
        return {
            "tag": "snce",
            "event": _to_json_unchecked(formula.event),
            "guard": _to_json_unchecked(formula.guard),
        }
    raise TypeError(f"not a Formula: {formula!r}")


def from_json(obj: Dict[str, object]) -> Formula:
    """Parse a wire-shape dict (as produced by `to_json`, or read from JSON text) into a
    `Formula`. Mirrors `pFormula` (`BimodalTools/JsonParse.lean`); an atom always round-trips
    with `fresh_index=None`, since the wire format never carries `freshIndex`.
    """
    if not isinstance(obj, dict) or "tag" not in obj:
        raise ValueError(f"not a formula object: {obj!r}")
    tag = obj["tag"]
    if tag == "atom":
        return Atom(base=obj["name"])  # type: ignore[arg-type]
    if tag == "bot":
        return Bot()
    if tag == "imp":
        return Imp(from_json(obj["left"]), from_json(obj["right"]))  # type: ignore[arg-type]
    if tag == "box":
        return Box(from_json(obj["child"]))  # type: ignore[arg-type]
    if tag == "untl":
        return Untl(
            guard=from_json(obj["guard"]),  # type: ignore[arg-type]
            event=from_json(obj["event"]),  # type: ignore[arg-type]
        )
    if tag == "snce":
        return Snce(
            guard=from_json(obj["guard"]),  # type: ignore[arg-type]
            event=from_json(obj["event"]),  # type: ignore[arg-type]
        )
    raise ValueError(f"unknown formula tag: {tag!r}")


# ---------------------------------------------------------------------------
# Sentence-to-Formula translation
# ---------------------------------------------------------------------------

# Memoizing cache keyed by sentence identity (Sentence has no custom __eq__/__hash__, so the
# default identity-based hash is exactly "keyed by sentence identity"). A plain dict is used
# rather than functools.lru_cache so the cache is directly inspectable in tests.
_TRANSLATE_CACHE: Dict[Any, Formula] = {}


def translate(sentence: Any) -> Formula:
    """Translate a type-updated `syntactic.Sentence` into a `Formula`.

    `sentence` must already have gone through `Sentence.update_types` (as every sentence built
    via `syntactic.Syntax` has): `sentence.operator` is one of the theory's primitive operator
    classes/instances, or `None` for an atomic sentence letter, and `sentence.arguments` is the
    list of child `Sentence`s (or `None`/empty for a 0-ary operator).

    Raises `ValueError` for an operator this translation has no rule for (a `DefinedOperator`
    reaching here would indicate `update_types` was skipped, not that a new rule is needed --
    see the module docstring's Scope Hypothesis note).
    """
    cached = _TRANSLATE_CACHE.get(sentence)
    if cached is not None:
        return cached
    result = _translate_uncached(sentence)
    _TRANSLATE_CACHE[sentence] = result
    return result


def _translate_uncached(sentence: Any) -> Formula:
    sentence_letter = getattr(sentence, "sentence_letter", None)
    if sentence_letter is not None:
        return Atom(str(sentence_letter))

    operator = sentence.operator
    if operator is None:
        raise ValueError(f"sentence {sentence!r} has neither an operator nor a sentence_letter")
    name = operator.name
    arguments = sentence.arguments or ()

    if name == "\\bot":
        return Bot()
    if name == "\\neg":
        (a,) = arguments
        return Imp(translate(a), Bot())
    if name == "\\wedge":
        a, b = arguments
        # A wedge B := not (A -> not B)
        return Imp(Imp(translate(a), Imp(translate(b), Bot())), Bot())
    if name == "\\vee":
        a, b = arguments
        # A vee B := (not A) -> B
        return Imp(Imp(translate(a), Bot()), translate(b))
    if name == "\\Box":
        (a,) = arguments
        return Box(translate(a))
    if name == "\\Future":
        # Future A = G A = not F(not A) = not (top until (not A))
        (a,) = arguments
        top = Imp(Bot(), Bot())
        return Imp(Untl(top, Imp(translate(a), Bot())), Bot())
    if name == "\\Past":
        (a,) = arguments
        top = Imp(Bot(), Bot())
        return Imp(Snce(top, Imp(translate(a), Bot())), Bot())
    if name == "\\Until":
        # ModelChecker is event-first: true_at(self, event_arg, guard_arg, eval_point).
        event_arg, guard_arg = arguments
        return Untl(guard=translate(guard_arg), event=translate(event_arg))
    if name == "\\Since":
        event_arg, guard_arg = arguments
        return Snce(guard=translate(guard_arg), event=translate(event_arg))

    raise ValueError(
        f"translate has no rule for operator {name!r}: expected one of the 9 bimodal "
        "primitives (\\neg, \\wedge, \\vee, \\bot, \\Box, \\Future, \\Past, \\Until, \\Since); "
        "a DefinedOperator reaching translate means Sentence.update_types was not applied"
    )
