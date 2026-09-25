"""Unit tests for the Lean-mirroring `Formula` ADT and subformula closure.

`Formula` mirrors `FormalSystem.Syntax.Formula`
(`~/Projects/BimodalLogic/FormalSystem/Syntax/Formula.lean:76`) exactly: six constructors
(`atom`, `bot`, `imp`, `box`, `untl`, `snce`), with `untl`/`snce` guard-first (argument 1 is the
guard, argument 2 is the event -- see that file's docstring). `closure_of` mirrors
`FormalSystem.Metalogic.Decidability.closureOf`
(`~/Projects/BimodalLogic/FormalSystem/Metalogic/Decidability/WitnessFamily/Closure.lean`), the
union of the single-formula `subformulaClosure` over a context (list) of formulas.

`to_json`/`from_json` mirror the wire tag format `Formula.toJson` emits
(`~/Projects/BimodalLogic/BimodalTools/DataExport.lean:109-121`) and `pFormula` parses
(`~/Projects/BimodalLogic/BimodalTools/JsonParse.lean`), documented in
`~/Projects/BimodalLogic/BimodalTools/README.md`'s "Certificate re-verification protocol".
"""

from __future__ import annotations

import json

import pytest

from model_checker.theory_lib.bimodal.semantic.formula import (
    Atom,
    Bot,
    Box,
    Formula,
    Imp,
    Snce,
    Untl,
    closure_of,
    from_json,
    subformula_closure,
    to_json,
)


class TestConstructorIdentityAndHashing:
    def test_atom_equality_by_base(self):
        assert Atom("p") == Atom("p")
        assert Atom("p") != Atom("q")

    def test_atom_hashable_and_usable_in_sets(self):
        assert len({Atom("p"), Atom("p"), Atom("q")}) == 2

    def test_bot_is_a_singleton_value(self):
        assert Bot() == Bot()
        assert hash(Bot()) == hash(Bot())

    def test_compound_formulas_equal_by_structure(self):
        a = Imp(Atom("p"), Bot())
        b = Imp(Atom("p"), Bot())
        assert a == b
        assert hash(a) == hash(b)

    def test_compound_formulas_distinguish_structure(self):
        assert Imp(Atom("p"), Bot()) != Imp(Bot(), Atom("p"))
        assert Box(Atom("p")) != Atom("p")

    def test_untl_is_guard_first_like_the_lean_constructor(self):
        """`Untl(guard, event)` mirrors `Formula.untl : Formula -> Formula -> Formula`, whose
        first argument is the guard and second is the event (Formula.lean:86-95)."""
        guard, event = Atom("g"), Atom("e")
        f = Untl(guard, event)
        assert f.guard == guard
        assert f.event == event
        # Swapping the arguments produces a different formula -- order is load-bearing.
        assert Untl(guard, event) != Untl(event, guard)

    def test_snce_is_guard_first_like_the_lean_constructor(self):
        guard, event = Atom("g"), Atom("e")
        f = Snce(guard, event)
        assert f.guard == guard
        assert f.event == event
        assert Snce(guard, event) != Snce(event, guard)

    def test_formulas_are_frozen(self):
        f = Atom("p")
        with pytest.raises(Exception):
            f.base = "q"  # type: ignore[misc]


class TestSubformulaClosure:
    def test_atom_closure_is_itself(self):
        assert subformula_closure(Atom("p")) == frozenset({Atom("p")})

    def test_bot_closure_is_itself(self):
        assert subformula_closure(Bot()) == frozenset({Bot()})

    def test_imp_closure_includes_self_and_both_children(self):
        p, q = Atom("p"), Atom("q")
        f = Imp(p, q)
        assert subformula_closure(f) == frozenset({f, p, q})

    def test_box_closure_includes_self_and_child(self):
        p = Atom("p")
        f = Box(p)
        assert subformula_closure(f) == frozenset({f, p})

    def test_untl_closure_includes_self_guard_and_event(self):
        g, e = Atom("g"), Atom("e")
        f = Untl(g, e)
        assert subformula_closure(f) == frozenset({f, g, e})

    def test_snce_closure_includes_self_guard_and_event(self):
        g, e = Atom("g"), Atom("e")
        f = Snce(g, e)
        assert subformula_closure(f) == frozenset({f, g, e})

    def test_nested_closure_hand_computed(self):
        # box(p -> q): { box(p->q), p->q, p, q }
        p, q = Atom("p"), Atom("q")
        imp_pq = Imp(p, q)
        f = Box(imp_pq)
        assert subformula_closure(f) == frozenset({f, imp_pq, p, q})

    def test_deeply_nested_closure_hand_computed(self):
        # (g U e) -> box(e): includes self, (g U e), g, e, box(e)
        g, e = Atom("g"), Atom("e")
        untl = Untl(g, e)
        boxed = Box(e)
        f = Imp(untl, boxed)
        assert subformula_closure(f) == frozenset({f, untl, g, e, boxed})


class TestClosureOf:
    def test_closure_of_empty_context_is_empty(self):
        assert closure_of([]) == frozenset()

    def test_closure_of_single_member_context_equals_its_own_closure(self):
        p = Atom("p")
        assert closure_of([p]) == subformula_closure(p)

    def test_closure_of_two_element_context_is_the_union(self):
        p, q = Atom("p"), Atom("q")
        boxed_p = Box(p)
        imp_pq = Imp(p, q)
        result = closure_of([boxed_p, imp_pq])
        expected = subformula_closure(boxed_p) | subformula_closure(imp_pq)
        assert result == expected
        assert result == frozenset({boxed_p, p, imp_pq, q})

    def test_closure_of_deduplicates_shared_subformulas(self):
        p = Atom("p")
        boxed_p = Box(p)
        # Both members share the atom p; closure_of must not double count (it's a set).
        result = closure_of([boxed_p, p])
        assert result == frozenset({boxed_p, p})


class TestToJsonFromJson:
    """Round-trip and exact tag-shape tests against the Lean wire format."""

    @pytest.mark.parametrize(
        "formula",
        [
            Atom("p"),
            Bot(),
            Imp(Atom("p"), Atom("q")),
            Box(Atom("p")),
            Untl(Atom("g"), Atom("e")),
            Snce(Atom("g"), Atom("e")),
        ],
        ids=["atom", "bot", "imp", "box", "untl", "snce"],
    )
    def test_round_trip(self, formula: Formula):
        assert from_json(to_json(formula)) == formula

    def test_atom_json_shape(self):
        assert to_json(Atom("p")) == {"tag": "atom", "name": "p"}

    def test_bot_json_shape(self):
        assert to_json(Bot()) == {"tag": "bot"}

    def test_imp_json_shape(self):
        assert to_json(Imp(Atom("p"), Atom("q"))) == {
            "tag": "imp",
            "left": {"tag": "atom", "name": "p"},
            "right": {"tag": "atom", "name": "q"},
        }

    def test_box_json_shape(self):
        assert to_json(Box(Atom("p"))) == {
            "tag": "box",
            "child": {"tag": "atom", "name": "p"},
        }

    def test_untl_json_shape_is_event_then_guard_field_named(self):
        """`Formula.toJson` emits `event`/`guard` field names, with `event` bound to the
        constructor's *second* argument and `guard` to the *first* -- see
        `DataExport.lean:119` (`.untl ψ φ => {"event": φ, "guard": ψ}`, where `untl ψ φ` reads
        `ψ` as the guard and `φ` as the event per `untl`'s own guard-first constructor)."""
        guard, event = Atom("g"), Atom("e")
        assert to_json(Untl(guard, event)) == {
            "tag": "untl",
            "event": {"tag": "atom", "name": "e"},
            "guard": {"tag": "atom", "name": "g"},
        }

    def test_snce_json_shape_is_event_then_guard_field_named(self):
        guard, event = Atom("g"), Atom("e")
        assert to_json(Snce(guard, event)) == {
            "tag": "snce",
            "event": {"tag": "atom", "name": "e"},
            "guard": {"tag": "atom", "name": "g"},
        }

    def test_json_serializes_with_stdlib_json(self):
        formula = Imp(Box(Atom("p")), Untl(Atom("g"), Atom("e")))
        # Must be plain-JSON-serializable (dicts/lists/str/bool only).
        text = json.dumps(to_json(formula))
        assert from_json(json.loads(text)) == formula

    def test_from_json_unknown_tag_raises(self):
        with pytest.raises(ValueError):
            from_json({"tag": "nonsense"})

    def test_from_json_ignores_fresh_index_absent_by_construction(self):
        # The wire format never carries freshIndex (Formula.toJson drops it), so from_json
        # only ever sees a base name and always builds a non-fresh Atom.
        formula = from_json({"tag": "atom", "name": "p"})
        assert formula == Atom("p")


class TestFreshAtomGuard:
    """D1's explicit guard: an internally generated fresh/Skolem atom must never reach the wire
    format, since `Formula.toJson` drops `Atom.freshIndex`, which would silently change the
    atom's identity on the Lean side (`BimodalTools/README.md`, "Atom names round-trip on
    `Atom.base` only")."""

    def test_fresh_atom_rejected_by_to_json(self):
        fresh = Atom("p", fresh_index=3)
        with pytest.raises(ValueError, match="fresh"):
            to_json(fresh)

    def test_fresh_atom_rejected_even_when_nested(self):
        fresh = Atom("p", fresh_index=0)
        with pytest.raises(ValueError, match="fresh"):
            to_json(Box(fresh))

    def test_non_fresh_atom_is_unaffected(self):
        # fresh_index=None (the default) is the ordinary, exportable atom.
        assert to_json(Atom("p")) == {"tag": "atom", "name": "p"}
