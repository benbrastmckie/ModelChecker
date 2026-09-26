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

from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal.operators import (
    DefPossibilityOperator,
    NecessityOperator,
    NegationOperator,
    bimodal_operators,
)
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
    translate,
)


def _sentence(infix: str):
    """Build one fully type-updated `Sentence` for `infix`, via the real `Syntax` pipeline and
    the theory's own `bimodal_operators` collection -- exactly the object `translate` receives
    in production (before `update_objects`/`update_proposition`, which only matter for Z3
    evaluation, not for the syntactic operator/arguments structure `translate` reads)."""
    syntax = Syntax([infix], [], bimodal_operators)
    return syntax.premises[0]


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


# ---------------------------------------------------------------------------
# Phase 2: sentence-to-Formula translation
# ---------------------------------------------------------------------------


class TestScopeHypothesisDefinedOperatorsAreExpandedBeforeTranslate:
    """Confirms the plan's Scope Hypothesis: `syntactic.DefinedOperator` instances (e.g.
    `\\Diamond`, the 8 in `operators.py`) are fully expanded into the 9 primitive
    `syntactic.Operator`s by `Syntax`/`Sentence.update_types` before any sentence reaches
    `translate` -- so `translate` only needs rules for the 9 primitives. See
    `Sentence.update_types`'s `derive_type` (recurses via `derived_definition` until
    `primitive_operator` holds) and `Syntax.initialize_sentences`'s `initialize_types` (applies
    this recursively down the whole argument tree, not just the root)."""

    def test_diamond_sentence_reaches_translate_as_negation_of_box_of_negation(self):
        sentence = _sentence("\\Diamond p")
        assert sentence.operator is not DefPossibilityOperator
        assert sentence.operator is NegationOperator
        boxed = sentence.arguments[0]
        assert boxed.operator is NecessityOperator
        inner_neg = boxed.arguments[0]
        assert inner_neg.operator is NegationOperator

    def test_diamond_translates_as_not_box_not(self):
        p = Atom("p")
        expected = Imp(Box(Imp(p, Bot())), Bot())
        assert translate(_sentence("\\Diamond p")) == expected


class TestTranslatePrimitives:
    def test_atom(self):
        assert translate(_sentence("p")) == Atom("p")

    def test_bot(self):
        assert translate(_sentence("\\bot")) == Bot()

    def test_negation(self):
        assert translate(_sentence("\\neg p")) == Imp(Atom("p"), Bot())

    def test_conjunction_is_not_left_arrow_not_right(self):
        p, q = Atom("p"), Atom("q")
        expected = Imp(Imp(p, Imp(q, Bot())), Bot())
        assert translate(_sentence("(p \\wedge q)")) == expected

    def test_disjunction_is_not_left_arrow_right(self):
        p, q = Atom("p"), Atom("q")
        expected = Imp(Imp(p, Bot()), q)
        assert translate(_sentence("(p \\vee q)")) == expected

    def test_box(self):
        assert translate(_sentence("\\Box p")) == Box(Atom("p"))

    def test_future_is_not_eventually_not(self):
        """`\\Future A` (G A, "always in the future") translates to `¬F¬A` in Lean primitives:
        `Imp(Untl(top, Imp(A, Bot)), Bot)`, where `top = Imp(Bot, Bot)` and the untranslated
        `Untl(top, ¬A)` is `future(¬A)` per the Lean `future φ := ⊤ until φ` derived def."""
        p = Atom("p")
        top = Imp(Bot(), Bot())
        expected = Imp(Untl(top, Imp(p, Bot())), Bot())
        assert translate(_sentence("\\Future p")) == expected

    def test_past_is_not_previously_not(self):
        p = Atom("p")
        top = Imp(Bot(), Bot())
        expected = Imp(Snce(top, Imp(p, Bot())), Bot())
        assert translate(_sentence("\\Past p")) == expected


class TestTranslateUntilSinceOrderSensitive:
    """ModelChecker's `UntilOperator`/`SinceOperator` are now guard-first
    (`true_at(self, guard_arg, event_arg, eval_point)`, `operators.py`), matching the Lean
    `Formula.untl`/`Formula.snce` constructors exactly. `translate` is positional identity: no
    swap. This test is deliberately written so that a wrong translation that swapped the
    operands would make it fail -- see the module-level comment below for how to verify that by
    hand."""

    def test_until_is_positional_identity_guard_first(self):
        # Infix "A \\Until B" parses to prefix [\\Until, A, B], and UntilOperator.true_at's
        # positional signature (guard_arg, event_arg, ...) means arguments[0]=A is the guard and
        # arguments[1]=B is the event (see core.py's `operator.true_at(*arguments, eval_point)`).
        guard, event = Atom("p"), Atom("q")
        sentence = _sentence("(p \\Until q)")
        result = translate(sentence)
        assert result == Untl(guard=guard, event=event)
        # The order-sensitive assertion: swapping guard/event must NOT match.
        assert result != Untl(guard=event, event=guard)

    def test_since_is_positional_identity_guard_first(self):
        guard, event = Atom("p"), Atom("q")
        sentence = _sentence("(p \\Since q)")
        result = translate(sentence)
        assert result == Snce(guard=guard, event=event)
        assert result != Snce(guard=event, event=guard)


class TestTranslateMemoization:
    def test_repeated_translation_of_the_same_sentence_object_is_cached(self):
        sentence = _sentence("\\Box p")
        first = translate(sentence)
        second = translate(sentence)
        assert first == second
        # Cached: re-translating the identical sentence object must not rebuild fresh Formula
        # subtrees each time it is looked up (though equal dataclasses would compare equal
        # regardless, this checks the cache is actually consulted).
        from model_checker.theory_lib.bimodal.semantic.formula import _TRANSLATE_CACHE

        assert sentence in _TRANSLATE_CACHE
        assert _TRANSLATE_CACHE[sentence] is first


class TestTranslateNestedFormula:
    def test_box_of_until_of_atoms(self):
        p, q = Atom("p"), Atom("q")
        sentence = _sentence("\\Box (p \\Until q)")
        expected = Box(Untl(guard=p, event=q))
        assert translate(sentence) == expected

    def test_translate_rejects_non_sentence(self):
        with pytest.raises((TypeError, AttributeError)):
            translate(object())


# ---------------------------------------------------------------------------
# Phase 2 amendment: truth-preservation property test
# ---------------------------------------------------------------------------
#
# Phase 5's round-trip against `lake exe check_certificate` compares the Python re-checker and
# the Lean binary on the *same already-translated* Formula, so it structurally cannot test
# whether `translate` itself preserves truth against the sentence it started from. This test
# fills that gap directly, for the propositional-plus-tense fragment, without going through Z3
# or `BimodalSemantics` at all: it hand-implements two *independent* recursive evaluators --
# one over a small ModelChecker-sentence-shaped AST, mirroring the mathematical content of
# `operators.py`'s `true_at` definitions (bounded to a concrete finite time domain, matching
# `core.py.true_at`'s own "atoms are FALSE outside the world's domain" convention) -- and one
# over the translated `Formula`, mirroring the Lean `untl`/`snce` semantics -- then checks they
# agree at every point of several small hand-built valuations.
#
# Known, deliberate limitation (recorded, not silently absorbed): this covers only the five
# non-modal primitives (atom, neg, wedge, vee/bot via encoding, future, past, until, since), not
# Box -- `oracle/bimodal_logic/ground_truth.py`'s brute-force adjudicator has the identical gap,
# for the identical reason: a faithful Box comparison needs an actual multi-world/multi-history
# model, which does not exist independently of whichever semantic core (old window-based, or the
# certificate-based one later phases of this plan install) is under test. Discharging the Box
# case is left to later phases (the pure-Python re-checker's box-faithfulness condition, and the
# `check_certificate` round-trip), not claimed here.

_Ast = tuple


def _ast_to_infix(ast: _Ast) -> str:
    tag = ast[0]
    if tag == "atom":
        return ast[1]
    if tag == "bot":
        return "\\bot"
    if tag == "neg":
        return f"\\neg {_ast_to_infix(ast[1])}"
    if tag == "future":
        return f"\\Future {_ast_to_infix(ast[1])}"
    if tag == "past":
        return f"\\Past {_ast_to_infix(ast[1])}"
    if tag == "wedge":
        return f"({_ast_to_infix(ast[1])} \\wedge {_ast_to_infix(ast[2])})"
    if tag == "vee":
        return f"({_ast_to_infix(ast[1])} \\vee {_ast_to_infix(ast[2])})"
    if tag == "until":
        # ast[1] renders first (guard, post-normalization), ast[2] second (event); the
        # rendered positions are unchanged, but what they mean has flipped along with the
        # rest of the guard-first normalization.
        return f"({_ast_to_infix(ast[1])} \\Until {_ast_to_infix(ast[2])})"
    if tag == "since":
        return f"({_ast_to_infix(ast[1])} \\Since {_ast_to_infix(ast[2])})"
    raise ValueError(f"unknown ast tag: {tag!r}")


def _eval_mc_ast(ast: _Ast, valuation, t: int, domain: range) -> bool:
    """Direct evaluator mirroring `operators.py`'s ModelChecker semantics (guard-first Until/
    Since, `\\Future`/`\\Past` as G/H), restricted to `domain` with atoms false outside it."""
    tag = ast[0]
    if tag == "atom":
        return t in domain and bool(valuation.get(ast[1], {}).get(t, False))
    if tag == "bot":
        return False
    if tag == "neg":
        return not _eval_mc_ast(ast[1], valuation, t, domain)
    if tag == "wedge":
        return _eval_mc_ast(ast[1], valuation, t, domain) and _eval_mc_ast(
            ast[2], valuation, t, domain
        )
    if tag == "vee":
        return _eval_mc_ast(ast[1], valuation, t, domain) or _eval_mc_ast(
            ast[2], valuation, t, domain
        )
    if tag == "future":
        # G A: true at t iff A holds at every domain time strictly after t.
        return all(
            _eval_mc_ast(ast[1], valuation, s, domain) for s in domain if s > t
        )
    if tag == "past":
        return all(
            _eval_mc_ast(ast[1], valuation, s, domain) for s in domain if s < t
        )
    if tag == "until":
        # ast[1] is the guard, ast[2] is the event (guard-first, matching UntilOperator).
        guard, event = ast[1], ast[2]
        for s in domain:
            if s > t and _eval_mc_ast(event, valuation, s, domain):
                if all(
                    _eval_mc_ast(guard, valuation, r, domain)
                    for r in domain
                    if t < r < s
                ):
                    return True
        return False
    if tag == "since":
        guard, event = ast[1], ast[2]
        for s in domain:
            if s < t and _eval_mc_ast(event, valuation, s, domain):
                if all(
                    _eval_mc_ast(guard, valuation, r, domain)
                    for r in domain
                    if s < r < t
                ):
                    return True
        return False
    raise ValueError(f"unknown ast tag: {tag!r}")


def _eval_lean_formula(formula: Formula, valuation, t: int, domain: range) -> bool:
    """Direct evaluator over the translated `Formula`, mirroring the Lean `untl`/`snce`
    semantics (guard-first), independent of `_eval_mc_ast` and of `translate`'s own logic."""
    if isinstance(formula, Atom):
        return t in domain and bool(valuation.get(formula.base, {}).get(t, False))
    if isinstance(formula, Bot):
        return False
    if isinstance(formula, Imp):
        return (not _eval_lean_formula(formula.left, valuation, t, domain)) or _eval_lean_formula(
            formula.right, valuation, t, domain
        )
    if isinstance(formula, Box):
        raise NotImplementedError("Box is out of scope for this tense-fragment property test")
    if isinstance(formula, Untl):
        guard, event = formula.guard, formula.event
        for s in domain:
            if s > t and _eval_lean_formula(event, valuation, s, domain):
                if all(
                    _eval_lean_formula(guard, valuation, r, domain)
                    for r in domain
                    if t < r < s
                ):
                    return True
        return False
    if isinstance(formula, Snce):
        guard, event = formula.guard, formula.event
        for s in domain:
            if s < t and _eval_lean_formula(event, valuation, s, domain):
                if all(
                    _eval_lean_formula(guard, valuation, r, domain)
                    for r in domain
                    if s < r < t
                ):
                    return True
        return False
    raise TypeError(f"not a Formula: {formula!r}")


_PROPERTY_ASTS = [
    ("atom", "p"),
    ("neg", ("atom", "p")),
    ("wedge", ("atom", "p"), ("atom", "q")),
    ("vee", ("atom", "p"), ("atom", "q")),
    ("future", ("atom", "p")),
    ("past", ("atom", "p")),
    ("until", ("atom", "p"), ("atom", "q")),
    ("since", ("atom", "p"), ("atom", "q")),
    ("future", ("past", ("atom", "p"))),
    ("wedge", ("until", ("atom", "p"), ("atom", "q")), ("since", ("atom", "r"), ("atom", "s"))),
    ("neg", ("future", ("neg", ("atom", "p")))),  # not(G(not p)) == F(p)
]

_PROPERTY_DOMAIN = range(-3, 4)


def _valuations(atoms, domain):
    """Deterministically enumerate every Boolean valuation of `atoms` over `domain` (small: at
    most 2 atoms x 7 times x a handful of hand-picked patterns, not the full 2**14 space)."""
    import itertools

    patterns = [
        {t: False for t in domain},
        {t: True for t in domain},
        {t: (t % 2 == 0) for t in domain},
        {t: (t >= 0) for t in domain},
        {t: (t == 0) for t in domain},
    ]
    for combo in itertools.product(patterns, repeat=len(atoms)):
        yield {atom: pattern for atom, pattern in zip(atoms, combo)}


def _atoms_in_ast(ast, out=None):
    if out is None:
        out = set()
    if ast[0] == "atom":
        out.add(ast[1])
    else:
        for child in ast[1:]:
            _atoms_in_ast(child, out)
    return out


class TestTranslateTruthPreservation:
    @pytest.mark.parametrize("ast", _PROPERTY_ASTS)
    def test_translate_preserves_truth_across_hand_built_valuations(self, ast):
        sentence = _sentence(_ast_to_infix(ast))
        formula = translate(sentence)
        atoms = sorted(_atoms_in_ast(ast))
        for valuation in _valuations(atoms, _PROPERTY_DOMAIN):
            for t in _PROPERTY_DOMAIN:
                mc_value = _eval_mc_ast(ast, valuation, t, _PROPERTY_DOMAIN)
                lean_value = _eval_lean_formula(formula, valuation, t, _PROPERTY_DOMAIN)
                assert mc_value == lean_value, (
                    f"translate({_ast_to_infix(ast)}) disagrees with the original sentence's "
                    f"semantics at t={t} under valuation {valuation}: "
                    f"mc={mc_value} lean={lean_value}"
                )
