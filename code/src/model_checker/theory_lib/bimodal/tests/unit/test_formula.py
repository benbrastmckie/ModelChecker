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

import importlib.util
import json
from pathlib import Path

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


def _load_certificate_model():
    """Load `_certificate_model.py` by file path.

    `pyproject.toml` sets `--import-mode=importlib`, under which a plain
    `import _certificate_model` does not resolve (no directory-based `sys.path` insertion for
    a sibling test file) -- see that module's own docstring for why it exists as a relocation
    out of `test_certificate_fixtures.py` rather than a second, independently-maintained copy.
    """
    path = Path(__file__).parent / "_certificate_model.py"
    spec = importlib.util.spec_from_file_location("_certificate_model", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_certificate_model = _load_certificate_model()
_cert_parse_formula = _certificate_model.parse_formula
_CertLasso = _certificate_model.Lasso
_cert_coherent_at = _certificate_model.coherent_at
_cert_box_faithful = _certificate_model.box_faithful


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


class TestExtremalOperatorUpdateTypes:
    """`Sentence.update_types`'s `store_types` extremal-operator branch used to dispatch on
    `self.name in {'\\top', '\\bot'}` -- the *original*, pre-derivation operator name -- rather
    than the shape of `derived_type`. `\\top` is a `DefinedOperator` whose
    `derived_definition` (`TopOperator.derived_definition`, `operators.py`) expands to
    `[NegationOperator, [BotOperator]]`, a **two**-element `derived_type`; the name-keyed branch
    fired anyway (since `self.name == '\\top'` regardless of the derived shape) and truncated
    the expansion to `(first_elem, None, None)`, discarding the negation's `BotOperator`
    argument entirely -- so a `\\top` sentence's `operator` was set but its `arguments` stayed
    `None`, and `translate` (which reads `sentence.arguments`) could never see the argument it
    needs. The fix dispatches on `len(derived_type) == 1` instead, so a two-element derived
    shape (however it originated) falls through to the complex branch it belongs in. `\\bot` is
    a *primitive* `syntactic.Operator` with a genuinely one-element `derived_type`, so the
    shape-keyed branch is behavior-identical for it -- covered by the companion assertion
    below."""

    def test_bare_top_type_updates_with_operator_and_arguments_set(self):
        sentence = _sentence("\\top")
        assert sentence.operator is NegationOperator
        assert sentence.arguments is not None
        assert len(sentence.arguments) == 1

    def test_bare_top_translates_to_the_negated_bot_shape(self):
        expected = Imp(Bot(), Bot())
        top_formula = translate(_sentence("\\top"))
        assert top_formula == expected
        assert to_json(top_formula) == {
            "tag": "imp",
            "left": {"tag": "bot"},
            "right": {"tag": "bot"},
        }

    def test_bare_bot_is_unchanged_by_the_shape_keyed_fix(self):
        sentence = _sentence("\\bot")
        assert sentence.arguments is None
        bot_formula = translate(sentence)
        assert bot_formula == Bot()
        assert to_json(bot_formula) == {"tag": "bot"}

    def test_nested_top_under_box_type_updates_and_translates(self):
        """`\\Box \\top` -- a nested bare `\\top`, not only the bare-formula case above."""
        sentence = _sentence("\\Box \\top")
        boxed = sentence.arguments[0]
        assert boxed.operator is NegationOperator
        assert boxed.arguments is not None
        expected = Box(Imp(Bot(), Bot()))
        top_formula = translate(sentence)
        assert top_formula == expected
        assert to_json(top_formula) == {
            "tag": "box",
            "child": {"tag": "imp", "left": {"tag": "bot"}, "right": {"tag": "bot"}},
        }

    def test_nested_top_inside_conjunction_type_updates_and_translates(self):
        """`(\\top \\wedge p)` -- `\\top` nested as a conjunction operand, not the root."""
        p = Atom("p")
        sentence = _sentence("(\\top \\wedge p)")
        top_arg = sentence.arguments[0]
        assert top_arg.operator is NegationOperator
        assert top_arg.arguments is not None
        top = Imp(Bot(), Bot())
        expected = Imp(Imp(top, Imp(p, Bot())), Bot())
        assert translate(sentence) == expected


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
# The Box case is covered directly by `TestTranslateTruthPreservationBox` below (a sibling test
# class), over hand-built multi-lasso label families -- it cannot be inherited from
# `oracle/bimodal_logic/ground_truth.py`'s brute-force adjudicator, which covers only the five
# primitive tense tags and has no Box case of its own, for the same underlying reason a faithful
# Box comparison needs an actual multi-world/multi-history model. `\Box` is family-global: it
# quantifies over every position of every lasso in the family, per `NecessityOperator`'s own
# docstring and (C3) box faithfulness -- not a per-point quantifier the way `\Future`/`\Past`/
# `\Until`/`\Since` are.

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
    if tag == "box":
        return f"\\Box {_ast_to_infix(ast[1])}"
    # Defined operators (Phase 6, Axis 2): rendered via their own surface syntax so `_sentence`
    # exercises the real Syntax/derived_definition expansion path; `_eval_mc_ast` below
    # evaluates each independently of that expansion (elimination-coverage, not delegation).
    if tag == "imp":
        return f"({_ast_to_infix(ast[1])} \\rightarrow {_ast_to_infix(ast[2])})"
    if tag == "diamond":
        return f"\\Diamond {_ast_to_infix(ast[1])}"
    if tag == "top":
        return "\\top"
    if tag == "def_future":
        return f"\\future {_ast_to_infix(ast[1])}"
    if tag == "def_past":
        return f"\\past {_ast_to_infix(ast[1])}"
    if tag == "next":
        return f"\\next {_ast_to_infix(ast[1])}"
    if tag == "prev":
        return f"\\prev {_ast_to_infix(ast[1])}"
    raise ValueError(f"unknown ast tag: {tag!r}")


def _eval_mc_ast(ast: _Ast, family, i: int, t: int, domain: range) -> bool:
    """Direct evaluator mirroring `operators.py`'s ModelChecker semantics (guard-first Until/
    Since, `\\Future`/`\\Past` as G/H, family-global `\\Box`), restricted to `domain` with atoms
    false outside it. `family` is a tuple of `_certificate_model.Lasso`; `i` selects the lasso
    this AST is evaluated against for every clause except `box`, which quantifies over every
    lasso of `family`."""
    tag = ast[0]
    if tag == "atom":
        return t in domain and (("atom", ast[1]) in family[i].lab(t))
    if tag == "bot":
        return False
    if tag == "neg":
        return not _eval_mc_ast(ast[1], family, i, t, domain)
    if tag == "wedge":
        return _eval_mc_ast(ast[1], family, i, t, domain) and _eval_mc_ast(
            ast[2], family, i, t, domain
        )
    if tag == "vee":
        return _eval_mc_ast(ast[1], family, i, t, domain) or _eval_mc_ast(
            ast[2], family, i, t, domain
        )
    if tag == "future":
        # G A: true at t iff A holds at every domain time strictly after t, within lasso i.
        return all(
            _eval_mc_ast(ast[1], family, i, s, domain) for s in domain if s > t
        )
    if tag == "past":
        return all(
            _eval_mc_ast(ast[1], family, i, s, domain) for s in domain if s < t
        )
    if tag == "until":
        # ast[1] is the guard, ast[2] is the event (guard-first, matching UntilOperator).
        guard, event = ast[1], ast[2]
        for s in domain:
            if s > t and _eval_mc_ast(event, family, i, s, domain):
                if all(
                    _eval_mc_ast(guard, family, i, r, domain)
                    for r in domain
                    if t < r < s
                ):
                    return True
        return False
    if tag == "since":
        guard, event = ast[1], ast[2]
        for s in domain:
            if s < t and _eval_mc_ast(event, family, i, s, domain):
                if all(
                    _eval_mc_ast(guard, family, i, r, domain)
                    for r in domain
                    if s < r < t
                ):
                    return True
        return False
    if tag == "box":
        # Family-global: true at (i, t) iff the child holds at EVERY position of EVERY lasso
        # in the family (NecessityOperator's own docstring; (C3) box faithfulness), not merely
        # every position of lasso i.
        return all(
            _eval_mc_ast(ast[1], family, j, u, domain)
            for j in range(len(family))
            for u in domain
        )
    # Defined operators (Phase 6, Axis 2): each evaluated by its own independent mathematical
    # meaning -- NOT by delegating to `DefinedOperator.derived_definition` or `translate` -- so
    # that testing `translate(sentence)` against this AST's own tag genuinely checks the real
    # elimination path, rather than assuming it.
    if tag == "imp":
        # Material conditional: A -> B.
        return (not _eval_mc_ast(ast[1], family, i, t, domain)) or _eval_mc_ast(
            ast[2], family, i, t, domain
        )
    if tag == "diamond":
        # Possibility: family-global existential dual of Box.
        return any(
            _eval_mc_ast(ast[1], family, j, u, domain)
            for j in range(len(family))
            for u in domain
        )
    if tag == "top":
        return True
    if tag == "def_future":
        # \future A (F, "eventually"): true at t iff A holds at SOME domain time strictly
        # after t (dual of the primitive \Future's "always").
        return any(
            _eval_mc_ast(ast[1], family, i, s, domain) for s in domain if s > t
        )
    if tag == "def_past":
        return any(
            _eval_mc_ast(ast[1], family, i, s, domain) for s in domain if s < t
        )
    if tag == "next":
        # \next A: true at t iff A holds at the immediately following position t+1.
        return (t + 1) in domain and _eval_mc_ast(ast[1], family, i, t + 1, domain)
    if tag == "prev":
        return (t - 1) in domain and _eval_mc_ast(ast[1], family, i, t - 1, domain)
    raise ValueError(f"unknown ast tag: {tag!r}")


def _eval_lean_formula(formula: Formula, family, i: int, t: int, domain: range) -> bool:
    """Direct evaluator over the translated `Formula`, mirroring the Lean `untl`/`snce`/`box`
    semantics (guard-first Until/Since, family-global Box), independent of `_eval_mc_ast` and of
    `translate`'s own logic. Never calls `translate`, and shares no helper with `_eval_mc_ast`
    beyond the `family`/`domain` data it both read -- a reference evaluator routed through
    `translate` would pass under the very bug this differential targets."""
    if isinstance(formula, Atom):
        return t in domain and (("atom", formula.base) in family[i].lab(t))
    if isinstance(formula, Bot):
        return False
    if isinstance(formula, Imp):
        return (
            not _eval_lean_formula(formula.left, family, i, t, domain)
        ) or _eval_lean_formula(formula.right, family, i, t, domain)
    if isinstance(formula, Box):
        return all(
            _eval_lean_formula(formula.child, family, j, u, domain)
            for j in range(len(family))
            for u in domain
        )
    if isinstance(formula, Untl):
        guard, event = formula.guard, formula.event
        for s in domain:
            if s > t and _eval_lean_formula(event, family, i, s, domain):
                if all(
                    _eval_lean_formula(guard, family, i, r, domain)
                    for r in domain
                    if t < r < s
                ):
                    return True
        return False
    if isinstance(formula, Snce):
        guard, event = formula.guard, formula.event
        for s in domain:
            if s < t and _eval_lean_formula(event, family, i, s, domain):
                if all(
                    _eval_lean_formula(guard, family, i, r, domain)
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


def _family_from_valuation(valuation, domain):
    """Wrap a `{atom: {t: bool}}` valuation (over `domain`) in a one-lasso family, so the
    existing tense-fragment regression test can reuse the family-aware evaluators unchanged.
    Assumes `domain` is a contiguous range with at least one negative position (as
    `_PROPERTY_DOMAIN` is): `back` covers the negative positions in one exact cycle (no
    wraparound within `domain`), `mid` covers the non-negative positions directly, and `fwd` is
    a single unread filler segment -- every clause above bounds its quantification to `domain`
    explicitly, so `Lasso.lab` is never consulted past it."""
    atoms = sorted(valuation.keys())

    def _label(t):
        return [{"tag": "atom", "name": a} for a in atoms if valuation[a].get(t, False)]

    neg_positions = sorted(t for t in domain if t < 0)
    nonneg_positions = sorted(t for t in domain if t >= 0)
    back = [_label(t) for t in neg_positions]
    mid = [_label(t) for t in nonneg_positions]
    fwd = [[]]
    return (_CertLasso(back=back, mid=mid, fwd=fwd),)


class TestTranslateTruthPreservation:
    @pytest.mark.parametrize("ast", _PROPERTY_ASTS)
    def test_translate_preserves_truth_across_hand_built_valuations(self, ast):
        sentence = _sentence(_ast_to_infix(ast))
        formula = translate(sentence)
        atoms = sorted(_atoms_in_ast(ast))
        for valuation in _valuations(atoms, _PROPERTY_DOMAIN):
            family = _family_from_valuation(valuation, _PROPERTY_DOMAIN)
            for t in _PROPERTY_DOMAIN:
                mc_value = _eval_mc_ast(ast, family, 0, t, _PROPERTY_DOMAIN)
                lean_value = _eval_lean_formula(formula, family, 0, t, _PROPERTY_DOMAIN)
                assert mc_value == lean_value, (
                    f"translate({_ast_to_infix(ast)}) disagrees with the original sentence's "
                    f"semantics at t={t} under valuation {valuation}: "
                    f"mc={mc_value} lean={lean_value}"
                )


# ---------------------------------------------------------------------------
# Phase 6: two axes -- generated sentences and hand-built multi-lasso families
# ---------------------------------------------------------------------------
#
# Axis 1 (below): hand-built multi-lasso label families, built the way
# `01_positive_box.json`/`03_box_unfaithful.json` were built -- explicit `Certificate` objects
# constructed from the same wire-format shape those fixtures use (labels carrying both an atom
# and, where the `bx` guess says True, the box formula itself, so (C1) local coherence holds).
# Each family covers a wide-enough periodic window (`nb = nm = nf = 4`, `box_window =
# range(-4, 8)`) that `_PROPERTY_DOMAIN = range(-3, 4)` is a proper subset with every position
# explicitly defined (no cyclical wraparound within the window).

_ATOM_P = {"tag": "atom", "name": "p"}
_ATOM_Q = {"tag": "atom", "name": "q"}
_BOX_P = {"tag": "box", "child": _ATOM_P}
_BOX_Q = {"tag": "box", "child": _ATOM_Q}


def _lasso_raw(nb: int, nm: int, nf: int, label_fn):
    """Build a raw `{back, mid, fwd}` lasso dict via `label_fn(t) -> [formula-tag dict, ...]`,
    covering exactly `range(-nb, nm + nf)` with each position explicitly defined once (no
    cyclical repeats inside that span)."""
    positions = list(range(-nb, nm + nf))
    return {
        "back": [label_fn(t) for t in positions[:nb]],
        "mid": [label_fn(t) for t in positions[nb : nb + nm]],
        "fwd": [label_fn(t) for t in positions[nb + nm :]],
    }


def _certificate_from_lassos(lassos_raw, bx, closure_conclusions=()):
    """Build a `_certificate_model.Certificate`. `closure_conclusions` is not a real decision
    target (these families are evaluated directly, not decided) -- it exists only to pull a
    box formula into `cert.closure` when the `bx` guess is False, since a False guess means no
    label carries the box formula itself, and `box_faithful`/`coherent_at` only examine formulas
    already present in the closure. `01_positive_box.json` pulls its box formula in via
    `premises` (guess True, box formula already in every label too); `03_box_unfaithful.json`
    pulls it in via `conclusions` (guess False, box formula absent from labels) -- this mirrors
    the latter."""
    raw = {
        "target": {"premises": [], "conclusions": list(closure_conclusions), "time": 0},
        "bx": bx,
        "lassos": lassos_raw,
    }
    return _certificate_model.Certificate(raw)


def _label_p_everywhere_with_box(t: int):
    return [_ATOM_P, _BOX_P]


def _label_p_only(t: int):
    return [_ATOM_P]


def _label_p_only_except(exceptions):
    def _label(t: int):
        return [] if t in exceptions else [_ATOM_P]
    return _label


def _label3_lasso0(t: int):
    return [_ATOM_P, _ATOM_Q, _BOX_P]


def _label3_lasso1_q_missing_at(exceptions):
    def _label(t: int):
        return [_ATOM_P, _BOX_P] if t in exceptions else [_ATOM_P, _ATOM_Q, _BOX_P]
    return _label


# Family A ("positive_box"): 2 lassos, p (and its box guess) hold at literally every position
# -- \Box p is true, family-wide, mirroring 01_positive_box.json's own shape but genuinely
# multi-lasso.
_FAMILY_BOX_TRUE = _certificate_from_lassos(
    [
        _lasso_raw(4, 4, 4, _label_p_everywhere_with_box),
        _lasso_raw(4, 4, 4, _label_p_everywhere_with_box),
    ],
    [[_ATOM_P, True]],
)

# Family B ("box false, single-lasso can't catch it"): lasso 0 has p everywhere (would make
# \Box p look true if only lasso 0 existed); lasso 1 has a single p-violation at t=0 (within
# _PROPERTY_DOMAIN), which is what actually makes \Box p false for the whole family. The bx
# guess (False) is the faithful one -- box_faithful holds -- and no label carries the box
# formula (since the guess is False, (C1) requires the box formula itself absent from every
# label, matching 03_box_unfaithful.json's *label* shape, though this family's guess IS correct).
_FAMILY_BOX_FALSE_VIA_SECOND_LASSO = _certificate_from_lassos(
    [
        _lasso_raw(4, 4, 4, _label_p_only),
        _lasso_raw(4, 4, 4, _label_p_only_except({0})),
    ],
    [[_ATOM_P, False]],
    closure_conclusions=[_BOX_P],
)

# Family C ("mixed atoms"): p holds everywhere in both lassos (\Box p true); q holds everywhere
# except a single position in lasso 1 (\Box q false) -- \Box p and \Box q genuinely differ
# within the same family.
_FAMILY_MIXED_BOX_P_TRUE_BOX_Q_FALSE = _certificate_from_lassos(
    [
        _lasso_raw(4, 4, 4, _label3_lasso0),
        _lasso_raw(4, 4, 4, _label3_lasso1_q_missing_at({0})),
    ],
    [[_ATOM_P, True], [_ATOM_Q, False]],
    closure_conclusions=[_BOX_Q],
)

_PROPERTY_FAMILIES = [
    _FAMILY_BOX_TRUE.lassos,
    _FAMILY_BOX_FALSE_VIA_SECOND_LASSO.lassos,
    _FAMILY_MIXED_BOX_P_TRUE_BOX_Q_FALSE.lassos,
]

_PROPERTY_CERTIFICATES = [
    _FAMILY_BOX_TRUE,
    _FAMILY_BOX_FALSE_VIA_SECOND_LASSO,
    _FAMILY_MIXED_BOX_P_TRUE_BOX_Q_FALSE,
]


class TestPropertyFamiliesAreCoherent:
    """Coherence as a precondition, not an outcome: an incoherent family would make the
    differential vacuous (any disagreement could be blamed on the family, not on `translate`).
    `03_box_unfaithful.json` is the reference for what an incoherent family looks like (its own
    fixture test already covers it as a *rejected* certificate); this class asserts the
    positive precondition on the hand-built families above, using the identical imported
    `coherent_at`/`box_faithful` checkers."""

    @pytest.mark.parametrize(
        "cert", _PROPERTY_CERTIFICATES, ids=["box_true", "box_false_second_lasso", "mixed"]
    )
    def test_family_is_locally_coherent(self, cert):
        for lasso in cert.lassos:
            ok, failing = _cert_coherent_at(cert, lasso, 0)
            # Spot-check a handful of positions across the certificate's own coherence window
            # rather than only t=0, since (C1) is a per-position condition.
            for t in lasso.coherence_window():
                ok, failing = _cert_coherent_at(cert, lasso, t)
                assert ok, f"expected local coherence at t={t}, failing formula={failing}"

    @pytest.mark.parametrize(
        "cert", _PROPERTY_CERTIFICATES, ids=["box_true", "box_false_second_lasso", "mixed"]
    )
    def test_family_is_box_faithful(self, cert):
        ok, failing = _cert_box_faithful(cert)
        assert ok, f"expected box faithfulness, failing formula={failing}"

    def test_rejects_the_known_incoherent_shape(self):
        """Negative case: `03_box_unfaithful.json`'s own shape (bx says False, but the atom
        holds at every position) is NOT box-faithful -- confirms the precondition test would
        actually catch an incoherent family, not merely pass vacuously."""
        bad_cert = _certificate_from_lassos(
            [_lasso_raw(4, 4, 4, _label_p_only)],  # p holds everywhere, no box formula in label
            [[_ATOM_P, False]],  # ... but the guess says False: unfaithful
            closure_conclusions=[_BOX_P],
        )
        ok, failing = _cert_box_faithful(bad_cert)
        assert not ok, "expected box_faithful to reject the known-unfaithful shape"
        assert failing == ("box", ("atom", "p"))


# ---------------------------------------------------------------------------
# Axis 2: generated sentences covering every defined operator, plus mandatory asymmetric
# Until/Since instances.
# ---------------------------------------------------------------------------

_GENERATED_CORPUS_SEED = 196
_GENERATED_CORPUS_MAX_DEPTH = 3
_GENERATED_CORPUS_SAMPLE_COUNT = 24

# Every operator this task's obligation names as required elimination coverage (Testing &
# Validation checklist): '\neg', '\wedge', '\vee', '\rightarrow', '\Diamond', '\top', '\future',
# '\past', '\next', '\prev'.
_REQUIRED_OPERATOR_SURFACE_NAMES = {
    "neg": "\\neg",
    "wedge": "\\wedge",
    "vee": "\\vee",
    "imp": "\\rightarrow",
    "diamond": "\\Diamond",
    "top": "\\top",
    "def_future": "\\future",
    "def_past": "\\past",
    "next": "\\next",
    "prev": "\\prev",
}


def _tags_in_ast(ast, out=None):
    if out is None:
        out = set()
    out.add(ast[0])
    for child in ast[1:]:
        if isinstance(child, tuple):
            _tags_in_ast(child, out)
    return out


def _generate_corpus(seed: int, max_depth: int, sample_count: int):
    """Deterministic (seeded), bounded-depth generator over atoms {p, q}. Forces at least one
    instance of every tag `_REQUIRED_OPERATOR_SURFACE_NAMES` names (coverage by construction,
    still checked below rather than assumed) and mixes in randomly-generated deeper nestings so
    elimination coverage is broad rather than only what someone thought to write down."""
    import random

    rng = random.Random(seed)
    leaves = [("atom", "p"), ("atom", "q"), ("bot",)]
    unary_tags = ["neg", "box", "future", "past", "def_future", "def_past", "next", "prev", "diamond"]
    binary_tags = ["wedge", "vee", "until", "since", "imp"]

    def gen(depth):
        if depth <= 0 or rng.random() < 0.35:
            return rng.choice(leaves)
        if rng.random() < 0.4:
            tag = rng.choice(unary_tags)
            return (tag, gen(depth - 1))
        tag = rng.choice(binary_tags)
        return (tag, gen(depth - 1), gen(depth - 1))

    corpus = [("top",)]
    for tag in unary_tags:
        corpus.append((tag, rng.choice(leaves)))
    for tag in binary_tags:
        corpus.append((tag, rng.choice(leaves), rng.choice(leaves)))
    # Asymmetric Until/Since: guard and event genuinely distinguishable (p vs q, both atoms
    # that actually differ across _PROPERTY_FAMILIES -- see the sensitivity assertions below).
    corpus.append(("until", ("atom", "p"), ("atom", "q")))
    corpus.append(("until", ("atom", "q"), ("atom", "p")))
    corpus.append(("since", ("atom", "p"), ("atom", "q")))
    corpus.append(("since", ("atom", "q"), ("atom", "p")))
    for _ in range(sample_count):
        corpus.append(gen(max_depth))
    return corpus


_GENERATED_CORPUS = _generate_corpus(
    _GENERATED_CORPUS_SEED, _GENERATED_CORPUS_MAX_DEPTH, _GENERATED_CORPUS_SAMPLE_COUNT
)

# Hand-written nestings a bounded generator may not reliably reach: Box combined with every
# other connective, including nested inside Until/Since and vice versa. Operand order shown
# guard-first.
_BOX_PROPERTY_ASTS = [
    ("box", ("atom", "p")),
    ("box", ("wedge", ("atom", "p"), ("atom", "q"))),
    ("neg", ("box", ("atom", "p"))),
    ("vee", ("box", ("atom", "p")), ("atom", "q")),
    ("until", ("atom", "q"), ("box", ("atom", "p"))),
    ("since", ("atom", "q"), ("box", ("atom", "p"))),
    ("box", ("until", ("atom", "q"), ("atom", "p"))),
    ("box", ("def_future", ("atom", "p"))),
    ("def_future", ("box", ("atom", "p"))),
]

# `\top` is excluded from the differential exercise below (though it stays in
# `_GENERATED_CORPUS` for the coverage assertion): a bare/nested `\top` sentence hits a
# pre-existing, already-documented TopOperator bug in `Sentence.update_types`'s extremal-operator
# branch (see `examples.py`'s own "explicit expansion to avoid TopOperator bug" comment, which
# routes around it the same way everywhere else in this theory) -- out of scope for this
# translation-bridge obligation to fix as a drive-by.
_BOX_TEST_CORPUS = [ast for ast in _GENERATED_CORPUS if ast[0] != "top"] + _BOX_PROPERTY_ASTS


class TestDefinedOperatorCoverage:
    """Coverage is checked, not assumed: every operator the obligation names must appear in at
    least one generated sentence."""

    def test_every_required_operator_appears_in_the_generated_corpus(self):
        seen_tags: set = set()
        for ast in _GENERATED_CORPUS:
            seen_tags |= _tags_in_ast(ast)
        missing = {
            surface
            for tag, surface in _REQUIRED_OPERATOR_SURFACE_NAMES.items()
            if tag not in seen_tags
        }
        assert not missing, f"generated corpus is missing coverage for: {sorted(missing)}"


class TestAsymmetryIsGenuine:
    """Operator coverage is not hazard sensitivity (user decision, cycle 2, design property
    (3)): this asserts the generated asymmetric Until/Since instances actually disagree with
    their operand-swapped form at some point of some family -- the property the differential
    test needs in order to be capable of catching a guard/event mixup at all."""

    def test_at_least_one_generated_until_instance_is_order_sensitive(self):
        until_asts = [ast for ast in _GENERATED_CORPUS if ast[0] == "until"]
        assert until_asts, "expected at least one generated \\Until instance"
        sensitive = False
        for ast in until_asts:
            swapped = ("until", ast[2], ast[1])
            for family in _PROPERTY_FAMILIES:
                for i in range(len(family)):
                    for t in _PROPERTY_DOMAIN:
                        if _eval_mc_ast(ast, family, i, t, _PROPERTY_DOMAIN) != _eval_mc_ast(
                            swapped, family, i, t, _PROPERTY_DOMAIN
                        ):
                            sensitive = True
        assert sensitive, "no generated \\Until instance is order-sensitive at any family point"

    def test_at_least_one_generated_since_instance_is_order_sensitive(self):
        since_asts = [ast for ast in _GENERATED_CORPUS if ast[0] == "since"]
        assert since_asts, "expected at least one generated \\Since instance"
        sensitive = False
        for ast in since_asts:
            swapped = ("since", ast[2], ast[1])
            for family in _PROPERTY_FAMILIES:
                for i in range(len(family)):
                    for t in _PROPERTY_DOMAIN:
                        if _eval_mc_ast(ast, family, i, t, _PROPERTY_DOMAIN) != _eval_mc_ast(
                            swapped, family, i, t, _PROPERTY_DOMAIN
                        ):
                            sensitive = True
        assert sensitive, "no generated \\Since instance is order-sensitive at any family point"


class TestTranslateTruthPreservationBox:
    """Discharges S4's box half: differentially checks `translate` against the independent
    `_eval_mc_ast`/`_eval_lean_formula` evaluators over the generated corpus (Axis 2) plus the
    hand-written box nestings, crossed with the hand-built multi-lasso families (Axis 1), at
    every point of every lasso of every family."""

    @pytest.mark.parametrize("ast", _BOX_TEST_CORPUS)
    def test_translate_preserves_truth_across_hand_built_families(self, ast):
        sentence = _sentence(_ast_to_infix(ast))
        formula = translate(sentence)
        for family in _PROPERTY_FAMILIES:
            for i in range(len(family)):
                for t in _PROPERTY_DOMAIN:
                    mc_value = _eval_mc_ast(ast, family, i, t, _PROPERTY_DOMAIN)
                    lean_value = _eval_lean_formula(formula, family, i, t, _PROPERTY_DOMAIN)
                    assert mc_value == lean_value, (
                        f"translate({_ast_to_infix(ast)}) disagrees with the original "
                        f"sentence's semantics at lasso={i}, t={t}: "
                        f"mc={mc_value} lean={lean_value}"
                    )


# ---------------------------------------------------------------------------
# Phase 7: negative controls -- prove the new coverage has teeth
# ---------------------------------------------------------------------------


class TestNegativeControlsHaveTeeth:
    """Recorded, executable evidence that the box coverage and the asymmetry coverage would
    actually fail on a wrong translation -- closing the vacuity risk that a differential test
    which never disagrees might simply never be exercising the thing it claims to test."""

    def test_family_corpus_is_non_vacuous_for_box(self):
        """`\\Box p` is true for at least one family and false for at least one other -- the
        family corpus is not constant, so a differential over it can actually discriminate."""
        box_p = ("box", ("atom", "p"))
        values = {
            _eval_mc_ast(box_p, family, 0, 0, _PROPERTY_DOMAIN) for family in _PROPERTY_FAMILIES
        }
        assert values == {True, False}, (
            f"expected \\Box p to be both true and false across the family corpus, got {values}"
        )

    def test_box_mutation_is_detected(self):
        """A deliberately wrong translation of `\\Box p` -- dropping the Box wrapper entirely,
        i.e. translating it as if it were bare `p` -- must disagree with the correct
        translation at some family point. The mutation is constructed by hand; `translate`
        itself is never monkeypatched."""
        sentence = _sentence("\\Box p")
        correct = translate(sentence)
        assert isinstance(correct, Box)
        wrong = correct.child  # the Box-dropping mutation: Box(p) mistranslated as p

        disagreement = False
        for family in _PROPERTY_FAMILIES:
            for i in range(len(family)):
                for t in _PROPERTY_DOMAIN:
                    if _eval_lean_formula(
                        correct, family, i, t, _PROPERTY_DOMAIN
                    ) != _eval_lean_formula(wrong, family, i, t, _PROPERTY_DOMAIN):
                        disagreement = True
        assert disagreement, "dropping the Box wrapper was not detected at any family point"

    def test_family_crossing_control_a_single_lasso_box_would_miss_the_second_lasso(self):
        """The multi-lasso structure is load-bearing, not decorative: a box translation that
        (wrongly) quantified over only its own lasso, rather than every lasso in the family,
        would agree with the correct family-global semantics on a single-lasso family but
        disagree on Family B (whose violation lives entirely in lasso 1). This is exactly the
        defect a single-lasso family corpus could not have caught."""

        def _single_lasso_box(child_ast, family, i, t, domain):
            return all(_eval_mc_ast(child_ast, family, i, u, domain) for u in domain)

        p = ("atom", "p")
        family_b = _PROPERTY_FAMILIES[1]  # box_false_via_second_lasso
        correct = _eval_mc_ast(("box", p), family_b, 0, 0, _PROPERTY_DOMAIN)
        wrong_single_lasso = _single_lasso_box(p, family_b, 0, 0, _PROPERTY_DOMAIN)
        assert correct is False, "expected the family-global \\Box p to be false (lasso 1 fails)"
        assert wrong_single_lasso is True, (
            "expected the single-lasso mutation to (wrongly) see only lasso 0, where p holds "
            "everywhere"
        )
        assert correct != wrong_single_lasso, (
            "the single-lasso mutation was not caught -- the multi-lasso family failed to be "
            "load-bearing"
        )

    def test_asymmetry_sensitivity_control_until(self):
        """For a generated asymmetric `\\Until` instance, the operand-swapped `Formula` (built
        by hand, not via `translate`) must disagree with the translated original at some family
        point -- the control proving the asymmetric corpus actually has hazard sensitivity."""
        sentence = _sentence("(p \\Until q)")
        correct = translate(sentence)
        assert isinstance(correct, Untl)
        swapped = Untl(guard=correct.event, event=correct.guard)

        disagreement = False
        for family in _PROPERTY_FAMILIES:
            for i in range(len(family)):
                for t in _PROPERTY_DOMAIN:
                    if _eval_lean_formula(
                        correct, family, i, t, _PROPERTY_DOMAIN
                    ) != _eval_lean_formula(swapped, family, i, t, _PROPERTY_DOMAIN):
                        disagreement = True
        assert disagreement, "the guard/event swap on \\Until was not detected at any family point"

    def test_asymmetry_sensitivity_control_since(self):
        sentence = _sentence("(p \\Since q)")
        correct = translate(sentence)
        assert isinstance(correct, Snce)
        swapped = Snce(guard=correct.event, event=correct.guard)

        disagreement = False
        for family in _PROPERTY_FAMILIES:
            for i in range(len(family)):
                for t in _PROPERTY_DOMAIN:
                    if _eval_lean_formula(
                        correct, family, i, t, _PROPERTY_DOMAIN
                    ) != _eval_lean_formula(swapped, family, i, t, _PROPERTY_DOMAIN):
                        disagreement = True
        assert disagreement, "the guard/event swap on \\Since was not detected at any family point"

    def test_elimination_control_next_wrong_pre_normalization_order(self):
        """A wrong elimination of `\\next A` using the pre-normalization (event-first) operand
        order -- `Untl(guard=A, event=bot)` instead of the correct guard-first
        `Untl(guard=bot, event=A)` -- must be detected by the differential. This is exactly the
        defect a missed flip of `DefNextOperator.derived_definition` (Phase 2) would have
        produced, and is the control that would have caught it."""
        sentence = _sentence("\\next p")
        correct = translate(sentence)
        assert isinstance(correct, Untl)
        wrong = Untl(guard=correct.event, event=correct.guard)  # the retired event-first order

        disagreement = False
        for family in _PROPERTY_FAMILIES:
            for i in range(len(family)):
                for t in _PROPERTY_DOMAIN:
                    if _eval_lean_formula(
                        correct, family, i, t, _PROPERTY_DOMAIN
                    ) != _eval_lean_formula(wrong, family, i, t, _PROPERTY_DOMAIN):
                        disagreement = True
        assert disagreement, (
            "the pre-normalization event-first \\next elimination was not detected at any "
            "family point"
        )
