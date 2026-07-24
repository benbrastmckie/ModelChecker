"""Tests for formula fold/unfold normalization utilities.

Tests for three public functions in bimodal_logic.translation:
  unfold_formula(formula_json) - recursively expand enriched tags to 6 primitives
  fold_formula(formula_json) - outside-in pattern matching Level 3->1 ordering
  normalize_formula(formula_json, level) - fold/unfold to specific operator level

Phase 1: TestUnfoldFormula - verify all 11 enriched tags expand to primitives
Phase 2: TestFoldFormula, TestOverlappingPatterns - verify all 11 patterns fold
Phase 3: TestNormalizeFormula - verify level-based normalization and exports
Phase 4: TestRoundTrip, TestAllEnrichedPatternsFoldable - property-based tests
"""

from __future__ import annotations

import random
import pytest

from bimodal_logic.translation import unfold_formula, fold_formula, normalize_formula


##############################################################################
# Shared helpers
##############################################################################

PRIMITIVE_TAGS = frozenset({"atom", "bot", "imp", "box", "untl", "snce"})

ENRICHED_LEVEL1 = frozenset({"neg", "top", "next", "prev"})
ENRICHED_LEVEL2 = frozenset({"and", "or", "diamond", "some_future", "some_past"})
ENRICHED_LEVEL3 = frozenset({"all_future", "all_past"})
ALL_ENRICHED = ENRICHED_LEVEL1 | ENRICHED_LEVEL2 | ENRICHED_LEVEL3

# Formula builders
def atom(name): return {"tag": "atom", "name": name}
def bot(): return {"tag": "bot"}
def top(): return {"tag": "top"}
def imp(l, r): return {"tag": "imp", "left": l, "right": r}
def box(c): return {"tag": "box", "child": c}
def untl(e, g): return {"tag": "untl", "event": e, "guard": g}
def snce(e, g): return {"tag": "snce", "event": e, "guard": g}
def neg(a): return {"tag": "neg", "arg": a}
def and_(l, r): return {"tag": "and", "left": l, "right": r}
def or_(l, r): return {"tag": "or", "left": l, "right": r}
def diamond(a): return {"tag": "diamond", "arg": a}
def next_(a): return {"tag": "next", "arg": a}
def prev_(a): return {"tag": "prev", "arg": a}
def some_future(a): return {"tag": "some_future", "arg": a}
def some_past(a): return {"tag": "some_past", "arg": a}
def all_future(a): return {"tag": "all_future", "arg": a}
def all_past(a): return {"tag": "all_past", "arg": a}


def _all_tags_in(formula):
    """Collect all tags in a formula tree by recursive walk."""
    tags = {formula["tag"]}
    tag = formula["tag"]
    if tag == "atom":
        pass
    elif tag in ("bot", "top"):
        pass
    elif tag in ("imp", "and", "or"):
        tags |= _all_tags_in(formula.get("left", {}))
        tags |= _all_tags_in(formula.get("right", {}))
    elif tag in ("box",):
        tags |= _all_tags_in(formula["child"])
    elif tag in ("untl", "snce"):
        tags |= _all_tags_in(formula["event"])
        tags |= _all_tags_in(formula["guard"])
    elif tag in ("neg", "diamond", "next", "prev",
                 "some_future", "some_past", "all_future", "all_past"):
        tags |= _all_tags_in(formula["arg"])
    return tags


def assert_only_primitives(formula):
    """Walk formula tree and assert all tags are primitive."""
    all_tags = _all_tags_in(formula)
    bad = all_tags - PRIMITIVE_TAGS
    assert not bad, f"Non-primitive tags found: {bad}"


##############################################################################
# Phase 1: TestUnfoldFormula
##############################################################################

class TestUnfoldFormula:
    """Tests for unfold_formula: all enriched tags expand to primitives."""

    # Primitive passthrough
    def test_atom_passthrough(self):
        """Atom is returned unchanged."""
        f = atom("p")
        result = unfold_formula(f)
        assert result == atom("p")

    def test_bot_passthrough(self):
        """Bot is returned unchanged."""
        result = unfold_formula(bot())
        assert result == bot()

    def test_imp_passthrough_atoms(self):
        """imp(p, q) with atom children is returned structurally unchanged."""
        f = imp(atom("p"), atom("q"))
        result = unfold_formula(f)
        assert result == imp(atom("p"), atom("q"))

    def test_box_passthrough_atom(self):
        """box(p) is returned structurally unchanged."""
        f = box(atom("p"))
        result = unfold_formula(f)
        assert result == box(atom("p"))

    def test_untl_passthrough_atoms(self):
        """untl(p, q) is returned structurally unchanged."""
        f = untl(atom("p"), atom("q"))
        result = unfold_formula(f)
        assert result == untl(atom("p"), atom("q"))

    def test_snce_passthrough_atoms(self):
        """snce(p, q) is returned structurally unchanged."""
        f = snce(atom("p"), atom("q"))
        result = unfold_formula(f)
        assert result == snce(atom("p"), atom("q"))

    # Level 1 enriched expansions
    def test_neg_expands_to_imp_bot(self):
        """neg(p) -> imp(p, bot)."""
        f = neg(atom("p"))
        result = unfold_formula(f)
        assert result == imp(atom("p"), bot())

    def test_top_expands_to_imp_bot_bot(self):
        """top -> imp(bot, bot)."""
        result = unfold_formula(top())
        assert result == imp(bot(), bot())

    def test_next_expands_to_untl_bot(self):
        """next(p) -> untl(p, bot)."""
        f = next_(atom("p"))
        result = unfold_formula(f)
        assert result == untl(atom("p"), bot())

    def test_prev_expands_to_snce_bot(self):
        """prev(p) -> snce(p, bot)."""
        f = prev_(atom("p"))
        result = unfold_formula(f)
        assert result == snce(atom("p"), bot())

    # Level 2 enriched expansions
    def test_and_expands_correctly(self):
        """and(p, q) -> imp(imp(p, imp(q, bot)), bot)."""
        f = and_(atom("p"), atom("q"))
        result = unfold_formula(f)
        expected = imp(
            imp(atom("p"), imp(atom("q"), bot())),
            bot()
        )
        assert result == expected

    def test_or_expands_correctly(self):
        """or(p, q) -> imp(imp(p, bot), q)."""
        f = or_(atom("p"), atom("q"))
        result = unfold_formula(f)
        expected = imp(imp(atom("p"), bot()), atom("q"))
        assert result == expected

    def test_diamond_expands_correctly(self):
        """diamond(p) -> imp(box(imp(p, bot)), bot)."""
        f = diamond(atom("p"))
        result = unfold_formula(f)
        expected = imp(box(imp(atom("p"), bot())), bot())
        assert result == expected

    def test_some_future_expands_correctly(self):
        """some_future(p) -> untl(p, imp(bot, bot))."""
        f = some_future(atom("p"))
        result = unfold_formula(f)
        expected = untl(atom("p"), imp(bot(), bot()))
        assert result == expected

    def test_some_past_expands_correctly(self):
        """some_past(p) -> snce(p, imp(bot, bot))."""
        f = some_past(atom("p"))
        result = unfold_formula(f)
        expected = snce(atom("p"), imp(bot(), bot()))
        assert result == expected

    # Level 3 enriched expansions
    def test_all_future_expands_correctly(self):
        """all_future(p) -> imp(untl(imp(p, bot), imp(bot, bot)), bot)."""
        f = all_future(atom("p"))
        result = unfold_formula(f)
        expected = imp(
            untl(imp(atom("p"), bot()), imp(bot(), bot())),
            bot()
        )
        assert result == expected

    def test_all_past_expands_correctly(self):
        """all_past(p) -> imp(snce(imp(p, bot), imp(bot, bot)), bot)."""
        f = all_past(atom("p"))
        result = unfold_formula(f)
        expected = imp(
            snce(imp(atom("p"), bot()), imp(bot(), bot())),
            bot()
        )
        assert result == expected

    # All expansions produce only primitives
    def test_neg_produces_only_primitives(self):
        assert_only_primitives(unfold_formula(neg(atom("p"))))

    def test_top_produces_only_primitives(self):
        assert_only_primitives(unfold_formula(top()))

    def test_and_produces_only_primitives(self):
        assert_only_primitives(unfold_formula(and_(atom("p"), atom("q"))))

    def test_or_produces_only_primitives(self):
        assert_only_primitives(unfold_formula(or_(atom("p"), atom("q"))))

    def test_diamond_produces_only_primitives(self):
        assert_only_primitives(unfold_formula(diamond(atom("p"))))

    def test_next_produces_only_primitives(self):
        assert_only_primitives(unfold_formula(next_(atom("p"))))

    def test_prev_produces_only_primitives(self):
        assert_only_primitives(unfold_formula(prev_(atom("p"))))

    def test_some_future_produces_only_primitives(self):
        assert_only_primitives(unfold_formula(some_future(atom("p"))))

    def test_some_past_produces_only_primitives(self):
        assert_only_primitives(unfold_formula(some_past(atom("p"))))

    def test_all_future_produces_only_primitives(self):
        assert_only_primitives(unfold_formula(all_future(atom("p"))))

    def test_all_past_produces_only_primitives(self):
        assert_only_primitives(unfold_formula(all_past(atom("p"))))

    # Nested formulas
    def test_neg_and_produces_only_primitives(self):
        """unfold(neg(and(p, q))) produces only primitive tags."""
        f = neg(and_(atom("p"), atom("q")))
        result = unfold_formula(f)
        assert_only_primitives(result)

    def test_nested_enriched_all_primitives(self):
        """Deeply nested enriched formula produces only primitives."""
        # all_future(diamond(neg(p)))
        f = all_future(diamond(neg(atom("p"))))
        result = unfold_formula(f)
        assert_only_primitives(result)

    def test_children_are_recursively_unfolded(self):
        """imp children containing enriched tags are recursively unfolded."""
        # imp(neg(p), neg(q)) -> imp(imp(p, bot), imp(q, bot))
        f = imp(neg(atom("p")), neg(atom("q")))
        result = unfold_formula(f)
        expected = imp(imp(atom("p"), bot()), imp(atom("q"), bot()))
        assert result == expected

    # Idempotency: unfold(unfold(f)) == unfold(f)
    def test_idempotency_neg(self):
        f = neg(atom("p"))
        once = unfold_formula(f)
        twice = unfold_formula(once)
        assert once == twice

    def test_idempotency_and(self):
        f = and_(atom("p"), atom("q"))
        once = unfold_formula(f)
        twice = unfold_formula(once)
        assert once == twice

    def test_idempotency_all_future(self):
        f = all_future(atom("p"))
        once = unfold_formula(f)
        twice = unfold_formula(once)
        assert once == twice

    def test_idempotency_nested(self):
        f = or_(neg(atom("p")), some_future(atom("q")))
        once = unfold_formula(f)
        twice = unfold_formula(once)
        assert once == twice


##############################################################################
# Phase 2: TestFoldFormula
##############################################################################

class TestFoldFormula:
    """Tests for fold_formula: primitive patterns are recognized as enriched tags."""

    # Primitive passthrough (no enriched pattern match)
    def test_atom_passthrough(self):
        """Atom is returned unchanged."""
        result = fold_formula(atom("p"))
        assert result == atom("p")

    def test_bot_passthrough(self):
        """Bot is returned unchanged."""
        result = fold_formula(bot())
        assert result == bot()

    def test_imp_pq_no_pattern(self):
        """imp(p, q) where q is not bot -> stays as imp (matches or pattern)."""
        # imp(p, q) -> or(neg(p), q) in fold? No - or is imp(imp(p,bot), q).
        # imp(p, q) does not match imp(p, bot) or imp(bot, something)
        # so fold should return imp(fold(p), fold(q)) = imp(p, q)
        f = imp(atom("p"), atom("q"))
        result = fold_formula(f)
        # imp(p, q) where right is not bot -> OR: imp(imp(p,bot), q) would match or
        # but f is imp(atom("p"), atom("q")), so left is atom (not imp), right is atom (not bot)
        # Does not match any enriched pattern, stays as imp
        assert result == imp(atom("p"), atom("q"))

    def test_box_passthrough(self):
        """box(p) is returned as box (no fold for plain box)."""
        f = box(atom("p"))
        result = fold_formula(f)
        assert result == box(atom("p"))

    def test_untl_atoms_no_pattern(self):
        """untl(p, q) where q is not bot and not top -> stays as untl."""
        f = untl(atom("p"), atom("q"))
        result = fold_formula(f)
        assert result == untl(atom("p"), atom("q"))

    def test_snce_atoms_no_pattern(self):
        """snce(p, q) where q is not bot and not top -> stays as snce."""
        f = snce(atom("p"), atom("q"))
        result = fold_formula(f)
        assert result == snce(atom("p"), atom("q"))

    # Level 1 recognition
    def test_fold_neg_from_primitive(self):
        """imp(p, bot) -> neg(p)."""
        f = imp(atom("p"), bot())
        result = fold_formula(f)
        assert result == neg(atom("p"))

    def test_fold_top_from_primitive(self):
        """imp(bot, bot) -> top."""
        f = imp(bot(), bot())
        result = fold_formula(f)
        assert result == top()

    def test_fold_next_from_primitive(self):
        """untl(p, bot) -> next(p)."""
        f = untl(atom("p"), bot())
        result = fold_formula(f)
        assert result == next_(atom("p"))

    def test_fold_prev_from_primitive(self):
        """snce(p, bot) -> prev(p)."""
        f = snce(atom("p"), bot())
        result = fold_formula(f)
        assert result == prev_(atom("p"))

    # Level 2 recognition
    def test_fold_and_from_primitive(self):
        """imp(imp(p, imp(q, bot)), bot) -> and(p, q)."""
        f = imp(imp(atom("p"), imp(atom("q"), bot())), bot())
        result = fold_formula(f)
        assert result == and_(atom("p"), atom("q"))

    def test_fold_or_from_primitive(self):
        """imp(imp(p, bot), q) -> or(p, q)."""
        f = imp(imp(atom("p"), bot()), atom("q"))
        result = fold_formula(f)
        assert result == or_(atom("p"), atom("q"))

    def test_fold_diamond_from_primitive(self):
        """imp(box(imp(p, bot)), bot) -> diamond(p)."""
        f = imp(box(imp(atom("p"), bot())), bot())
        result = fold_formula(f)
        assert result == diamond(atom("p"))

    def test_fold_some_future_from_primitive(self):
        """untl(p, imp(bot, bot)) -> some_future(p)."""
        f = untl(atom("p"), imp(bot(), bot()))
        result = fold_formula(f)
        assert result == some_future(atom("p"))

    def test_fold_some_past_from_primitive(self):
        """snce(p, imp(bot, bot)) -> some_past(p)."""
        f = snce(atom("p"), imp(bot(), bot()))
        result = fold_formula(f)
        assert result == some_past(atom("p"))

    # Level 3 recognition
    def test_fold_all_future_from_primitive(self):
        """imp(untl(imp(p, bot), imp(bot, bot)), bot) -> all_future(p)."""
        f = imp(untl(imp(atom("p"), bot()), imp(bot(), bot())), bot())
        result = fold_formula(f)
        assert result == all_future(atom("p"))

    def test_fold_all_past_from_primitive(self):
        """imp(snce(imp(p, bot), imp(bot, bot)), bot) -> all_past(p)."""
        f = imp(snce(imp(atom("p"), bot()), imp(bot(), bot())), bot())
        result = fold_formula(f)
        assert result == all_past(atom("p"))

    # Children are recursively folded
    def test_children_are_recursively_folded(self):
        """fold(imp(imp(p, bot), bot)) -> neg(neg(p)) not neg(imp(p, bot))."""
        # imp(imp(p, bot), bot) is neg(neg(p)) after recursive folding:
        # outer: imp(X, bot) where X=imp(p, bot) -> neg(X)
        # but X=imp(p, bot) also folds to neg(p)
        # so result = neg(neg(p))
        f = imp(imp(atom("p"), bot()), bot())
        result = fold_formula(f)
        assert result == neg(neg(atom("p")))


##############################################################################
# Phase 2: TestOverlappingPatterns
##############################################################################

class TestOverlappingPatterns:
    """Tests for fold_formula disambiguation: overlapping patterns in imp(X, bot)."""

    def test_top_preferred_over_neg_bot(self):
        """imp(bot, bot) -> top, not neg(bot)."""
        f = imp(bot(), bot())
        result = fold_formula(f)
        assert result == top()
        assert result != neg(bot())

    def test_all_future_preferred_over_neg(self):
        """imp(untl(imp(p,bot), imp(bot,bot)), bot) -> all_future(p), not neg(...)."""
        f = imp(untl(imp(atom("p"), bot()), imp(bot(), bot())), bot())
        result = fold_formula(f)
        assert result == all_future(atom("p"))
        # Verify it was NOT folded as neg
        assert result["tag"] == "all_future"

    def test_all_past_preferred_over_neg(self):
        """imp(snce(imp(p,bot), imp(bot,bot)), bot) -> all_past(p), not neg(...)."""
        f = imp(snce(imp(atom("p"), bot()), imp(bot(), bot())), bot())
        result = fold_formula(f)
        assert result == all_past(atom("p"))
        assert result["tag"] == "all_past"

    def test_diamond_preferred_over_neg(self):
        """imp(box(imp(p,bot)), bot) -> diamond(p), not neg(box(neg(p)))."""
        f = imp(box(imp(atom("p"), bot())), bot())
        result = fold_formula(f)
        assert result == diamond(atom("p"))
        assert result["tag"] == "diamond"

    def test_and_preferred_over_neg(self):
        """imp(imp(p, imp(q, bot)), bot) -> and(p, q), not neg(imp(p, neg(q)))."""
        f = imp(imp(atom("p"), imp(atom("q"), bot())), bot())
        result = fold_formula(f)
        assert result == and_(atom("p"), atom("q"))
        assert result["tag"] == "and"

    def test_or_not_confused_with_neg(self):
        """imp(imp(p, bot), q) -> or(p, q) when q is not bot."""
        f = imp(imp(atom("p"), bot()), atom("q"))
        result = fold_formula(f)
        assert result == or_(atom("p"), atom("q"))
        assert result["tag"] == "or"

    def test_neg_is_fallback_for_imp_x_bot(self):
        """imp(atom, bot) -> neg(atom) (fallback case)."""
        f = imp(atom("p"), bot())
        result = fold_formula(f)
        assert result["tag"] == "neg"

    def test_neg_with_box_atom_child(self):
        """imp(box(p), bot) -> neg(box(p)) [box without neg-child is not diamond]."""
        f = imp(box(atom("p")), bot())
        result = fold_formula(f)
        assert result["tag"] == "neg"
        # The box child should itself be folded (it's just atom(p), stays as atom)
        assert result["arg"]["tag"] == "box"

    def test_some_future_vs_untl_atoms(self):
        """untl(p, imp(bot, bot)) -> some_future(p) (top guard matches)."""
        f = untl(atom("p"), imp(bot(), bot()))
        result = fold_formula(f)
        assert result == some_future(atom("p"))

    def test_next_vs_untl_bot(self):
        """untl(p, bot) -> next(p) (bot guard matches next)."""
        f = untl(atom("p"), bot())
        result = fold_formula(f)
        assert result == next_(atom("p"))


##############################################################################
# Phase 3: TestNormalizeFormula
##############################################################################

class TestNormalizeFormula:
    """Tests for normalize_formula with levels 0-3."""

    def test_level_0_equals_unfold_neg(self):
        """normalize(neg(p), 0) == unfold(neg(p))."""
        f = neg(atom("p"))
        assert normalize_formula(f, 0) == unfold_formula(f)

    def test_level_0_equals_unfold_all_future(self):
        """normalize(all_future(p), 0) == unfold(all_future(p))."""
        f = all_future(atom("p"))
        assert normalize_formula(f, 0) == unfold_formula(f)

    def test_level_0_produces_only_primitives(self):
        """normalize(f, 0) produces only primitive tags."""
        for f in [neg(atom("p")), and_(atom("p"), atom("q")), all_future(atom("p"))]:
            result = normalize_formula(f, 0)
            assert_only_primitives(result)

    def test_level_1_uses_neg_not_and(self):
        """normalize(and(p, q), 1) uses neg but not and."""
        f = and_(atom("p"), atom("q"))
        result = normalize_formula(f, 1)
        all_tags = _all_tags_in(result)
        # Level 1 can use neg, top, next, prev but not and/or/diamond/etc.
        assert "and" not in all_tags
        assert "neg" in all_tags or result["tag"] in PRIMITIVE_TAGS

    def test_level_1_no_level2_or_level3_tags(self):
        """normalize(f, 1) contains no Level 2 or Level 3 tags."""
        formulas = [
            and_(atom("p"), atom("q")),
            or_(atom("p"), atom("q")),
            diamond(atom("p")),
            some_future(atom("p")),
            some_past(atom("p")),
            all_future(atom("p")),
            all_past(atom("p")),
        ]
        forbidden = ENRICHED_LEVEL2 | ENRICHED_LEVEL3
        for f in formulas:
            result = normalize_formula(f, 1)
            all_tags = _all_tags_in(result)
            assert not (all_tags & forbidden), (
                f"normalize({f}, 1) contained forbidden tags: {all_tags & forbidden}"
            )

    def test_level_2_allows_level1_and_level2(self):
        """normalize(all_future(p), 2) uses enriched from Level 1+2 but not Level 3."""
        f = all_future(atom("p"))
        result = normalize_formula(f, 2)
        all_tags = _all_tags_in(result)
        assert "all_future" not in all_tags
        assert "all_past" not in all_tags

    def test_level_2_some_future_folds(self):
        """normalize(all_future(p), 2) - all_future unfolds and folds to some_future+neg."""
        f = all_future(atom("p"))
        result = normalize_formula(f, 2)
        # all_future(p) unfolds to imp(untl(imp(p,bot),imp(bot,bot)),bot)
        # at level 2: untl(neg(p), top) matches some_future for the guard
        # but outer imp(X, bot) might fold to neg or not
        # key: no level3 tags
        all_tags = _all_tags_in(result)
        assert not (all_tags & ENRICHED_LEVEL3)

    def test_level_3_equals_fold_of_unfold(self):
        """normalize(f, 3) == fold(unfold(f))."""
        formulas = [
            neg(atom("p")),
            and_(atom("p"), atom("q")),
            all_future(atom("p")),
            or_(neg(atom("p")), some_future(atom("q"))),
        ]
        for f in formulas:
            assert normalize_formula(f, 3) == fold_formula(unfold_formula(f)), (
                f"normalize({f}, 3) != fold(unfold({f}))"
            )

    def test_invalid_level_negative_raises_value_error(self):
        """normalize(f, -1) raises ValueError."""
        with pytest.raises(ValueError):
            normalize_formula(atom("p"), -1)

    def test_invalid_level_four_raises_value_error(self):
        """normalize(f, 4) raises ValueError."""
        with pytest.raises(ValueError):
            normalize_formula(atom("p"), 4)


##############################################################################
# Phase 4: TestRoundTrip
##############################################################################

def random_formula(atoms, max_depth, rng):
    """Generate a random formula JSON dict with all 17 tags."""
    if max_depth == 0:
        # Only nullary or atoms
        choice = rng.randint(0, len(atoms) + 1)
        if choice < len(atoms):
            return atom(atoms[choice])
        elif choice == len(atoms):
            return bot()
        else:
            return top()

    # Decide arity
    arity = rng.randint(0, 3)  # 0=nullary, 1=unary, 2=binary

    if arity == 0:
        choice = rng.randint(0, len(atoms) + 1)
        if choice < len(atoms):
            return atom(atoms[choice])
        elif choice == len(atoms):
            return bot()
        else:
            return top()

    elif arity == 1:
        child = random_formula(atoms, max_depth - 1, rng)
        tag_choice = rng.randint(0, 6)
        if tag_choice == 0:
            return neg(child)
        elif tag_choice == 1:
            return box(child) if rng.randint(0, 1) == 0 else {"tag": "box", "child": child}
        elif tag_choice == 2:
            return diamond(child)
        elif tag_choice == 3:
            return next_(child)
        elif tag_choice == 4:
            return prev_(child)
        elif tag_choice == 5:
            return some_future(child)
        else:
            return some_past(child)

    else:  # arity == 2
        left = random_formula(atoms, max_depth - 1, rng)
        right = random_formula(atoms, max_depth - 1, rng)
        tag_choice = rng.randint(0, 7)
        if tag_choice == 0:
            return imp(left, right)
        elif tag_choice == 1:
            return and_(left, right)
        elif tag_choice == 2:
            return or_(left, right)
        elif tag_choice == 3:
            return untl(left, right)
        elif tag_choice == 4:
            return snce(left, right)
        elif tag_choice == 5:
            return all_future(left)  # only uses left arg
        else:
            return all_past(left)  # only uses left arg


class TestRoundTrip:
    """Property-based round-trip tests for fold/unfold."""

    ATOMS = ["p", "q", "r"]
    MAX_DEPTH = 4
    N_FORMULAS = 120  # > 100 as required

    def _generate_formulas(self, n):
        rng = random.Random(42)
        return [random_formula(self.ATOMS, self.MAX_DEPTH, rng) for _ in range(n)]

    def test_unfold_fold_roundtrip_100(self):
        """unfold(fold(unfold(f))) == unfold(f) for 100+ random formulas."""
        formulas = self._generate_formulas(self.N_FORMULAS)
        for i, f in enumerate(formulas):
            u = unfold_formula(f)
            fu = fold_formula(u)
            ufu = unfold_formula(fu)
            assert ufu == u, (
                f"Formula {i}: unfold(fold(unfold(f))) != unfold(f)\n"
                f"  f = {f}\n  unfold(f) = {u}\n  fold(unfold(f)) = {fu}\n"
                f"  unfold(fold(unfold(f))) = {ufu}"
            )

    def test_fold_idempotent_after_unfold(self):
        """fold(fold(unfold(f))) == fold(unfold(f)) for 100+ random formulas."""
        formulas = self._generate_formulas(self.N_FORMULAS)
        for i, f in enumerate(formulas):
            u = unfold_formula(f)
            fu = fold_formula(u)
            ffu = fold_formula(fu)
            assert ffu == fu, (
                f"Formula {i}: fold(fold(unfold(f))) != fold(unfold(f))\n"
                f"  f = {f}\n  fold(unfold(f)) = {fu}\n"
                f"  fold(fold(unfold(f))) = {ffu}"
            )

    def test_unfold_idempotent(self):
        """unfold(unfold(f)) == unfold(f) for 100+ random formulas."""
        formulas = self._generate_formulas(self.N_FORMULAS)
        for i, f in enumerate(formulas):
            u1 = unfold_formula(f)
            u2 = unfold_formula(u1)
            assert u1 == u2, (
                f"Formula {i}: unfold(unfold(f)) != unfold(f)\n"
                f"  f = {f}\n  unfold(f) = {u1}\n  unfold(unfold(f)) = {u2}"
            )

    def test_unfold_produces_only_primitives(self):
        """unfold(f) contains only primitive tags for 100+ random formulas."""
        formulas = self._generate_formulas(self.N_FORMULAS)
        for i, f in enumerate(formulas):
            u = unfold_formula(f)
            all_tags = _all_tags_in(u)
            bad = all_tags - PRIMITIVE_TAGS
            assert not bad, (
                f"Formula {i}: unfold(f) contained non-primitive tags {bad}\n"
                f"  f = {f}\n  unfold(f) = {u}"
            )

    def test_normalize_level0_equals_unfold(self):
        """normalize(f, 0) == unfold(f) for 50+ random formulas."""
        rng = random.Random(99)
        formulas = [random_formula(self.ATOMS, self.MAX_DEPTH, rng) for _ in range(60)]
        for i, f in enumerate(formulas):
            assert normalize_formula(f, 0) == unfold_formula(f), (
                f"Formula {i}: normalize(f, 0) != unfold(f)\n  f = {f}"
            )

    def test_normalize_level3_equals_fold_unfold(self):
        """normalize(f, 3) == fold(unfold(f)) for 50+ random formulas."""
        rng = random.Random(77)
        formulas = [random_formula(self.ATOMS, self.MAX_DEPTH, rng) for _ in range(60)]
        for i, f in enumerate(formulas):
            assert normalize_formula(f, 3) == fold_formula(unfold_formula(f)), (
                f"Formula {i}: normalize(f, 3) != fold(unfold(f))\n  f = {f}"
            )


##############################################################################
# Phase 4: TestAllEnrichedPatternsFoldable
##############################################################################

class TestAllEnrichedPatternsFoldable:
    """Gate requirement: fold recognizes all 11 enriched patterns from primitive expansions."""

    def _check_roundtrip(self, enriched_formula, expected_tag):
        """Verify that fold(unfold(f)) has the expected top-level tag."""
        unfolded = unfold_formula(enriched_formula)
        folded = fold_formula(unfolded)
        assert folded["tag"] == expected_tag, (
            f"Expected fold(unfold({enriched_formula})) to have tag '{expected_tag}', "
            f"got '{folded['tag']}'\n  unfolded = {unfolded}\n  folded = {folded}"
        )

    def test_neg_foldable(self):
        self._check_roundtrip(neg(atom("p")), "neg")

    def test_top_foldable(self):
        self._check_roundtrip(top(), "top")

    def test_next_foldable(self):
        self._check_roundtrip(next_(atom("p")), "next")

    def test_prev_foldable(self):
        self._check_roundtrip(prev_(atom("p")), "prev")

    def test_and_foldable(self):
        self._check_roundtrip(and_(atom("p"), atom("q")), "and")

    def test_or_foldable(self):
        self._check_roundtrip(or_(atom("p"), atom("q")), "or")

    def test_diamond_foldable(self):
        self._check_roundtrip(diamond(atom("p")), "diamond")

    def test_some_future_foldable(self):
        self._check_roundtrip(some_future(atom("p")), "some_future")

    def test_some_past_foldable(self):
        self._check_roundtrip(some_past(atom("p")), "some_past")

    def test_all_future_foldable(self):
        self._check_roundtrip(all_future(atom("p")), "all_future")

    def test_all_past_foldable(self):
        self._check_roundtrip(all_past(atom("p")), "all_past")
