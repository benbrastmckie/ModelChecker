"""Tests for Formula JSON translation: json_to_prefix, temporal_depth, prefix_to_infix.

Phase 1: TDD RED phase -- tests written before implementation.
Phase 3: Sentence.from_prefix and Syntax integration tests.
Phase 4: Enriched operator Z3 equivalence tests.

JSON Formula Schema:
  Primitive tags (6): atom, bot, imp, box, untl, snce
  Enriched tags (11): neg, top, and, or, diamond, next, prev,
                      some_future, some_past, all_future, all_past

Field names per tag:
  atom: {"tag": "atom", "name": "p"}
  bot: {"tag": "bot"}
  imp: {"tag": "imp", "left": ..., "right": ...}
  box: {"tag": "box", "child": ...}
  untl: {"tag": "untl", "event": ..., "guard": ...}
  snce: {"tag": "snce", "event": ..., "guard": ...}
  neg: {"tag": "neg", "arg": ...}
  top: {"tag": "top"}
  and: {"tag": "and", "left": ..., "right": ...}
  or: {"tag": "or", "left": ..., "right": ...}
  diamond: {"tag": "diamond", "arg": ...}
  next: {"tag": "next", "arg": ...}
  prev: {"tag": "prev", "arg": ...}
  some_future: {"tag": "some_future", "arg": ...}
  some_past: {"tag": "some_past", "arg": ...}
  all_future: {"tag": "all_future", "arg": ...}
  all_past: {"tag": "all_past", "arg": ...}
"""

from __future__ import annotations

import pytest

# These imports will fail until Phase 2 (intentional RED state)
from bimodal_logic.translation import json_to_prefix, temporal_depth, prefix_to_infix


##############################################################################
# Phase 1: Tests for json_to_prefix -- Primitive Tags
##############################################################################

class TestJsonToPrefixPrimitives:
    """Tests for json_to_prefix with all 6 primitive JSON tags."""

    def test_atom_translation(self):
        """Atom formula translates to single-element list with atom name."""
        result = json_to_prefix({"tag": "atom", "name": "p"})
        assert result == ["p"]

    def test_atom_translation_different_name(self):
        """Atom formula with different name translates correctly."""
        result = json_to_prefix({"tag": "atom", "name": "q"})
        assert result == ["q"]

    def test_bot_translation(self):
        """Bot formula translates to [\\bot]."""
        result = json_to_prefix({"tag": "bot"})
        assert result == ["\\bot"]

    def test_imp_translation(self):
        """Implication translates to prefix: [\\rightarrow, left_prefix, right_prefix]."""
        formula = {
            "tag": "imp",
            "left": {"tag": "atom", "name": "p"},
            "right": {"tag": "atom", "name": "q"}
        }
        result = json_to_prefix(formula)
        assert result == ["\\rightarrow", ["p"], ["q"]]

    def test_box_translation(self):
        """Box (necessity) translates to prefix: [\\Box, child_prefix]."""
        formula = {
            "tag": "box",
            "child": {"tag": "atom", "name": "p"}
        }
        result = json_to_prefix(formula)
        assert result == ["\\Box", ["p"]]

    def test_untl_translation(self):
        """Until translates to prefix: [\\Until, event_prefix, guard_prefix]."""
        formula = {
            "tag": "untl",
            "event": {"tag": "atom", "name": "p"},
            "guard": {"tag": "atom", "name": "q"}
        }
        result = json_to_prefix(formula)
        assert result == ["\\Until", ["p"], ["q"]]

    def test_snce_translation(self):
        """Since translates to prefix: [\\Since, event_prefix, guard_prefix]."""
        formula = {
            "tag": "snce",
            "event": {"tag": "atom", "name": "p"},
            "guard": {"tag": "atom", "name": "q"}
        }
        result = json_to_prefix(formula)
        assert result == ["\\Since", ["p"], ["q"]]

    def test_imp_with_bot_left(self):
        """Implication with bot as left argument."""
        formula = {
            "tag": "imp",
            "left": {"tag": "bot"},
            "right": {"tag": "atom", "name": "p"}
        }
        result = json_to_prefix(formula)
        assert result == ["\\rightarrow", ["\\bot"], ["p"]]

    def test_box_with_bot(self):
        """Box applied to bot."""
        formula = {
            "tag": "box",
            "child": {"tag": "bot"}
        }
        result = json_to_prefix(formula)
        assert result == ["\\Box", ["\\bot"]]

    def test_untl_with_bot_guard(self):
        """Until with bot as guard (equivalent to Next)."""
        formula = {
            "tag": "untl",
            "event": {"tag": "atom", "name": "p"},
            "guard": {"tag": "bot"}
        }
        result = json_to_prefix(formula)
        assert result == ["\\Until", ["p"], ["\\bot"]]


##############################################################################
# Phase 1: Tests for json_to_prefix -- Enriched Tags
##############################################################################

class TestJsonToPrefixEnriched:
    """Tests for json_to_prefix with all 11 enriched JSON tags."""

    def test_neg_translation(self):
        """Neg (negation) translates to [\\neg, arg_prefix]."""
        formula = {"tag": "neg", "arg": {"tag": "atom", "name": "p"}}
        result = json_to_prefix(formula)
        assert result == ["\\neg", ["p"]]

    def test_top_translation(self):
        """Top (tautology) translates to [\\top]."""
        result = json_to_prefix({"tag": "top"})
        assert result == ["\\top"]

    def test_and_translation(self):
        """And (conjunction) translates to [\\wedge, left_prefix, right_prefix]."""
        formula = {
            "tag": "and",
            "left": {"tag": "atom", "name": "p"},
            "right": {"tag": "atom", "name": "q"}
        }
        result = json_to_prefix(formula)
        assert result == ["\\wedge", ["p"], ["q"]]

    def test_or_translation(self):
        """Or (disjunction) translates to [\\vee, left_prefix, right_prefix]."""
        formula = {
            "tag": "or",
            "left": {"tag": "atom", "name": "p"},
            "right": {"tag": "atom", "name": "q"}
        }
        result = json_to_prefix(formula)
        assert result == ["\\vee", ["p"], ["q"]]

    def test_diamond_translation(self):
        """Diamond (possibility) translates to [\\Diamond, arg_prefix]."""
        formula = {"tag": "diamond", "arg": {"tag": "atom", "name": "p"}}
        result = json_to_prefix(formula)
        assert result == ["\\Diamond", ["p"]]

    def test_next_translation(self):
        """Next translates to [\\next, arg_prefix]."""
        formula = {"tag": "next", "arg": {"tag": "atom", "name": "p"}}
        result = json_to_prefix(formula)
        assert result == ["\\next", ["p"]]

    def test_prev_translation(self):
        """Prev translates to [\\prev, arg_prefix]."""
        formula = {"tag": "prev", "arg": {"tag": "atom", "name": "p"}}
        result = json_to_prefix(formula)
        assert result == ["\\prev", ["p"]]

    def test_some_future_translation(self):
        """Some_future (DefFuture) translates to [\\future, arg_prefix]."""
        formula = {"tag": "some_future", "arg": {"tag": "atom", "name": "p"}}
        result = json_to_prefix(formula)
        assert result == ["\\future", ["p"]]

    def test_some_past_translation(self):
        """Some_past (DefPast) translates to [\\past, arg_prefix]."""
        formula = {"tag": "some_past", "arg": {"tag": "atom", "name": "p"}}
        result = json_to_prefix(formula)
        assert result == ["\\past", ["p"]]

    def test_all_future_translation(self):
        """All_future (FutureOperator G) translates to [\\Future, arg_prefix]."""
        formula = {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}}
        result = json_to_prefix(formula)
        assert result == ["\\Future", ["p"]]

    def test_all_past_translation(self):
        """All_past (PastOperator H) translates to [\\Past, arg_prefix]."""
        formula = {"tag": "all_past", "arg": {"tag": "atom", "name": "p"}}
        result = json_to_prefix(formula)
        assert result == ["\\Past", ["p"]]

    def test_neg_with_bot(self):
        """Negation of bot."""
        formula = {"tag": "neg", "arg": {"tag": "bot"}}
        result = json_to_prefix(formula)
        assert result == ["\\neg", ["\\bot"]]

    def test_and_with_top(self):
        """Conjunction with top."""
        formula = {
            "tag": "and",
            "left": {"tag": "atom", "name": "p"},
            "right": {"tag": "top"}
        }
        result = json_to_prefix(formula)
        assert result == ["\\wedge", ["p"], ["\\top"]]


##############################################################################
# Phase 1: Tests for json_to_prefix -- Nested Formulas
##############################################################################

class TestJsonToPrefixNested:
    """Tests for json_to_prefix with nested and complex formulas."""

    def test_nested_neg_next(self):
        """neg(next(atom)) translates to [\\neg, [\\next, [p]]]."""
        formula = {
            "tag": "neg",
            "arg": {"tag": "next", "arg": {"tag": "atom", "name": "p"}}
        }
        result = json_to_prefix(formula)
        assert result == ["\\neg", ["\\next", ["p"]]]

    def test_nested_binary(self):
        """and(atom, or(atom, atom)) translates to nested prefix."""
        formula = {
            "tag": "and",
            "left": {"tag": "atom", "name": "p"},
            "right": {
                "tag": "or",
                "left": {"tag": "atom", "name": "q"},
                "right": {"tag": "atom", "name": "r"}
            }
        }
        result = json_to_prefix(formula)
        assert result == ["\\wedge", ["p"], ["\\vee", ["q"], ["r"]]]

    def test_deeply_nested(self):
        """3+ levels of nesting."""
        # imp(neg(p), and(q, box(r)))
        formula = {
            "tag": "imp",
            "left": {"tag": "neg", "arg": {"tag": "atom", "name": "p"}},
            "right": {
                "tag": "and",
                "left": {"tag": "atom", "name": "q"},
                "right": {"tag": "box", "child": {"tag": "atom", "name": "r"}}
            }
        }
        result = json_to_prefix(formula)
        assert result == [
            "\\rightarrow",
            ["\\neg", ["p"]],
            ["\\wedge", ["q"], ["\\Box", ["r"]]]
        ]

    def test_nested_temporal_untl_in_box(self):
        """box(untl(p, q)) -- box containing until."""
        formula = {
            "tag": "box",
            "child": {
                "tag": "untl",
                "event": {"tag": "atom", "name": "p"},
                "guard": {"tag": "atom", "name": "q"}
            }
        }
        result = json_to_prefix(formula)
        assert result == ["\\Box", ["\\Until", ["p"], ["q"]]]

    def test_nested_imp_in_next(self):
        """next(imp(p, q)) -- next containing implication."""
        formula = {
            "tag": "next",
            "arg": {
                "tag": "imp",
                "left": {"tag": "atom", "name": "p"},
                "right": {"tag": "atom", "name": "q"}
            }
        }
        result = json_to_prefix(formula)
        assert result == ["\\next", ["\\rightarrow", ["p"], ["q"]]]

    def test_nested_snce_bot(self):
        """snce(p, bot) -- since with bot guard (equivalent to prev(p))."""
        formula = {
            "tag": "snce",
            "event": {"tag": "atom", "name": "p"},
            "guard": {"tag": "bot"}
        }
        result = json_to_prefix(formula)
        assert result == ["\\Since", ["p"], ["\\bot"]]

    def test_double_negation(self):
        """neg(neg(p)) -- double negation."""
        formula = {
            "tag": "neg",
            "arg": {"tag": "neg", "arg": {"tag": "atom", "name": "p"}}
        }
        result = json_to_prefix(formula)
        assert result == ["\\neg", ["\\neg", ["p"]]]


##############################################################################
# Phase 1: Tests for json_to_prefix -- Error Cases
##############################################################################

class TestJsonToPrefixErrors:
    """Tests for json_to_prefix error handling."""

    def test_unknown_tag_raises_value_error(self):
        """Unknown tag raises ValueError."""
        with pytest.raises(ValueError, match="unknown"):
            json_to_prefix({"tag": "unknown_tag_xyz"})

    def test_missing_tag_raises(self):
        """Formula dict without 'tag' field raises ValueError."""
        with pytest.raises((ValueError, KeyError)):
            json_to_prefix({"name": "p"})

    def test_missing_name_in_atom_raises(self):
        """Atom without 'name' field raises ValueError or KeyError."""
        with pytest.raises((ValueError, KeyError)):
            json_to_prefix({"tag": "atom"})

    def test_missing_left_in_imp_raises(self):
        """Imp without 'left' field raises ValueError or KeyError."""
        with pytest.raises((ValueError, KeyError)):
            json_to_prefix({"tag": "imp", "right": {"tag": "atom", "name": "p"}})

    def test_missing_right_in_imp_raises(self):
        """Imp without 'right' field raises ValueError or KeyError."""
        with pytest.raises((ValueError, KeyError)):
            json_to_prefix({"tag": "imp", "left": {"tag": "atom", "name": "p"}})

    def test_missing_child_in_box_raises(self):
        """Box without 'child' field raises ValueError or KeyError."""
        with pytest.raises((ValueError, KeyError)):
            json_to_prefix({"tag": "box"})

    def test_missing_event_in_untl_raises(self):
        """Untl without 'event' field raises ValueError or KeyError."""
        with pytest.raises((ValueError, KeyError)):
            json_to_prefix({"tag": "untl", "guard": {"tag": "atom", "name": "q"}})

    def test_missing_guard_in_untl_raises(self):
        """Untl without 'guard' field raises ValueError or KeyError."""
        with pytest.raises((ValueError, KeyError)):
            json_to_prefix({"tag": "untl", "event": {"tag": "atom", "name": "p"}})

    def test_missing_arg_in_neg_raises(self):
        """Neg without 'arg' field raises ValueError or KeyError."""
        with pytest.raises((ValueError, KeyError)):
            json_to_prefix({"tag": "neg"})


##############################################################################
# Phase 1: Tests for temporal_depth
##############################################################################

class TestTemporalDepth:
    """Tests for temporal_depth with all tag categories."""

    # Leaf nodes
    def test_atom_depth_is_zero(self):
        """Atom has temporal depth 0."""
        assert temporal_depth({"tag": "atom", "name": "p"}) == 0

    def test_bot_depth_is_zero(self):
        """Bot has temporal depth 0."""
        assert temporal_depth({"tag": "bot"}) == 0

    def test_top_depth_is_zero(self):
        """Top has temporal depth 0."""
        assert temporal_depth({"tag": "top"}) == 0

    # Extensional operators (no increment)
    def test_neg_atom_depth_is_zero(self):
        """neg(atom) has temporal depth 0 (extensional, no increment)."""
        formula = {"tag": "neg", "arg": {"tag": "atom", "name": "p"}}
        assert temporal_depth(formula) == 0

    def test_imp_atoms_depth_is_zero(self):
        """imp(atom, atom) has temporal depth 0."""
        formula = {
            "tag": "imp",
            "left": {"tag": "atom", "name": "p"},
            "right": {"tag": "atom", "name": "q"}
        }
        assert temporal_depth(formula) == 0

    def test_and_atoms_depth_is_zero(self):
        """and(atom, atom) has temporal depth 0."""
        formula = {
            "tag": "and",
            "left": {"tag": "atom", "name": "p"},
            "right": {"tag": "atom", "name": "q"}
        }
        assert temporal_depth(formula) == 0

    def test_or_atoms_depth_is_zero(self):
        """or(atom, atom) has temporal depth 0."""
        formula = {
            "tag": "or",
            "left": {"tag": "atom", "name": "p"},
            "right": {"tag": "atom", "name": "q"}
        }
        assert temporal_depth(formula) == 0

    # Modal operators (no increment)
    def test_box_atom_depth_is_zero(self):
        """box(atom) has temporal depth 0 (modal, no increment)."""
        formula = {"tag": "box", "child": {"tag": "atom", "name": "p"}}
        assert temporal_depth(formula) == 0

    def test_diamond_atom_depth_is_zero(self):
        """diamond(atom) has temporal depth 0 (modal, no increment)."""
        formula = {"tag": "diamond", "arg": {"tag": "atom", "name": "p"}}
        assert temporal_depth(formula) == 0

    # Temporal primitive operators (increment by 1)
    def test_untl_atoms_depth_is_one(self):
        """untl(atom, atom) has temporal depth 1."""
        formula = {
            "tag": "untl",
            "event": {"tag": "atom", "name": "p"},
            "guard": {"tag": "atom", "name": "q"}
        }
        assert temporal_depth(formula) == 1

    def test_snce_atoms_depth_is_one(self):
        """snce(atom, atom) has temporal depth 1."""
        formula = {
            "tag": "snce",
            "event": {"tag": "atom", "name": "p"},
            "guard": {"tag": "atom", "name": "q"}
        }
        assert temporal_depth(formula) == 1

    # Temporal enriched operators (increment by 1)
    def test_next_atom_depth_is_one(self):
        """next(atom) has temporal depth 1."""
        formula = {"tag": "next", "arg": {"tag": "atom", "name": "p"}}
        assert temporal_depth(formula) == 1

    def test_prev_atom_depth_is_one(self):
        """prev(atom) has temporal depth 1."""
        formula = {"tag": "prev", "arg": {"tag": "atom", "name": "p"}}
        assert temporal_depth(formula) == 1

    def test_some_future_atom_depth_is_one(self):
        """some_future(atom) has temporal depth 1."""
        formula = {"tag": "some_future", "arg": {"tag": "atom", "name": "p"}}
        assert temporal_depth(formula) == 1

    def test_some_past_atom_depth_is_one(self):
        """some_past(atom) has temporal depth 1."""
        formula = {"tag": "some_past", "arg": {"tag": "atom", "name": "p"}}
        assert temporal_depth(formula) == 1

    def test_all_future_atom_depth_is_one(self):
        """all_future(atom) has temporal depth 1."""
        formula = {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}}
        assert temporal_depth(formula) == 1

    def test_all_past_atom_depth_is_one(self):
        """all_past(atom) has temporal depth 1."""
        formula = {"tag": "all_past", "arg": {"tag": "atom", "name": "p"}}
        assert temporal_depth(formula) == 1

    # Nested temporal
    def test_next_untl_depth_is_two(self):
        """next(untl(atom, atom)) has temporal depth 2."""
        formula = {
            "tag": "next",
            "arg": {
                "tag": "untl",
                "event": {"tag": "atom", "name": "p"},
                "guard": {"tag": "atom", "name": "q"}
            }
        }
        assert temporal_depth(formula) == 2

    def test_untl_next_depth_is_two(self):
        """untl(next(p), atom) has temporal depth 2."""
        formula = {
            "tag": "untl",
            "event": {"tag": "next", "arg": {"tag": "atom", "name": "p"}},
            "guard": {"tag": "atom", "name": "q"}
        }
        assert temporal_depth(formula) == 2

    # Mixed modal-temporal
    def test_box_next_depth_is_one(self):
        """box(next(atom)) has temporal depth 1 (box does not increment)."""
        formula = {
            "tag": "box",
            "child": {"tag": "next", "arg": {"tag": "atom", "name": "p"}}
        }
        assert temporal_depth(formula) == 1

    def test_next_box_depth_is_one(self):
        """next(box(atom)) has temporal depth 1 (box does not increment)."""
        formula = {
            "tag": "next",
            "arg": {"tag": "box", "child": {"tag": "atom", "name": "p"}}
        }
        assert temporal_depth(formula) == 1

    def test_neg_next_depth_is_one(self):
        """neg(next(atom)) has temporal depth 1 (neg does not increment)."""
        formula = {
            "tag": "neg",
            "arg": {"tag": "next", "arg": {"tag": "atom", "name": "p"}}
        }
        assert temporal_depth(formula) == 1

    def test_imp_next_atom_depth_is_one(self):
        """imp(next(p), q) has temporal depth 1."""
        formula = {
            "tag": "imp",
            "left": {"tag": "next", "arg": {"tag": "atom", "name": "p"}},
            "right": {"tag": "atom", "name": "q"}
        }
        assert temporal_depth(formula) == 1

    def test_imp_max_depth(self):
        """imp(next(p), snce(q, r)) has temporal depth max(1, 1) = 1... wait, snce=1 + 0 = 1, next=1+0=1."""
        # imp is not temporal, takes max of children depths
        # next(p) has depth 1, snce(q, r) has depth 1
        formula = {
            "tag": "imp",
            "left": {"tag": "next", "arg": {"tag": "atom", "name": "p"}},
            "right": {
                "tag": "snce",
                "event": {"tag": "atom", "name": "q"},
                "guard": {"tag": "atom", "name": "r"}
            }
        }
        assert temporal_depth(formula) == 1

    def test_depth_three(self):
        """Depth-3 formula: next(next(next(atom)))."""
        formula = {
            "tag": "next",
            "arg": {
                "tag": "next",
                "arg": {
                    "tag": "next",
                    "arg": {"tag": "atom", "name": "p"}
                }
            }
        }
        assert temporal_depth(formula) == 3
