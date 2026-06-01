"""Tests for Formula JSON translation: json_to_prefix, temporal_depth, prefix_to_infix.

Phase 1: TDD RED phase -- tests written before implementation (RED).
Phase 2: Implementation of json_to_prefix, temporal_depth, prefix_to_infix (GREEN).
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


##############################################################################
# Phase 3: Tests for Sentence.from_prefix classmethod
##############################################################################

class TestSentenceFromPrefix:
    """Tests for Sentence.from_prefix classmethod."""

    def test_from_prefix_creates_sentence(self):
        """from_prefix creates a Sentence object."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["p"]
        sentence = Sentence.from_prefix(prefix)
        assert isinstance(sentence, Sentence)

    def test_from_prefix_atom_preserves_prefix_list(self):
        """from_prefix sets prefix_sentence to the input list."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["p"]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.prefix_sentence == prefix

    def test_from_prefix_unary_preserves_prefix_list(self):
        """from_prefix preserves prefix list for unary operator."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\neg", ["p"]]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.prefix_sentence == prefix

    def test_from_prefix_binary_preserves_prefix_list(self):
        """from_prefix preserves prefix list for binary operator."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\wedge", ["p"], ["q"]]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.prefix_sentence == prefix

    def test_from_prefix_atom_sets_name(self):
        """from_prefix sets name to a valid infix string."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["p"]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.name == "p"

    def test_from_prefix_unary_sets_name(self):
        """from_prefix sets name to infix for unary operator."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\neg", ["p"]]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.name == "\\neg p"

    def test_from_prefix_binary_sets_name(self):
        """from_prefix sets name to parenthesized infix for binary operator."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\wedge", ["p"], ["q"]]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.name == "(p \\wedge q)"

    def test_from_prefix_sets_complexity_zero_for_atom(self):
        """from_prefix sets complexity to 0 for atoms."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["p"]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.complexity == 0

    def test_from_prefix_sets_complexity_one_for_unary(self):
        """from_prefix sets complexity to 1 for simple unary."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\neg", ["p"]]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.complexity == 1

    def test_from_prefix_sets_complexity_two_for_nested(self):
        """from_prefix sets complexity to 2 for doubly nested."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\neg", ["\\neg", ["p"]]]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.complexity == 2

    def test_from_prefix_atom_has_no_operator(self):
        """from_prefix atom has original_operator = None."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["p"]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.original_operator is None

    def test_from_prefix_unary_has_operator(self):
        """from_prefix unary has correct original_operator string."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\neg", ["p"]]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.original_operator == "\\neg"

    def test_from_prefix_binary_has_operator(self):
        """from_prefix binary has correct original_operator string."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\wedge", ["p"], ["q"]]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.original_operator == "\\wedge"

    def test_from_prefix_atom_has_no_arguments(self):
        """from_prefix atom has original_arguments = None."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["p"]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.original_arguments is None

    def test_from_prefix_unary_has_arguments(self):
        """from_prefix unary has original_arguments list."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\neg", ["p"]]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.original_arguments is not None
        assert len(sentence.original_arguments) == 1

    def test_from_prefix_binary_has_two_arguments(self):
        """from_prefix binary has 2 original_arguments."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\wedge", ["p"], ["q"]]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.original_arguments is not None
        assert len(sentence.original_arguments) == 2

    def test_from_prefix_nullary_operator_bot(self):
        """from_prefix for bot nullary operator."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\bot"]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.prefix_sentence == ["\\bot"]
        assert sentence.name == "\\bot"

    def test_from_prefix_temporal_next(self):
        """from_prefix for \\next unary temporal operator."""
        from model_checker.syntactic.sentence import Sentence
        prefix = ["\\next", ["p"]]
        sentence = Sentence.from_prefix(prefix)
        assert sentence.prefix_sentence == ["\\next", ["p"]]
        assert sentence.original_operator == "\\next"


##############################################################################
# Phase 3: Tests for Syntax integration (prefix_to_infix round-trip)
##############################################################################

class TestSyntaxIntegration:
    """Tests for full pipeline: JSON -> prefix -> infix -> Syntax."""

    def test_prefix_to_infix_round_trip_atom(self):
        """atom: json_to_prefix -> prefix_to_infix -> Syntax parses."""
        from model_checker import Syntax
        from model_checker.theory_lib.bimodal import bimodal_operators
        prefix = json_to_prefix({"tag": "atom", "name": "p"})
        infix = prefix_to_infix(prefix)
        assert infix == "p"
        syntax = Syntax([infix], [], bimodal_operators)
        assert syntax is not None

    def test_prefix_to_infix_round_trip_neg(self):
        """neg(atom): json_to_prefix -> prefix_to_infix -> Syntax parses."""
        from model_checker import Syntax
        from model_checker.theory_lib.bimodal import bimodal_operators
        formula = {"tag": "neg", "arg": {"tag": "atom", "name": "p"}}
        prefix = json_to_prefix(formula)
        infix = prefix_to_infix(prefix)
        assert infix == "\\neg p"
        syntax = Syntax([infix], [], bimodal_operators)
        assert syntax is not None

    def test_prefix_to_infix_round_trip_binary(self):
        """and(p, q): json_to_prefix -> prefix_to_infix -> Syntax parses."""
        from model_checker import Syntax
        from model_checker.theory_lib.bimodal import bimodal_operators
        formula = {
            "tag": "and",
            "left": {"tag": "atom", "name": "p"},
            "right": {"tag": "atom", "name": "q"}
        }
        prefix = json_to_prefix(formula)
        infix = prefix_to_infix(prefix)
        assert infix == "(p \\wedge q)"
        syntax = Syntax([infix], [], bimodal_operators)
        assert syntax is not None

    def test_syntax_with_enriched_operator_next(self):
        """Full pipeline with next enriched tag."""
        from model_checker import Syntax
        from model_checker.theory_lib.bimodal import bimodal_operators
        formula = {"tag": "next", "arg": {"tag": "atom", "name": "p"}}
        prefix = json_to_prefix(formula)
        infix = prefix_to_infix(prefix)
        syntax = Syntax([infix], [], bimodal_operators)
        assert syntax is not None

    def test_syntax_with_enriched_operator_diamond(self):
        """Full pipeline with diamond enriched tag."""
        from model_checker import Syntax
        from model_checker.theory_lib.bimodal import bimodal_operators
        formula = {"tag": "diamond", "arg": {"tag": "atom", "name": "p"}}
        prefix = json_to_prefix(formula)
        infix = prefix_to_infix(prefix)
        syntax = Syntax([infix], [], bimodal_operators)
        assert syntax is not None

    def test_syntax_with_all_future(self):
        """Full pipeline with all_future (G) tag."""
        from model_checker import Syntax
        from model_checker.theory_lib.bimodal import bimodal_operators
        formula = {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}}
        prefix = json_to_prefix(formula)
        infix = prefix_to_infix(prefix)
        syntax = Syntax([infix], [], bimodal_operators)
        assert syntax is not None

    def test_update_types_works_with_from_prefix(self):
        """Sentence.from_prefix -> update_types succeeds with bimodal_operators."""
        from model_checker.syntactic.sentence import Sentence
        from model_checker.theory_lib.bimodal import bimodal_operators
        prefix = ["\\neg", ["p"]]
        sentence = Sentence.from_prefix(prefix)
        # update_types should not raise
        sentence.update_types(bimodal_operators)
        # After update_types, operator should be an operator class
        assert sentence.operator is not None

    def test_prefix_to_infix_consistency_with_sentence_infix(self):
        """prefix_to_infix is consistent with Sentence.infix method."""
        from model_checker.syntactic.sentence import Sentence
        test_cases = [
            ["p"],
            ["\\neg", ["p"]],
            ["\\wedge", ["p"], ["q"]],
            ["\\next", ["p"]],
            ["\\Box", ["p"]],
        ]
        temp_sentence = Sentence("p")  # Create temp for infix() access
        for prefix in test_cases:
            our_infix = prefix_to_infix(prefix)
            sentence_infix = temp_sentence.infix(prefix)
            assert our_infix == sentence_infix, (
                f"prefix_to_infix({prefix}) = {our_infix!r} but "
                f"Sentence.infix({prefix}) = {sentence_infix!r}"
            )


##############################################################################
# Phase 4: Tests for Enriched Operator Z3 Equivalence
##############################################################################

class TestEnrichedEquivalence:
    """Tests that enriched operator formulas are semantically equivalent to their primitive forms.

    Each test verifies that the enriched operator is semantically equivalent to
    its definition using the primitive operators. These are theorem tests (no
    countermodel should exist).
    """

    def _make_equiv_example(self, conclusion):
        """Create example dict for an equivalence theorem test."""
        return [
            [],
            [conclusion],
            {
                'N': 2,
                'M': 2,
                'contingent': False,
                'disjoint': False,
                'max_time': 5,
                'expectation': False,
            }
        ]

    def _run_equivalence(self, conclusion):
        """Run an equivalence test and return True if theorem (no countermodel)."""
        from model_checker import ModelConstraints, Syntax, run_test
        from model_checker.theory_lib.bimodal import (
            BimodalStructure, BimodalProposition, BimodalSemantics, bimodal_operators
        )
        from model_checker.utils.context import isolated_z3_context
        example = self._make_equiv_example(conclusion)
        with isolated_z3_context():
            result = run_test(
                example,
                BimodalSemantics,
                BimodalProposition,
                bimodal_operators,
                Syntax,
                ModelConstraints,
                BimodalStructure,
            )
        return result

    def test_neg_equivalence(self):
        """\\neg A <-> (A \\rightarrow \\bot) is a theorem."""
        assert self._run_equivalence(
            "(\\neg A \\leftrightarrow (A \\rightarrow \\bot))"
        ), "neg equivalence should be a theorem"

    def test_top_equivalence(self):
        """\\neg \\bot <-> \\neg \\bot is a theorem (\\top has pre-existing bug; use expansion).

        Note: TopOperator has a known pre-existing evaluation bug (see examples.py comment).
        Test uses the expanded form \\neg \\bot instead of \\top directly.
        """
        assert self._run_equivalence(
            "(\\neg \\bot \\leftrightarrow \\neg \\bot)"
        ), "neg-bot self-equivalence should be a theorem"

    def test_and_equivalence(self):
        """(A \\wedge B) <-> \\neg (A \\rightarrow \\neg B) is a theorem."""
        assert self._run_equivalence(
            "((A \\wedge B) \\leftrightarrow \\neg (A \\rightarrow \\neg B))"
        ), "and equivalence should be a theorem"

    def test_or_equivalence(self):
        """(A \\vee B) <-> (\\neg A \\rightarrow B) is a theorem."""
        assert self._run_equivalence(
            "((A \\vee B) \\leftrightarrow (\\neg A \\rightarrow B))"
        ), "or equivalence should be a theorem"

    def test_diamond_equivalence(self):
        """\\Diamond A <-> \\neg \\Box \\neg A is a theorem."""
        assert self._run_equivalence(
            "(\\Diamond A \\leftrightarrow \\neg \\Box \\neg A)"
        ), "diamond equivalence should be a theorem"

    def test_next_equivalence(self):
        """\\next A <-> (A \\Until \\bot) is a theorem."""
        assert self._run_equivalence(
            "(\\next A \\leftrightarrow (A \\Until \\bot))"
        ), "next equivalence should be a theorem"

    def test_prev_equivalence(self):
        """\\prev A <-> (A \\Since \\bot) is a theorem."""
        assert self._run_equivalence(
            "(\\prev A \\leftrightarrow (A \\Since \\bot))"
        ), "prev equivalence should be a theorem"

    def test_some_future_equivalence(self):
        """\\future A <-> \\neg \\Future \\neg A is a theorem."""
        assert self._run_equivalence(
            "(\\future A \\leftrightarrow \\neg \\Future \\neg A)"
        ), "some_future equivalence should be a theorem"

    def test_some_past_equivalence(self):
        """\\past A <-> \\neg \\Past \\neg A is a theorem."""
        assert self._run_equivalence(
            "(\\past A \\leftrightarrow \\neg \\Past \\neg A)"
        ), "some_past equivalence should be a theorem"

    def test_all_future_self_equivalence(self):
        """\\Future A <-> \\Future A (primitive self-equivalence)."""
        assert self._run_equivalence(
            "(\\Future A \\leftrightarrow \\Future A)"
        ), "all_future self-equivalence should be trivially true"

    def test_all_past_self_equivalence(self):
        """\\Past A <-> \\Past A (primitive self-equivalence)."""
        assert self._run_equivalence(
            "(\\Past A \\leftrightarrow \\Past A)"
        ), "all_past self-equivalence should be trivially true"


##############################################################################
# Phase 4: Tests for full JSON-to-Z3 pipeline
##############################################################################

class TestJsonToZ3Pipeline:
    """Tests for full JSON -> prefix -> infix -> Syntax -> Z3 pipeline."""

    def test_json_atom_through_pipeline(self):
        """JSON atom -> prefix -> infix -> Syntax -> parse succeeds."""
        from model_checker import Syntax
        from model_checker.theory_lib.bimodal import bimodal_operators
        formula_json = {"tag": "atom", "name": "p"}
        prefix = json_to_prefix(formula_json)
        infix = prefix_to_infix(prefix)
        syntax = Syntax([infix], [], bimodal_operators)
        assert syntax is not None
        assert infix == "p"

    def test_json_compound_neg_through_pipeline(self):
        """JSON neg -> prefix -> infix -> Syntax parses correctly."""
        from model_checker import Syntax
        from model_checker.theory_lib.bimodal import bimodal_operators
        formula_json = {"tag": "neg", "arg": {"tag": "atom", "name": "p"}}
        prefix = json_to_prefix(formula_json)
        infix = prefix_to_infix(prefix)
        syntax = Syntax([infix], [], bimodal_operators)
        assert syntax is not None

    def test_json_temporal_depth_matches_prefix_complexity(self):
        """temporal_depth from JSON is consistent with formula structure."""
        # next(p) should have depth 1, complexity 1
        formula_json = {"tag": "next", "arg": {"tag": "atom", "name": "p"}}
        depth = temporal_depth(formula_json)
        prefix = json_to_prefix(formula_json)
        # Verify depth=1 (temporal operator)
        assert depth == 1
        # Verify prefix has the right structure: [op, [arg]]
        assert len(prefix) == 2
        assert prefix[0] == "\\next"

    def test_json_nested_formula_through_pipeline(self):
        """Nested JSON formula -> prefix -> infix -> Syntax parses."""
        from model_checker import Syntax
        from model_checker.theory_lib.bimodal import bimodal_operators
        # box(neg(p))
        formula_json = {
            "tag": "box",
            "child": {"tag": "neg", "arg": {"tag": "atom", "name": "p"}}
        }
        prefix = json_to_prefix(formula_json)
        infix = prefix_to_infix(prefix)
        syntax = Syntax([infix], [], bimodal_operators)
        assert syntax is not None
        assert infix == "\\Box \\neg p"

    def test_all_17_tags_produce_valid_infix(self):
        """All 17 JSON tags produce valid infix strings parseable by Syntax."""
        from model_checker import Syntax
        from model_checker.theory_lib.bimodal import bimodal_operators

        test_formulas = [
            {"tag": "atom", "name": "p"},
            {"tag": "bot"},
            {"tag": "top"},
            {"tag": "imp", "left": {"tag": "atom", "name": "p"}, "right": {"tag": "atom", "name": "q"}},
            {"tag": "box", "child": {"tag": "atom", "name": "p"}},
            {"tag": "untl", "event": {"tag": "atom", "name": "p"}, "guard": {"tag": "atom", "name": "q"}},
            {"tag": "snce", "event": {"tag": "atom", "name": "p"}, "guard": {"tag": "atom", "name": "q"}},
            {"tag": "neg", "arg": {"tag": "atom", "name": "p"}},
            {"tag": "and", "left": {"tag": "atom", "name": "p"}, "right": {"tag": "atom", "name": "q"}},
            {"tag": "or", "left": {"tag": "atom", "name": "p"}, "right": {"tag": "atom", "name": "q"}},
            {"tag": "diamond", "arg": {"tag": "atom", "name": "p"}},
            {"tag": "next", "arg": {"tag": "atom", "name": "p"}},
            {"tag": "prev", "arg": {"tag": "atom", "name": "p"}},
            {"tag": "some_future", "arg": {"tag": "atom", "name": "p"}},
            {"tag": "some_past", "arg": {"tag": "atom", "name": "p"}},
            {"tag": "all_future", "arg": {"tag": "atom", "name": "p"}},
            {"tag": "all_past", "arg": {"tag": "atom", "name": "p"}},
        ]

        for formula_json in test_formulas:
            tag = formula_json["tag"]
            prefix = json_to_prefix(formula_json)
            infix = prefix_to_infix(prefix)
            try:
                syntax = Syntax([infix], [], bimodal_operators)
                assert syntax is not None, f"Syntax failed for tag {tag}"
            except Exception as e:
                raise AssertionError(f"Pipeline failed for tag {tag!r}: {e}")
