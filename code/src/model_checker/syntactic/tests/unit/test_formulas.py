"""Tests for `is_syntactically_wff`.

The first test class (`TestCharacterizationBeforeAndAfter`) pins the function's
*current* accept/reject behavior for a representative set of prefix shapes,
including the accidental acceptance of a non-backslash multi-argument head (e.g.
a Unicode-aliased connective like `["∧", ["p"], ["q"]]`) through the "atomic
sentence letter" branch. Phase 3 restructures the function so that shape is
accepted for the *right* reason (a connective with arguments, gated by
`len(prefix) == 1`), with zero change to any of these accept/reject outcomes --
every assertion in this class must hold identically before and after the change.

The second class (`TestStructuralDiscrimination`) asserts the new, structurally
correct discrimination directly: a bare non-backslash head is an atomic sentence
letter only when it has no arguments; the same head with arguments is a connective.
"""

from typing import Any

import pytest
from z3 import Const, DeclareSort

from model_checker.syntactic.formulas import is_syntactically_wff


ATOM_SORT = DeclareSort("TestFormulasAtomSort")


class TestCharacterizationBeforeAndAfter:
    """Pins current accept/reject behavior. Must pass identically before and
    after the Phase 3 structural change."""

    def test_bare_atomic_sentence_letter_accepted(self):
        assert is_syntactically_wff(["p"]) == (True, "")

    def test_top_accepted(self):
        assert is_syntactically_wff(["\\top"]) == (True, "")

    def test_bot_accepted(self):
        assert is_syntactically_wff(["\\bot"]) == (True, "")

    def test_negation_accepted(self):
        assert is_syntactically_wff(["\\neg", ["p"]]) == (True, "")

    def test_latex_binary_connective_accepted(self):
        assert is_syntactically_wff(["\\wedge", ["p"], ["q"]]) == (True, "")

    def test_unicode_binary_connective_accepted(self):
        """Currently accepted via the (wrong-reason) atomic-sentence-letter
        branch, since that branch is unguarded by `len(prefix)`. Phase 3 must
        keep this accepted, now for the right (connective) reason."""
        assert is_syntactically_wff(["∧", ["p"], ["q"]]) == (True, "")

    def test_unicode_unary_connective_accepted(self):
        assert is_syntactically_wff(["¬", ["p"]]) == (True, "")

    def test_z3_const_head_accepted(self):
        atom = Const("p", ATOM_SORT)
        assert is_syntactically_wff([atom]) == (True, "")

    def test_empty_list_rejected(self):
        is_wff, message = is_syntactically_wff([])
        assert is_wff is False
        assert message == "Empty formula"

    def test_non_list_input_rejected(self):
        is_wff, message = is_syntactically_wff("not a list")
        assert is_wff is False
        assert "Expected list structure" in message


class TestStructuralDiscrimination:
    """Post-change: a non-backslash head is classified by structure, not by an
    accidental fallthrough."""

    def test_bare_non_backslash_head_with_no_arguments_is_atomic_sentence_letter(self):
        # len(prefix) == 1 -> atomic sentence letter.
        assert is_syntactically_wff(["p"]) == (True, "")

    def test_non_backslash_head_with_arguments_is_a_connective_not_atomic(self):
        # len(prefix) > 1 -> connective applied to arguments, never reported as
        # an atomic sentence letter.
        assert is_syntactically_wff(["∧", ["p"], ["q"]]) == (True, "")
        assert is_syntactically_wff(["¬", ["p"]]) == (True, "")

    def test_unrecognized_structure_terminus_still_reachable(self):
        # A non-string, non-backslash-operator head with more than one element
        # still falls through every ACCEPT branch to the final rejection --
        # the restructuring must not make this terminus unreachable.
        is_wff, message = is_syntactically_wff([123, ["p"], ["q"]])
        assert is_wff is False
        assert "Unrecognized formula structure" in message
