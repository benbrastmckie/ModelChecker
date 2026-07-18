"""Unit tests for formulas module - WFF checking.

Tests the is_syntactically_wff() function from the formulas module.
"""

import pytest
from model_checker.syntactic.formulas import is_syntactically_wff


class TestIsSyntacticallyWff:
    """Tests for is_syntactically_wff function."""

    # --- Valid formulas ---

    def test_atomic_sentence_letter_is_wff(self):
        """Atomic sentence letter 'P' is a WFF."""
        prefix = ['P']
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True
        assert msg == ""

    def test_top_is_wff(self):
        """\\top is a WFF."""
        prefix = ['\\top']
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_bot_is_wff(self):
        """\\bot is a WFF."""
        prefix = ['\\bot']
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_negation_is_wff(self):
        """\\neg phi is a WFF."""
        prefix = ['\\neg', ['P']]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_conjunction_is_wff(self):
        """phi \\wedge psi is a WFF."""
        prefix = ['\\wedge', ['P'], ['Q']]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_disjunction_is_wff(self):
        """phi \\vee psi is a WFF."""
        prefix = ['\\vee', ['P'], ['Q']]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_implication_is_wff(self):
        """phi \\rightarrow psi is a WFF."""
        prefix = ['\\rightarrow', ['P'], ['Q']]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_equivalence_is_wff(self):
        """phi \\equiv psi is a WFF."""
        prefix = ['\\equiv', ['P'], ['Q']]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    def test_other_backslash_operator_is_wff(self):
        """Modal-style operators (e.g. \\Box) are accepted as WFFs."""
        prefix = ['\\Box', ['P']]
        is_wff, msg = is_syntactically_wff(prefix)
        assert is_wff is True

    # --- Edge cases ---

    def test_empty_list_is_not_wff(self):
        """Empty list is not a WFF."""
        is_wff, msg = is_syntactically_wff([])
        assert is_wff is False
        assert "empty" in msg.lower()

    def test_non_list_is_not_wff(self):
        """Non-list input is not a WFF."""
        is_wff, msg = is_syntactically_wff("P")
        assert is_wff is False
        assert "expected list" in msg.lower()
