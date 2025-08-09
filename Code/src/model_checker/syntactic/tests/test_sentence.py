"""Tests for the Sentence class."""

import pytest
from unittest.mock import MagicMock, Mock

from model_checker.syntactic.sentence import Sentence


class TestSentenceBasics:
    """Test basic Sentence functionality."""
    
    def test_atomic_sentence(self):
        """Test creation of atomic sentences."""
        sent = Sentence("p")
        assert sent.name == "p"
        assert sent.prefix_sentence == ["p"]
        assert sent.complexity == 0
        assert sent.original_arguments is None
        assert sent.original_operator is None
        
    def test_unary_operator(self):
        """Test sentences with unary operators."""
        sent = Sentence("\\neg p")
        assert sent.name == "\\neg p"
        assert sent.prefix_sentence == ["\\neg", ["p"]]
        assert sent.complexity == 1
        assert sent.original_arguments == ["p"]
        assert sent.original_operator == "\\neg"
        
    def test_binary_operator(self):
        """Test sentences with binary operators."""
        sent = Sentence("(p \\wedge q)")
        assert sent.name == "(p \\wedge q)"
        assert sent.prefix_sentence == ["\\wedge", ["p"], ["q"]]
        assert sent.complexity == 1
        assert sent.original_arguments == ["p", "q"]
        assert sent.original_operator == "\\wedge"
        
    def test_nested_sentence(self):
        """Test nested complex sentences."""
        sent = Sentence("((p \\wedge q) \\rightarrow r)")
        assert sent.name == "((p \\wedge q) \\rightarrow r)"
        assert sent.prefix_sentence == ["\\rightarrow", ["\\wedge", ["p"], ["q"]], ["r"]]
        assert sent.complexity == 2
        assert sent.original_arguments == ["(p \\wedge q)", "r"]
        assert sent.original_operator == "\\rightarrow"
        
    def test_str_repr(self):
        """Test string representation."""
        sent = Sentence("(p \\vee q)")
        assert str(sent) == "(p \\vee q)"
        assert repr(sent) == "(p \\vee q)"


class TestPrefixInfixConversion:
    """Test conversion between prefix and infix notation."""
    
    def test_prefix_atomic(self):
        """Test prefix conversion for atomic sentences."""
        sent = Sentence("A")
        prefix, complexity = sent.prefix("A")
        assert prefix == ["A"]
        assert complexity == 0
        
    def test_prefix_unary(self):
        """Test prefix conversion for unary operators."""
        sent = Sentence("\\Box A")
        prefix, complexity = sent.prefix("\\Box A")
        assert prefix == ["\\Box", ["A"]]
        assert complexity == 1
        
    def test_prefix_binary(self):
        """Test prefix conversion for binary operators."""
        sent = Sentence("(A \\wedge B)")
        prefix, complexity = sent.prefix("(A \\wedge B)")
        assert prefix == ["\\wedge", ["A"], ["B"]]
        assert complexity == 1
        
    def test_infix_string(self):
        """Test infix conversion with string input."""
        sent = Sentence("p")
        assert sent.infix("p") == "p"
        
    def test_infix_list_atomic(self):
        """Test infix conversion with single-element list."""
        sent = Sentence("p")
        assert sent.infix(["p"]) == "p"
        
    def test_infix_list_unary(self):
        """Test infix conversion with unary operator."""
        sent = Sentence("\\neg p")
        assert sent.infix(["\\neg", "p"]) == "\\neg p"
        
    def test_infix_list_binary(self):
        """Test infix conversion with binary operator."""
        sent = Sentence("(p \\wedge q)")
        assert sent.infix(["\\wedge", "p", "q"]) == "(p \\wedge q)"
        
    def test_infix_nested(self):
        """Test infix conversion with nested structure."""
        sent = Sentence("((p \\wedge q) \\vee r)")
        prefix = ["\\vee", ["\\wedge", "p", "q"], "r"]
        assert sent.infix(prefix) == "((p \\wedge q) \\vee r)"
        
    def test_infix_sentence_object(self):
        """Test infix conversion with Sentence object."""
        sent1 = Sentence("p")
        sent2 = Sentence("q")
        assert sent1.infix(sent2) == "q"
        
    def test_infix_type_error(self):
        """Test that infix raises TypeError for unsupported types."""
        sent = Sentence("p")
        with pytest.raises(TypeError):
            sent.infix(42)  # Numbers not supported


class TestSpecialOperators:
    """Test handling of special operators like \\top and \\bot."""
    
    def test_top_operator(self):
        """Test \\top (tautology) operator."""
        sent = Sentence("\\top")
        assert sent.name == "\\top"
        assert sent.prefix_sentence == ["\\top"]
        assert sent.complexity == 0
        assert sent.original_operator == "\\top"
        assert sent.original_arguments is None
        
    def test_bot_operator(self):
        """Test \\bot (contradiction) operator."""
        sent = Sentence("\\bot")
        assert sent.name == "\\bot"
        assert sent.prefix_sentence == ["\\bot"]
        assert sent.complexity == 0
        assert sent.original_operator == "\\bot"
        assert sent.original_arguments is None


class TestUpdateMethods:
    """Test the various update methods."""
    
    def test_update_types_atomic(self):
        """Test update_types for atomic sentences."""
        sent = Sentence("p")
        
        # Mock operator collection
        mock_collection = MagicMock()
        mock_atom = MagicMock()
        mock_collection.apply_operator.return_value = [mock_atom]
        
        sent.update_types(mock_collection)
        
        assert sent.sentence_letter == mock_atom
        assert sent.operator is None
        assert sent.arguments is None
        
    def test_update_types_operator(self):
        """Test update_types for operator sentences."""
        sent = Sentence("(p \\wedge q)")
        
        # Mock operator collection and operator class
        mock_collection = MagicMock()
        mock_op_class = MagicMock()
        mock_op_class.primitive = True
        mock_atom1 = MagicMock()
        mock_atom2 = MagicMock()
        # Set up the name attribute so infix() returns the correct value
        mock_atom1.name = "p"
        mock_atom2.name = "q"
        
        mock_collection.apply_operator.return_value = [mock_op_class, mock_atom1, mock_atom2]
        
        sent.update_types(mock_collection)
        
        assert sent.original_operator == mock_op_class
        assert sent.operator == mock_op_class
        assert sent.arguments == ["p", "q"]
        assert sent.sentence_letter is None
        
    def test_update_objects(self):
        """Test update_objects method."""
        sent = Sentence("(p \\wedge q)")
        
        # Set up sentence with mock operator
        mock_op_class = MagicMock()
        mock_op_class.name = "wedge"
        sent.original_operator = mock_op_class
        sent.operator = mock_op_class
        
        # Mock model constraints
        mock_constraints = MagicMock()
        mock_op_instance = MagicMock()
        mock_constraints.operators = {"wedge": mock_op_instance}
        
        sent.update_objects(mock_constraints)
        
        assert sent.original_operator == mock_op_instance
        assert sent.operator == mock_op_instance
        
    def test_update_proposition(self):
        """Test update_proposition method."""
        sent = Sentence("p")
        
        # Mock model structure and proposition class
        mock_structure = MagicMock()
        mock_prop_class = MagicMock()
        mock_prop_instance = MagicMock()
        mock_prop_class.return_value = mock_prop_instance
        mock_structure.proposition_class = mock_prop_class
        
        sent.update_proposition(mock_structure)
        
        assert sent.proposition == mock_prop_instance
        mock_prop_class.assert_called_once_with(sent, mock_structure)