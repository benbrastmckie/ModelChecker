"""Tests for proposition.py module.

Tests for PropositionDefaults class functionality following TDD approach.
"""

import unittest
from unittest.mock import Mock
import pytest

from model_checker.models.proposition import PropositionDefaults


class TestPropositionDefaults(unittest.TestCase):
    """Test PropositionDefaults class functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Create mock objects
        self.mock_sentence = Mock()
        self.mock_sentence.name = "A"
        self.mock_sentence.is_atom = True
        self.mock_sentence.operator = None
        self.mock_sentence.arguments = None
        
        self.mock_model_structure = Mock()
        self.mock_model_structure.semantics = Mock()
        self.mock_model_structure.semantics.N = 3
        self.mock_model_structure.semantics.main_point = {'w': 0}
        self.mock_model_structure.model_constraints = Mock()
        self.mock_model_structure.model_constraints.settings = {'N': 3}
        self.mock_model_structure.model_constraints.sentence_letters = ['A', 'B']
    
    def test_cannot_instantiate_base_class(self):
        """Test that PropositionDefaults cannot be instantiated directly."""
        with self.assertRaises(NotImplementedError) as context:
            PropositionDefaults(self.mock_sentence, self.mock_model_structure)
        
        self.assertIn("PropositionDefaults", str(context.exception))
    
    def test_validates_model_structure(self):
        """Test that initialization validates model_structure has semantics."""
        # Create a concrete subclass for testing
        class ConcreteProposition(PropositionDefaults):
            pass
        
        # Test with invalid model_structure (no semantics attribute)
        invalid_model = Mock(spec=[])  # No semantics attribute
        
        with self.assertRaises(TypeError) as context:
            ConcreteProposition(self.mock_sentence, invalid_model)
        
        self.assertIn("ModelStructure object", str(context.exception))
    
    def test_initialization_with_valid_inputs(self):
        """Test that a concrete subclass initializes correctly."""
        # Create a concrete subclass
        class ConcreteProposition(PropositionDefaults):
            pass
        
        # Should initialize without error
        prop = ConcreteProposition(self.mock_sentence, self.mock_model_structure)
        
        # Verify attributes are set
        self.assertEqual(prop.sentence, self.mock_sentence)
        self.assertEqual(prop.model_structure, self.mock_model_structure)
        self.assertEqual(prop.N, 3)
        self.assertEqual(prop.name, "A")
        self.assertIsNone(prop.operator)
        self.assertIsNone(prop.arguments)
    
    def test_hash_and_equality(self):
        """Test that propositions can be hashed and compared."""
        class ConcreteProposition(PropositionDefaults):
            pass
        
        prop1 = ConcreteProposition(self.mock_sentence, self.mock_model_structure)
        prop2 = ConcreteProposition(self.mock_sentence, self.mock_model_structure)
        
        # Different objects with same sentence should be equal
        self.assertEqual(prop1, prop2)
        self.assertEqual(hash(prop1), hash(prop2))
        
        # Can be used in sets
        prop_set = {prop1, prop2}
        self.assertEqual(len(prop_set), 1)
    
    def test_complex_sentence_initialization(self):
        """Test initialization with complex (non-atomic) sentence."""
        class ConcreteProposition(PropositionDefaults):
            pass
        
        # Create mock complex sentence
        complex_sentence = Mock()
        complex_sentence.name = "(A \\wedge B)"
        complex_sentence.is_atom = False
        complex_sentence.operator = Mock(name="wedge")
        complex_sentence.arguments = [Mock(name="A"), Mock(name="B")]
        complex_sentence.sentence_letter = None  # Complex sentences don't have sentence_letter
        
        prop = ConcreteProposition(complex_sentence, self.mock_model_structure)
        
        # Verify complex sentence attributes
        self.assertFalse(prop.sentence.is_atom)
        self.assertIsNotNone(prop.operator)
        self.assertIsNotNone(prop.arguments)
        self.assertIsNone(prop.sentence_letter)  # Should be None for complex sentences


class TestPropositionColorFormatting(unittest.TestCase):
    """Test color formatting functionality."""
    
    def test_set_colors_method(self):
        """Test the set_colors method for output formatting."""
        class ConcreteProposition(PropositionDefaults):
            pass
        
        mock_sentence = Mock()
        mock_sentence.name = "A"
        mock_model = Mock()
        mock_model.semantics = Mock()
        mock_model.semantics.N = 3
        mock_model.semantics.main_point = {}
        mock_model.model_constraints = Mock()
        mock_model.model_constraints.settings = {}
        mock_model.model_constraints.sentence_letters = []
        
        prop = ConcreteProposition(mock_sentence, mock_model)
        
        # Test color setting (should not raise exceptions)
        prop.set_colors("A", indent_num=0, truth_value=True, 
                       world_state="000", use_colors=True)
        
        # Verify attributes exist after color setting
        self.assertTrue(hasattr(prop, 'color_name'))
        self.assertTrue(hasattr(prop, 'color_truth_value'))


if __name__ == '__main__':
    unittest.main()