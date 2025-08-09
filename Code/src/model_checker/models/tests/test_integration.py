"""Integration tests for models package.

Tests that verify all components work together correctly after refactoring.
"""

import unittest
from unittest.mock import Mock
import pytest

from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.constraints import ModelConstraints


class TestModelsIntegration(unittest.TestCase):
    """Test that refactored components integrate correctly."""
    
    def test_imports_work_correctly(self):
        """Test that imports from models package work correctly."""
        # SemanticDefaults should be importable
        self.assertIsNotNone(SemanticDefaults)
        
        # PropositionDefaults should be importable
        self.assertIsNotNone(PropositionDefaults)
        
        # ModelConstraints should be importable
        self.assertIsNotNone(ModelConstraints)
    
    def test_inheritance_works_correctly(self):
        """Test that inheritance from refactored classes works."""
        # Create a concrete proposition subclass
        class TestProposition(PropositionDefaults):
            pass
        
        # Create a concrete semantics subclass
        class TestSemantics(SemanticDefaults):
            pass
        
        # Verify they can be instantiated with proper arguments
        mock_sentence = Mock()
        mock_sentence.name = "A"
        mock_sentence.is_atom = True
        mock_sentence.operator = None
        mock_sentence.arguments = None
        mock_sentence.sentence_letter = Mock()
        
        mock_model = Mock()
        mock_model.semantics = Mock()
        mock_model.semantics.N = 3
        mock_model.semantics.main_point = {}
        mock_model.model_constraints = Mock()
        mock_model.model_constraints.settings = {'N': 3}
        mock_model.model_constraints.sentence_letters = []
        
        # Should not raise
        prop = TestProposition(mock_sentence, mock_model)
        self.assertIsInstance(prop, PropositionDefaults)
        
        # Test semantics
        settings = {'N': 3}
        sem = TestSemantics(settings)
        self.assertIsInstance(sem, SemanticDefaults)
    
    def test_cross_component_interaction(self):
        """Test that components can interact correctly."""
        # Create semantics instance
        settings = {'N': 3}
        semantics = SemanticDefaults(settings)
        
        # Create mock model structure that uses the semantics
        mock_model = Mock()
        mock_model.semantics = semantics
        mock_model.semantics.main_point = {}
        mock_model.model_constraints = Mock()
        mock_model.model_constraints.settings = settings
        mock_model.model_constraints.sentence_letters = []
        mock_model.model_constraints.semantics = semantics
        
        # Create concrete proposition class
        class TestProp(PropositionDefaults):
            pass
        
        mock_sentence = Mock()
        mock_sentence.name = "Test"
        mock_sentence.is_atom = True
        mock_sentence.operator = None
        mock_sentence.arguments = None
        mock_sentence.sentence_letter = None
        
        # Should work together
        prop = TestProp(mock_sentence, mock_model)
        self.assertEqual(prop.N, 3)
        self.assertEqual(prop.semantics.N, 3)


if __name__ == '__main__':
    unittest.main()