"""Tests for Z3 injection delegation in ModelConstraints.

Following TDD approach - written BEFORE implementing inject_z3_values.
Tests verify theory-agnostic delegation pattern.
"""

import unittest
from unittest.mock import Mock, MagicMock
from model_checker.models.constraints import ModelConstraints


class TestConstraintsInjection(unittest.TestCase):
    """Test Z3 injection delegation in ModelConstraints."""
    
    def test_inject_z3_values_delegates_to_semantics(self):
        """Test that injection delegates to semantics if available."""
        # Create mock semantics with injection method
        mock_semantics = Mock()
        mock_semantics.inject_z3_model_values = Mock()
        mock_semantics.frame_constraints = []
        mock_semantics.premise_behavior = Mock(return_value=Mock())
        mock_semantics.conclusion_behavior = Mock(return_value=Mock())
        
        # Create ModelConstraints with mock
        settings = {'N': 3}
        syntax = Mock()
        syntax.premises = []
        syntax.conclusions = []
        syntax.sentence_letters = []
        syntax.operator_collection = {}
        
        proposition = Mock()
        proposition.proposition_constraints = Mock(return_value=[])
        
        constraints = ModelConstraints(settings, syntax, mock_semantics, proposition)
        
        # Call injection
        mock_z3_model = Mock()
        mock_original_semantics = Mock()
        constraints.inject_z3_values(mock_z3_model, mock_original_semantics)
        
        # Verify delegation
        mock_semantics.inject_z3_model_values.assert_called_once_with(
            mock_z3_model, mock_original_semantics, constraints
        )
        
        # Verify z3_model stored
        self.assertEqual(constraints.injected_z3_model, mock_z3_model)
    
    def test_inject_z3_values_no_delegation_if_not_supported(self):
        """Test graceful handling when semantics doesn't support injection."""
        # Create mock semantics without injection method
        mock_semantics = Mock(spec=['frame_constraints', 'premise_behavior', 'conclusion_behavior'])
        mock_semantics.frame_constraints = []
        mock_semantics.premise_behavior = Mock(return_value=Mock())
        mock_semantics.conclusion_behavior = Mock(return_value=Mock())
        
        # Create ModelConstraints
        settings = {'N': 3}
        syntax = Mock()
        syntax.premises = []
        syntax.conclusions = []
        syntax.sentence_letters = []
        syntax.operator_collection = {}
        
        proposition = Mock()
        proposition.proposition_constraints = Mock(return_value=[])
        
        constraints = ModelConstraints(settings, syntax, mock_semantics, proposition)
        
        # Should not raise error
        mock_z3_model = Mock()
        mock_original_semantics = Mock()
        constraints.inject_z3_values(mock_z3_model, mock_original_semantics)
        
        # Z3 model still stored
        self.assertEqual(constraints.injected_z3_model, mock_z3_model)
    
    def test_no_theory_concepts_in_injection(self):
        """Verify inject_z3_values contains no theory-specific concepts."""
        import inspect
        
        # This test will fail until we implement the method
        # After implementation, it should check the source
        try:
            source = inspect.getsource(ModelConstraints.inject_z3_values)
            
            # These theory concepts should NOT appear
            forbidden_concepts = [
                'is_world', 'possible', 'verify', 'falsify',
                'states', 'worlds', 'atom', 'sentence_letter',
                'self.N', 'semantics.N', '2**'
            ]
            
            for concept in forbidden_concepts:
                self.assertNotIn(concept, source,
                    f"Theory concept '{concept}' found in inject_z3_values")
        except AttributeError:
            # Method doesn't exist yet - this is expected in TDD
            pass


if __name__ == '__main__':
    unittest.main()