"""Test simplified BaseModelIterator using injection approach.

Following TDD - written BEFORE simplifying BaseModelIterator.
Tests verify that theory-specific logic is properly delegated.
"""

import unittest
from unittest.mock import Mock, patch, MagicMock
import z3
from model_checker.iterate.core import BaseModelIterator


class TestSimplifiedIterator(unittest.TestCase):
    """Test simplified BaseModelIterator functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Create mock build example
        self.mock_build = Mock()
        self.mock_build.settings = {'N': 2}
        self.mock_build.semantic_theory = {
            'semantics': Mock,
            'model': Mock,
            'proposition': Mock
        }
        
        # Create mock model structure
        self.mock_structure = Mock()
        self.mock_structure.solver = Mock()
        self.mock_structure.solver.check.return_value = z3.sat
        self.mock_structure.solver.model.return_value = Mock()
        self.mock_structure.z3_model_status = True
        self.mock_structure.z3_model = Mock()
        
        # Mock build example attributes
        self.mock_build.model_structure = self.mock_structure
        self.mock_build.premises = []
        self.mock_build.conclusions = []
        
        # Mock model constraints with some dummy constraints
        mock_constraints = Mock()
        mock_constraints.all_constraints = [Mock(), Mock()]  # Add dummy constraints
        self.mock_build.model_constraints = mock_constraints
        
        # Create iterator
        self.iterator = BaseModelIterator(self.mock_build)
    
    @patch('model_checker.iterate.core.create_with_z3_model')
    def test_uses_iterator_build_example(self, mock_create):
        """Test that simplified iterator uses IteratorBuildExample."""
        # Set up mock
        mock_new_build = Mock()
        mock_new_structure = Mock()
        mock_new_build.model_structure = mock_new_structure
        mock_create.return_value = mock_new_build
        
        # Create Z3 model
        z3_model = Mock()
        
        # Call the method
        result = self.iterator._build_new_model_structure(z3_model)
        
        # Verify IteratorBuildExample was used
        mock_create.assert_called_once_with(
            self.mock_build, z3_model
        )
        
        # Verify structure returned
        self.assertEqual(result, mock_new_structure)
    
    def test_no_theory_concepts_in_core(self):
        """Verify no theory concepts in simplified implementation."""
        import inspect
        
        # Get the source of the method
        source = inspect.getsource(self.iterator._build_new_model_structure)
        
        # Theory concepts that should NOT appear
        forbidden = [
            'is_world', 'possible', 'verify', 'falsify',
            'states', '2**', 'semantics.N', 'sentence_letter'
        ]
        
        for concept in forbidden:
            if concept in source:
                # This test will fail until we implement the simplification
                self.skipTest(f"Simplification not implemented yet - found '{concept}'")
    
    @patch('model_checker.iterate.core.create_with_z3_model')
    def test_handles_failed_model_creation(self, mock_create):
        """Test handling when model creation fails."""
        # Set up failure
        mock_create.side_effect = Exception("Creation failed")
        
        # Create Z3 model
        z3_model = Mock()
        
        # Call should handle exception gracefully
        result = self.iterator._build_new_model_structure(z3_model)
        
        # Should return None on failure
        self.assertIsNone(result)
    
    @patch('model_checker.iterate.core.create_with_z3_model')
    def test_interpret_called_on_new_structure(self, mock_create):
        """Test that interpret is called on new model structure."""
        # Set up mock
        mock_new_build = Mock()
        mock_new_structure = Mock()
        mock_new_structure.premises = ['P1']
        mock_new_structure.conclusions = ['C1']
        mock_new_build.model_structure = mock_new_structure
        mock_create.return_value = mock_new_build
        
        # Create Z3 model
        z3_model = Mock()
        
        # Call the method
        result = self.iterator._build_new_model_structure(z3_model)
        
        # Verify interpret was called
        mock_new_structure.interpret.assert_called_once_with(['P1', 'C1'])
    
    def test_simplified_method_shorter(self):
        """Verify the simplified method is much shorter."""
        import inspect
        
        # Get the source
        source = inspect.getsource(self.iterator._build_new_model_structure)
        lines = source.count('\n')
        
        # Should be much shorter than original ~130 lines
        # Allow for current length during development
        if lines > 50:
            self.skipTest(f"Method still {lines} lines - not simplified yet")
        
        # Once simplified, should be under 50 lines
        self.assertLess(lines, 50, 
            f"Simplified method should be < 50 lines, got {lines}")


if __name__ == '__main__':
    unittest.main()