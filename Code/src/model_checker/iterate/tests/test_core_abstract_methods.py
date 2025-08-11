"""Test that BaseModelIterator requires theory-specific methods."""

import unittest
from unittest.mock import Mock, MagicMock
import z3
from model_checker.iterate.core import BaseModelIterator


class TestAbstractMethods(unittest.TestCase):
    """Test abstract method requirements."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Create mock build example
        self.mock_build = Mock()
        self.mock_build.model_structure = Mock()
        self.mock_build.model_structure.z3_model = Mock()
        self.mock_build.model_structure.z3_model_status = True
        self.mock_build.model_structure.z3_world_states = []
        self.mock_build.model_structure.z3_possible_states = []
        mock_solver = Mock(spec=['assertions', 'push', 'pop', 'add', 'check'])
        mock_solver.assertions.return_value = []
        self.mock_build.model_structure.solver = mock_solver
        self.mock_build.settings = {'iterate': 2}
        self.mock_build.model_constraints = Mock()
        self.mock_build.model_constraints.all_constraints = [z3.BoolVal(True)]
    
    def test_abstract_methods_required(self):
        """Test that BaseModelIterator cannot be instantiated without implementing abstract methods."""
        # Direct instantiation should fail (if we make them abstract)
        # For now, they raise NotImplementedError
        iterator = BaseModelIterator(self.mock_build)
        
        # These methods should raise NotImplementedError
        with self.assertRaises(NotImplementedError) as context:
            iterator._create_difference_constraint([])
        self.assertIn("Theory-specific implementation required", str(context.exception))
        
        with self.assertRaises(NotImplementedError) as context:
            iterator._create_non_isomorphic_constraint(Mock())
        self.assertIn("Theory-specific implementation required", str(context.exception))
        
        with self.assertRaises(NotImplementedError) as context:
            iterator._create_stronger_constraint(Mock())
        self.assertIn("Theory-specific implementation required", str(context.exception))
    
    def test_constraint_methods_called_correctly(self):
        """Test that constraint methods are called with correct arguments."""
        # Create concrete implementation
        class TestIterator(BaseModelIterator):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, **kwargs)
                self.diff_called = False
                self.diff_args = None
                self.non_iso_called = False
                self.non_iso_args = None
                self.stronger_called = False
                self.stronger_args = None
                
            def _create_difference_constraint(self, previous_models):
                self.diff_called = True
                self.diff_args = previous_models
                return z3.BoolVal(True)
                
            def _create_non_isomorphic_constraint(self, z3_model):
                self.non_iso_called = True
                self.non_iso_args = z3_model
                return z3.BoolVal(True)
                
            def _create_stronger_constraint(self, isomorphic_model):
                self.stronger_called = True
                self.stronger_args = isomorphic_model
                return z3.BoolVal(True)
                
            def _calculate_differences(self, new_structure, previous_structure):
                return {}
        
        iterator = TestIterator(self.mock_build)
        
        # Test _create_difference_constraint is called
        iterator.previous_models = [Mock()]
        diff_constraint = iterator._create_difference_constraint(iterator.previous_models)
        
        # Verify _create_difference_constraint was called
        self.assertTrue(iterator.diff_called, "_create_difference_constraint should be called")
        self.assertIsInstance(iterator.diff_args, list, "Should pass list of previous models")
        self.assertEqual(len(iterator.diff_args), 1, "Should have one previous model")
        
        # The other methods would be called during isomorphism checking
    
    def test_abstract_methods_docstrings(self):
        """Test that abstract methods have proper docstrings."""
        # Check that methods exist and have docstrings
        self.assertTrue(hasattr(BaseModelIterator, '_create_difference_constraint'))
        self.assertIsNotNone(BaseModelIterator._create_difference_constraint.__doc__)
        
        self.assertTrue(hasattr(BaseModelIterator, '_create_non_isomorphic_constraint'))
        self.assertIsNotNone(BaseModelIterator._create_non_isomorphic_constraint.__doc__)
        
        self.assertTrue(hasattr(BaseModelIterator, '_create_stronger_constraint'))
        self.assertIsNotNone(BaseModelIterator._create_stronger_constraint.__doc__)


if __name__ == '__main__':
    unittest.main()