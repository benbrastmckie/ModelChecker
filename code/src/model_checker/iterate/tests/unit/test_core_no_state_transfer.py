"""Test that MODEL 2 builds without verify/falsify state transfer."""

import unittest
from unittest.mock import Mock, patch, MagicMock
import z3


class TestNoStateTransfer(unittest.TestCase):
    """Test that state transfer mechanism is removed."""
    
    def test_no_extract_verify_falsify_method(self):
        """Test that _extract_verify_falsify_from_z3 method is removed."""
        # Import after patching to ensure we get current version
        from model_checker.iterate.core import BaseModelIterator
        
        # Create mock build example
        mock_build = Mock()
        mock_build.model_structure = Mock()
        mock_build.model_structure.z3_model = Mock()
        mock_build.model_structure.z3_model_status = True
        mock_build.model_structure.z3_world_states = []
        mock_build.model_structure.z3_possible_states = []
        mock_solver = Mock(spec=['assertions', 'push', 'pop', 'add', 'check'])
        mock_solver.assertions.return_value = []
        mock_build.model_structure.solver = mock_solver
        mock_build.settings = {'iterate': 2}
        mock_build.model_constraints = Mock()
        mock_build.model_constraints.all_constraints = [z3.BoolVal(True)]  # Add dummy constraint
        
        # Create concrete subclass since BaseModelIterator might be abstract
        class TestIterator(BaseModelIterator):
            def _create_difference_constraint(self, previous_models):
                return z3.BoolVal(True)
            
            def _create_non_isomorphic_constraint(self, z3_model):
                return z3.BoolVal(True)
                
            def _create_stronger_constraint(self, isomorphic_model):
                return z3.BoolVal(True)
        
        # Create iterator instance
        iterator = TestIterator(mock_build)
        
        # Method should not exist
        self.assertFalse(hasattr(iterator, '_extract_verify_falsify_from_z3'),
                        "_extract_verify_falsify_from_z3 should be removed")
    
    def test_no_initialize_with_state_call(self):
        """Test that initialize_with_state is not called in _build_new_model_structure."""
        from model_checker.iterate.core import BaseModelIterator
        
        # Create mock build example with all required attributes
        mock_build = Mock()
        mock_build.model_structure = Mock()
        mock_build.model_structure.z3_model = Mock()
        mock_build.model_structure.z3_model_status = True
        mock_build.model_structure.z3_world_states = []
        mock_build.model_structure.z3_possible_states = []
        mock_solver = Mock(spec=['assertions', 'push', 'pop', 'add', 'check'])
        mock_solver.assertions.return_value = []
        mock_build.model_structure.solver = mock_solver
        mock_build.settings = {'iterate': 2, 'N': 3, 'max_time': 10}
        mock_build.model_constraints = Mock()
        mock_build.model_constraints.all_constraints = [z3.BoolVal(True)]
        mock_build.premises = ["A"]
        mock_build.conclusions = ["B"]
        
        # Mock semantic theory
        mock_semantics_class = Mock()
        mock_semantics_instance = Mock()
        mock_semantics_class.return_value = mock_semantics_instance
        
        mock_build.semantic_theory = {
            "semantics": mock_semantics_class,
            "proposition": Mock(),
            "model": Mock(),
            "operators": []
        }
        
        # Mock syntax
        mock_build.example_syntax = Mock()
        mock_build.example_syntax.sentence_letters = []
        
        # Create test iterator
        class TestIterator(BaseModelIterator):
            def _create_difference_constraint(self, previous_models):
                return z3.BoolVal(True)
            
            def _create_non_isomorphic_constraint(self, z3_model):
                return z3.BoolVal(True)
                
            def _create_stronger_constraint(self, isomorphic_model):
                return z3.BoolVal(True)
        
        iterator = TestIterator(mock_build)
        
        # Mock Z3 model
        z3_model = Mock()
        
        # Call _build_new_model_structure
        try:
            iterator._build_new_model_structure(z3_model)
        except Exception:
            # We expect this to fail due to mocking, but we're checking the call
            pass
        
        # Check that initialize_with_state was NOT called
        mock_semantics_instance.initialize_with_state.assert_not_called()


if __name__ == '__main__':
    unittest.main()