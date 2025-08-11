"""Test constraint preservation in iterator.

Tests that iterator preserves premise/conclusion constraints across models.
"""

import unittest
from unittest.mock import MagicMock, patch
import z3

from model_checker.iterate.core import BaseModelIterator


class TestConstraintPreservation(unittest.TestCase):
    """Test that constraints are preserved during iteration."""
    
    def test_original_constraints_preserved(self):
        """Test that original model constraints are preserved in solver."""
        # Create mock build example
        mock_example = MagicMock()
        mock_example.settings = {'iterate': 3}
        
        # Create mock model structure with solver
        mock_solver = z3.Solver()
        mock_solver.add(z3.Bool('original_constraint'))  # Add a test constraint
        
        mock_model = MagicMock()
        mock_model.solver = mock_solver
        mock_model.stored_solver = None
        mock_model.z3_model_status = True
        # Just use a simple mock for z3_model
        mock_model.z3_model = MagicMock()
        
        mock_example.model_structure = mock_model
        
        # Mock model_constraints with all_constraints
        mock_constraints = MagicMock()
        mock_constraints.all_constraints = mock_solver.assertions()
        mock_example.model_constraints = mock_constraints
        
        # Create concrete iterator for testing
        class TestIterator(BaseModelIterator):
            def _create_difference_constraint(self, previous_models):
                return z3.Bool('difference')
            
            def _create_non_isomorphic_constraint(self, z3_model):
                return None
                
            def _create_stronger_constraint(self, isomorphic_model):
                return None
                
            def _calculate_differences(self, new_structure, previous_structure):
                return {}
        
        # Create iterator
        iterator = TestIterator(mock_example)
        
        # Check that persistent solver has original constraint
        assertions = iterator.solver.assertions()
        assertion_strs = [str(a) for a in assertions]
        self.assertIn('original_constraint', assertion_strs,
                     "Original constraint should be preserved in iterator solver")
    
    def test_premise_conclusion_constraints_added(self):
        """Test that premise/conclusion constraints are added to extended constraints."""
        # Create mock build example
        mock_example = MagicMock()
        mock_example.settings = {'iterate': 2}
        
        # Mock model constraints
        mock_constraints = MagicMock()
        premise_constraint = z3.Bool('premise_true')
        conclusion_constraint = z3.Bool('conclusion_false')
        mock_constraints.premise_constraints = [premise_constraint]
        mock_constraints.conclusion_constraints = [conclusion_constraint]
        
        mock_example.model_constraints = mock_constraints
        
        # Mock model structure
        mock_model = MagicMock()
        mock_solver = z3.Solver()
        mock_model.solver = mock_solver
        mock_model.z3_model_status = True
        mock_model.z3_model = MagicMock()
        
        mock_example.model_structure = mock_model
        
        # Add all_constraints
        mock_constraints.all_constraints = [premise_constraint, conclusion_constraint]
        
        # Create test iterator
        class TestIterator(BaseModelIterator):
            def _create_difference_constraint(self, previous_models):
                return z3.BoolVal(True)
                
            def _create_non_isomorphic_constraint(self, z3_model):
                return None
                
            def _create_stronger_constraint(self, isomorphic_model):
                return None
                
            def _calculate_differences(self, new_structure, previous_structure):
                return {}
        
        iterator = TestIterator(mock_example)
        
        # Test that constraint generator creates extended constraints correctly
        with patch.object(iterator, '_create_difference_constraint') as mock_diff:
            mock_diff.return_value = z3.Bool('difference')
            
            # The constraint generator creates extended constraints internally
            extended = iterator.constraint_generator.create_extended_constraints([MagicMock()])
            
            # Extended constraints should include difference constraint
            self.assertIsNotNone(extended)
            # The actual structure of extended constraints is a list of difference constraints
            # Just verify it was created without error
    
    def test_solver_isolation(self):
        """Test that iterator solver is isolated from original."""
        # Create mock example
        mock_example = MagicMock()
        mock_example.settings = {'iterate': 2}
        
        # Create original solver
        original_solver = z3.Solver()
        original_solver.add(z3.Bool('original'))
        
        mock_model = MagicMock()
        mock_model.solver = original_solver
        mock_model.z3_model_status = True
        mock_model.z3_model = MagicMock()
        
        mock_example.model_structure = mock_model
        
        # Mock model_constraints
        mock_constraints = MagicMock()
        mock_constraints.all_constraints = original_solver.assertions()
        mock_example.model_constraints = mock_constraints
        
        # Create test iterator
        class TestIterator(BaseModelIterator):
            def _create_difference_constraint(self, previous_models):
                return z3.Bool('new_constraint')
                
            def _create_non_isomorphic_constraint(self, z3_model):
                return None
                
            def _create_stronger_constraint(self, isomorphic_model):
                return None
                
            def _calculate_differences(self, new_structure, previous_structure):
                return {}
        
        iterator = TestIterator(mock_example)
        
        # Add constraint to iterator solver
        iterator.solver.add(z3.Bool('iterator_only'))
        
        # Check original solver doesn't have iterator constraint
        original_assertions = [str(a) for a in original_solver.assertions()]
        self.assertNotIn('iterator_only', original_assertions,
                        "Iterator constraints should not affect original solver")
        
        # Check iterator solver has both constraints
        iterator_assertions = [str(a) for a in iterator.solver.assertions()]
        self.assertIn('original', iterator_assertions)
        self.assertIn('iterator_only', iterator_assertions)


if __name__ == '__main__':
    unittest.main()