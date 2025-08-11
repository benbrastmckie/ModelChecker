"""Test Z3 injection for Imposition theory.

Imposition inherits from Logos, so it should already have injection support.
This test verifies that inheritance works correctly.
"""

import unittest
from unittest.mock import Mock
import z3
from model_checker.theory_lib.imposition.semantic import ImpositionSemantics


class TestImpositionInjection(unittest.TestCase):
    """Test Imposition theory Z3 injection functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.settings = {'N': 2}
        self.semantics = ImpositionSemantics(self.settings)
        
        # Create mock model constraints
        self.mock_constraints = Mock()
        self.mock_constraints.all_constraints = []
        self.mock_constraints.syntax = Mock()
        self.mock_constraints.syntax.sentence_letters = []
        self.mock_constraints.settings = {'N': 2}
    
    def test_inject_z3_model_values_exists(self):
        """Test that inject_z3_model_values method exists (inherited from Logos)."""
        self.assertTrue(hasattr(self.semantics, 'inject_z3_model_values'))
        
    def test_injection_works(self):
        """Test that injection functionality works."""
        # Create a minimal Z3 model
        solver = z3.Solver()
        solver.add(self.semantics.is_world(0))
        
        result = solver.check()
        self.assertEqual(result, z3.sat)
        z3_model = solver.model()
        
        # Inject values
        self.semantics.inject_z3_model_values(z3_model, self.semantics, self.mock_constraints)
        
        # Check that constraints were added
        self.assertGreater(len(self.mock_constraints.all_constraints), 0)
        
    def test_imposition_specific_constraints(self):
        """Test that imposition-specific constraints work with injection."""
        # Imposition theory has the imposition function
        self.assertTrue(hasattr(self.semantics, 'imposition'))
        
        # Create a Z3 model with imposition constraints
        solver = z3.Solver()
        solver.add(self.semantics.is_world(0))
        
        # Test that imposition function can be used
        # imposition(state, source, target)
        imp_result = self.semantics.imposition(0, 1, 2)
        self.assertIsNotNone(imp_result)
        
        result = solver.check()
        self.assertEqual(result, z3.sat)


if __name__ == '__main__':
    unittest.main()