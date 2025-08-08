"""Minimal test for pattern extraction utilities."""

import unittest
import z3
from model_checker.iterate.patterns import StructuralPattern, create_structural_difference_constraint


class TestPatternMinimal(unittest.TestCase):
    """Minimal tests for pattern extraction."""
    
    def test_empty_pattern_list(self):
        """Empty pattern list should return trivial constraint."""
        # Create a mock model_constraints object
        class MockModelConstraints:
            pass
        
        mock_constraints = MockModelConstraints()
        
        # Test with empty list
        constraint = create_structural_difference_constraint(mock_constraints, [])
        
        # Should be True (no exclusions)
        self.assertEqual(constraint, z3.BoolVal(True))
    
    def test_pattern_creation(self):
        """Test creating a structural pattern."""
        # Create mock objects
        class MockSemantics:
            N = 2  # 4 possible states
            
            def is_world(self, state):
                # States 0 and 1 are worlds
                return z3.BoolVal(state < 2)
            
            def possible(self, state):
                # All states are possible
                return z3.BoolVal(True)
            
            def verify(self, state, letter):
                # State 0 verifies A, state 1 verifies B
                if str(letter) == 'A':
                    return z3.BoolVal(state == 0)
                else:
                    return z3.BoolVal(state == 1)
            
            def falsify(self, state, letter):
                # State 2 falsifies A, state 3 falsifies B
                if str(letter) == 'A':
                    return z3.BoolVal(state == 2)
                else:
                    return z3.BoolVal(state == 3)
        
        class MockModelConstraints:
            def __init__(self):
                self.semantics = MockSemantics()
                self.sentence_letters = ['A', 'B']
        
        # Create a mock Z3 model
        class MockZ3Model:
            def eval(self, expr, model_completion=False):
                # Just return the expression since we're using BoolVal
                return expr
        
        mock_constraints = MockModelConstraints()
        mock_model = MockZ3Model()
        
        # Create pattern
        pattern = StructuralPattern(mock_constraints, mock_model)
        
        # Check pattern structure
        self.assertIn('num_worlds', pattern.pattern)
        self.assertIn('num_possible', pattern.pattern)
        self.assertIn('world_states', pattern.pattern)
        self.assertIn('verify', pattern.pattern)
        self.assertIn('falsify', pattern.pattern)
        
        # Check values
        self.assertEqual(pattern.pattern['num_worlds'], 2)
        self.assertEqual(pattern.pattern['num_possible'], 4)
        self.assertEqual(pattern.pattern['world_states'], [0, 1])
        self.assertEqual(pattern.pattern['verify']['A'], [0])
        self.assertEqual(pattern.pattern['verify']['B'], [1])
        self.assertEqual(pattern.pattern['falsify']['A'], [2])
        self.assertEqual(pattern.pattern['falsify']['B'], [3])


if __name__ == '__main__':
    unittest.main()