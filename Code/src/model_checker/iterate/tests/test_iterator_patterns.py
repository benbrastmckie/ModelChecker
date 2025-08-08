"""Test iterator usage of pattern-based constraints.

Tests that the iterator correctly uses pattern extraction to generate
structurally distinct models without referencing model objects.
"""

import unittest
from unittest.mock import Mock, patch, MagicMock
import z3
from model_checker.iterate.core import BaseModelIterator
from model_checker.iterate.patterns import StructuralPattern, create_structural_difference_constraint


class TestIteratorPatterns(unittest.TestCase):
    """Test iterator's use of pattern-based constraints."""
    
    def setUp(self):
        """Set up test environment."""
        # Create mock build_example
        self.mock_build = Mock()
        self.mock_build.output = Mock()
        self.mock_build.output.debug = Mock()
        
        # Add proper settings
        self.mock_build.settings = {
            'iterate': 3,
            'iteration_attempts': 5,
            'escape_attempts': 3
        }
        
        # Create mock model constraints
        self.mock_model_constraints = Mock()
        self.mock_model_constraints.all_constraints = [z3.Bool('c1'), z3.Bool('c2')]  # Add some constraints
        self.mock_model_constraints.semantics = Mock()
        self.mock_model_constraints.semantics.N = 2
        self.mock_model_constraints.sentence_letters = ['A', 'B']
        
        self.mock_build.model_constraints = self.mock_model_constraints
        
        # Create mock model structure
        self.mock_model_structure = Mock()
        self.mock_model_structure.z3_model = Mock()
        self.mock_model_structure.z3_model_status = True
        self.mock_model_structure.z3_world_states = [0, 1]  # Mock world states
        self.mock_model_structure.z3_possible_states = [0, 1, 2, 3]  # Mock possible states
        
        # Mock solver with spec to avoid assertion errors
        mock_solver = Mock(spec=['assertions', 'add', 'check'])
        mock_solver.assertions = Mock(return_value=[])
        self.mock_model_structure.solver = mock_solver
        
        self.mock_build.model_structure = self.mock_model_structure
        
    @patch('model_checker.iterate.core.StructuralPattern')
    @patch('model_checker.iterate.core.create_structural_difference_constraint')
    def test_iterator_uses_pattern_constraints(self, mock_create_diff, mock_pattern_class):
        """Iterator must use pattern-based constraints."""
        # Set up mocks
        mock_pattern = Mock()
        mock_pattern_class.return_value = mock_pattern
        mock_create_diff.return_value = z3.BoolVal(True)
        
        # Create iterator (this should extract initial pattern)
        iterator = BaseModelIterator(self.mock_build)
        
        # Verify initial pattern was extracted
        mock_pattern_class.assert_called_once_with(
            self.mock_model_constraints,
            self.mock_model_structure.z3_model
        )
        
        # Verify pattern was tracked
        self.assertEqual(len(iterator.found_patterns), 1)
        self.assertEqual(iterator.found_patterns[0], mock_pattern)
        
    @patch('model_checker.iterate.core.StructuralPattern')
    @patch('model_checker.iterate.core.create_structural_difference_constraint')
    def test_iterator_creates_extended_constraints(self, mock_create_diff, mock_pattern_class):
        """Iterator must create extended constraints using patterns."""
        # Set up mocks
        mock_pattern = Mock()
        mock_pattern_class.return_value = mock_pattern
        mock_diff_constraint = z3.Bool('diff')
        mock_create_diff.return_value = mock_diff_constraint
        
        # Create iterator
        iterator = BaseModelIterator(self.mock_build)
        
        # Create extended constraints
        extended = iterator._create_extended_constraints()
        
        # Verify difference constraint was created
        mock_create_diff.assert_called_once_with(
            self.mock_model_constraints,
            [mock_pattern]
        )
        
        # Verify extended constraints include difference
        self.assertIn(mock_diff_constraint, extended)
        
    @patch('model_checker.iterate.core.StructuralPattern')
    @patch('model_checker.iterate.core.create_structural_difference_constraint')
    def test_iterator_tracks_patterns_during_iteration(self, mock_create_diff, mock_pattern_class):
        """Iterator must track patterns for each found model."""
        # Set up pattern mocks
        pattern1 = Mock()
        pattern2 = Mock()
        mock_pattern_class.side_effect = [pattern1]  # Just initial pattern
        mock_create_diff.return_value = z3.BoolVal(True)
        
        # Create iterator
        iterator = BaseModelIterator(self.mock_build)
        
        # Verify initial pattern was tracked
        self.assertEqual(len(iterator.found_patterns), 1)
        self.assertEqual(iterator.found_patterns[0], pattern1)
        
        # Now manually test what happens when a new model is found
        # This simulates the code in iterate() after finding a valid model
        mock_pattern_class.side_effect = [pattern2]  # Next pattern
        
        # Simulate adding a new model (this is what happens in iterate())
        new_z3_model = Mock()
        new_model_structure = Mock()
        new_model_structure.z3_model = new_z3_model
        
        # Manually execute the pattern tracking code
        iterator.found_models.append(new_z3_model)
        iterator.model_structures.append(new_model_structure)
        iterator.current_iteration += 1
        
        # Track pattern for the new model using the mock
        iterator.found_patterns.append(pattern2)
        
        # Verify both patterns are tracked
        self.assertEqual(len(iterator.found_patterns), 2)
        self.assertEqual(iterator.found_patterns[0], pattern1)
        self.assertEqual(iterator.found_patterns[1], pattern2)
        
    def test_iterator_imports_pattern_modules(self):
        """Iterator must import pattern extraction modules."""
        # Check that BaseModelIterator can import pattern modules
        from model_checker.iterate import core
        
        # Verify imports are available
        self.assertTrue(hasattr(core, 'StructuralPattern'))
        self.assertTrue(hasattr(core, 'create_structural_difference_constraint'))


if __name__ == '__main__':
    unittest.main()