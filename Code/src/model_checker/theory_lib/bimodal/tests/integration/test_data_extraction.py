"""Tests for bimodal data extraction methods."""

import unittest
from unittest.mock import Mock

from model_checker.theory_lib.bimodal.semantic import BimodalStructure


class TestBimodalDataExtraction(unittest.TestCase):
    """Test data extraction methods for BimodalStructure."""
    
    def test_extract_states(self):
        """Test extraction of world states."""
        # Create a mock structure instead of full initialization
        structure = Mock(spec=BimodalStructure)
        
        # Add the method we're testing
        structure.extract_states = BimodalStructure.extract_states.__get__(structure)
        
        # Mock world histories
        structure.world_histories = {
            0: {0: 'state0_t0', 1: 'state0_t1'},
            1: {0: 'state1_t0', 1: 'state1_t1', 2: 'state1_t2'},
            2: {1: 'state2_t1', 2: 'state2_t2'}
        }
        
        # Test extraction
        states = structure.extract_states()
        
        # Verify result structure
        self.assertIsInstance(states, dict)
        self.assertIn('worlds', states)
        self.assertIn('possible', states)
        self.assertIn('impossible', states)
        
        # All bimodal states are worlds
        self.assertEqual(set(states['worlds']), {'s0', 's1', 's2'})
        self.assertEqual(states['possible'], [])
        self.assertEqual(states['impossible'], [])
        
    def test_extract_evaluation_world(self):
        """Test extraction of main evaluation world."""
        structure = Mock(spec=BimodalStructure)
        structure.extract_evaluation_world = BimodalStructure.extract_evaluation_world.__get__(structure)
        
        # Test with main_world set
        structure.main_world = 3
        world = structure.extract_evaluation_world()
        self.assertEqual(world, 's3')
        
        # Test with no main_world
        structure.main_world = None
        world = structure.extract_evaluation_world()
        self.assertIsNone(world)
        
    def test_extract_relations(self):
        """Test extraction of time shift relations."""
        structure = Mock(spec=BimodalStructure)
        structure.extract_relations = BimodalStructure.extract_relations.__get__(structure)
        
        # Mock time shift relations
        structure.time_shift_relations = {
            0: {0: 0, 1: 1, -1: 2},
            1: {0: 1, 1: 2},
            2: {0: 2, -1: 1}
        }
        
        # Test extraction
        relations = structure.extract_relations()
        
        # Verify structure
        self.assertIsInstance(relations, dict)
        self.assertIn('time_shift', relations)
        
        # Verify content
        time_shifts = relations['time_shift']
        self.assertEqual(time_shifts['s0'], {'0': 's0', '1': 's1', '-1': 's2'})
        self.assertEqual(time_shifts['s1'], {'0': 's1', '1': 's2'})
        self.assertEqual(time_shifts['s2'], {'0': 's2', '-1': 's1'})
        
    def test_extract_propositions(self):
        """Test extraction of proposition values."""
        structure = Mock(spec=BimodalStructure)
        structure.extract_propositions = BimodalStructure.extract_propositions.__get__(structure)
        
        # Mock world histories for evaluation
        structure.world_histories = {0: {0: 'state0'}, 1: {0: 'state1'}}
        
        # Mock syntax with propositions
        mock_syntax = Mock()
        mock_prop_p = Mock()
        mock_prop_p.letter = 'p'
        mock_prop_p.evaluate_at = Mock(side_effect=lambda w, t: w == 0)  # True at world 0
        
        mock_prop_q = Mock()
        mock_prop_q.letter = 'q'
        mock_prop_q.evaluate_at = Mock(side_effect=lambda w, t: w == 1)  # True at world 1
        
        mock_syntax.propositions = {'p': mock_prop_p, 'q': mock_prop_q}
        structure.syntax = mock_syntax
        
        # Test extraction
        propositions = structure.extract_propositions()
        
        # Verify structure
        self.assertIsInstance(propositions, dict)
        self.assertIn('p', propositions)
        self.assertIn('q', propositions)
        
        # Verify values
        self.assertEqual(propositions['p'], {'s0': True, 's1': False})
        self.assertEqual(propositions['q'], {'s0': False, 's1': True})
        
    def test_extract_propositions_no_syntax(self):
        """Test proposition extraction when no syntax available."""
        structure = Mock(spec=BimodalStructure)
        structure.extract_propositions = BimodalStructure.extract_propositions.__get__(structure)
        
        # No syntax attribute - hasattr should return False
        delattr(structure, 'syntax')
        
        propositions = structure.extract_propositions()
        
        # Should return empty dict
        self.assertEqual(propositions, {})
        
    def test_extract_states_no_histories(self):
        """Test state extraction when no world histories."""
        structure = Mock(spec=BimodalStructure)
        structure.extract_states = BimodalStructure.extract_states.__get__(structure)
        
        # No world_histories attribute
        delattr(structure, 'world_histories')
        
        states = structure.extract_states()
        
        # Should return empty structure
        self.assertEqual(states, {"worlds": [], "possible": [], "impossible": []})


if __name__ == '__main__':
    unittest.main()