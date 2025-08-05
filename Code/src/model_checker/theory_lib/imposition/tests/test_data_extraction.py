"""Tests for imposition data extraction methods."""

import unittest
from unittest.mock import Mock

from model_checker.theory_lib.imposition.semantic import ImpositionModelStructure


class TestImpositionDataExtraction(unittest.TestCase):
    """Test data extraction methods for ImpositionModelStructure."""
    
    def test_extract_states(self):
        """Test extraction of categorized states."""
        # Create a mock structure
        structure = Mock(spec=ImpositionModelStructure)
        
        # Add the method we're testing
        structure.extract_states = ImpositionModelStructure.extract_states.__get__(structure)
        
        # Mock state collections
        structure.z3_world_states = [3, 5]  # World states
        structure.z3_possible_states = [1, 3, 5, 7]  # Possible states (including worlds)
        structure.all_states = [0, 1, 2, 3, 4, 5, 6, 7]  # All states
        
        # Test extraction
        states = structure.extract_states()
        
        # Verify result structure
        self.assertIsInstance(states, dict)
        self.assertIn('worlds', states)
        self.assertIn('possible', states)
        self.assertIn('impossible', states)
        
        # Verify categorization
        self.assertEqual(set(states['worlds']), {'s3', 's5'})
        self.assertEqual(set(states['possible']), {'s1', 's7'})  # Excludes worlds
        self.assertEqual(set(states['impossible']), {'s0', 's2', 's4', 's6'})
        
    def test_extract_evaluation_world(self):
        """Test extraction of main evaluation world."""
        structure = Mock(spec=ImpositionModelStructure)
        structure.extract_evaluation_world = ImpositionModelStructure.extract_evaluation_world.__get__(structure)
        
        # Mock semantics with main_world
        structure.semantics = Mock()
        structure.semantics.main_world = 5
        
        # Test extraction
        world = structure.extract_evaluation_world()
        self.assertEqual(world, 's5')
        
        # Test with None
        structure.semantics.main_world = None
        world = structure.extract_evaluation_world()
        self.assertIsNone(world)
        
    def test_extract_relations(self):
        """Test extraction of imposition relations."""
        structure = Mock(spec=ImpositionModelStructure)
        structure.extract_relations = ImpositionModelStructure.extract_relations.__get__(structure)
        
        # Mock imposition relations: (state, world, outcome)
        structure.z3_imposition_relations = [
            (1, 3, 3),  # s3 ->_s1 s3
            (2, 3, 5),  # s3 ->_s2 s5
            (1, 5, 7),  # s5 ->_s1 s7
            (4, 5, 5),  # s5 ->_s4 s5
        ]
        
        # Test extraction
        relations = structure.extract_relations()
        
        # Verify structure
        self.assertIsInstance(relations, dict)
        self.assertIn('imposition', relations)
        
        # Verify content
        impositions = relations['imposition']
        self.assertEqual(impositions['s3'], {'s1': 's3', 's2': 's5'})
        self.assertEqual(impositions['s5'], {'s1': 's7', 's4': 's5'})
        
    def test_extract_propositions(self):
        """Test extraction of proposition values."""
        structure = Mock(spec=ImpositionModelStructure)
        structure.extract_propositions = ImpositionModelStructure.extract_propositions.__get__(structure)
        
        # Mock world states
        structure.z3_world_states = [3, 5]
        
        # Mock syntax with propositions
        mock_syntax = Mock()
        mock_prop_p = Mock()
        mock_prop_p.evaluate_at = Mock(side_effect=lambda w: w == 3)  # True at world 3
        
        mock_prop_q = Mock()
        mock_prop_q.evaluate_at = Mock(side_effect=lambda w: w == 5)  # True at world 5
        
        mock_syntax.propositions = {'p': mock_prop_p, 'q': mock_prop_q}
        structure.syntax = mock_syntax
        
        # Test extraction
        propositions = structure.extract_propositions()
        
        # Verify structure
        self.assertIsInstance(propositions, dict)
        self.assertIn('p', propositions)
        self.assertIn('q', propositions)
        
        # Verify values
        self.assertEqual(propositions['p'], {'s3': True, 's5': False})
        self.assertEqual(propositions['q'], {'s3': False, 's5': True})
        
    def test_extract_propositions_no_syntax(self):
        """Test proposition extraction when no syntax available."""
        structure = Mock(spec=ImpositionModelStructure)
        structure.extract_propositions = ImpositionModelStructure.extract_propositions.__get__(structure)
        
        # No syntax attribute
        structure.syntax = Mock()
        delattr(structure.syntax, 'propositions')
        
        propositions = structure.extract_propositions()
        
        # Should return empty dict
        self.assertEqual(propositions, {})
        
    def test_extract_relations_no_impositions(self):
        """Test relation extraction when no impositions defined."""
        structure = Mock(spec=ImpositionModelStructure)
        structure.extract_relations = ImpositionModelStructure.extract_relations.__get__(structure)
        
        # No imposition relations
        delattr(structure, 'z3_imposition_relations')
        
        relations = structure.extract_relations()
        
        # Should return empty structure
        self.assertEqual(relations, {})


if __name__ == '__main__':
    unittest.main()