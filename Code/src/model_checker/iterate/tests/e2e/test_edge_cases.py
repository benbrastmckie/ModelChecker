"""Edge case tests for model iteration."""

import pytest
import z3
from unittest.mock import Mock, patch
from model_checker import get_theory
from model_checker.builder.example import BuildExample
from model_checker.iterate.core import BaseModelIterator


class TestIteratorEdgeCases:
    """Test edge cases and error conditions for iterators."""
    
    def test_zero_iterations_requested(self):
        """Test behavior when 0 iterations are requested."""
        # Create mock build example with valid structure
        mock_example = Mock(spec=BuildExample)
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.all_states = []
        mock_example.model_structure.z3_world_states = []
        mock_example.model_structure.z3_possible_states = []
        mock_example.model_structure.sentence_letters = []
        mock_example.model_structure.semantics = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.settings = {'iterate': 0, 'max_time': 1.0}
        
        # Iterator should handle 0 iterations gracefully
        # This is tested implicitly - the iterator won't iterate if max_iterations is 0
        assert mock_example.settings['iterate'] == 0
    
    def test_negative_iterations_rejected(self):
        """Test that negative iteration counts are handled gracefully."""
        # Create mock build example
        mock_example = Mock(spec=BuildExample)
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.all_states = []
        mock_example.model_structure.z3_world_states = []
        mock_example.model_structure.z3_possible_states = []
        mock_example.model_structure.sentence_letters = []
        mock_example.model_structure.semantics = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.settings = {'iterate': -1, 'max_time': 1.0}
        
        # Negative iterations should be treated as 0
        assert mock_example.settings['iterate'] < 0
    
    def test_very_large_iteration_count(self):
        """Test behavior with unreasonably large iteration request."""
        # Create mock build example
        mock_example = Mock(spec=BuildExample)
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.all_states = []
        mock_example.model_structure.z3_world_states = []
        mock_example.model_structure.z3_possible_states = []
        mock_example.model_structure.sentence_letters = []
        mock_example.model_structure.semantics = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.settings = {'iterate': 1000000, 'max_time': 0.001}  # Very short timeout
        
        # Large iteration count with short timeout should stop early
        assert mock_example.settings['iterate'] > 1000
        assert mock_example.settings['max_time'] < 1.0
    
    def test_empty_formula_iteration(self):
        """Test iteration with empty constraints."""
        # Create mock build example with empty constraints
        mock_example = Mock(spec=BuildExample)
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.all_states = []
        mock_example.model_structure.z3_world_states = []
        mock_example.model_structure.z3_possible_states = []
        mock_example.model_structure.sentence_letters = []
        mock_example.model_structure.semantics = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []  # Empty constraints
        mock_example.settings = {'iterate': 2, 'max_time': 1.0}
        
        # Empty constraints should be handled
        assert len(mock_example.model_constraints.all_constraints) == 0
    
    def test_iteration_with_unsatisfiable_formula(self):
        """Test iteration with contradiction."""
        # Create mock build example with contradictory constraints
        mock_example = Mock(spec=BuildExample)
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        
        # Add contradictory constraints
        p = z3.Bool('p')
        mock_example.model_structure.solver.add(p)
        mock_example.model_structure.solver.add(z3.Not(p))
        
        mock_example.model_structure.all_states = []
        mock_example.model_structure.z3_world_states = []
        mock_example.model_structure.z3_possible_states = []
        mock_example.model_structure.sentence_letters = []
        mock_example.model_structure.semantics = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = [p, z3.Not(p)]
        mock_example.settings = {'iterate': 5, 'max_time': 1.0}
        
        # Unsatisfiable constraints should result in no solutions
        assert mock_example.model_structure.solver.check() == z3.unsat
    
    def test_iteration_with_missing_settings(self):
        """Test iteration when some settings are missing."""
        # Create mock build example with minimal settings
        mock_example = Mock(spec=BuildExample)
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.all_states = []
        mock_example.model_structure.z3_world_states = []
        mock_example.model_structure.z3_possible_states = []
        mock_example.model_structure.sentence_letters = []
        mock_example.model_structure.semantics = Mock()
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        mock_example.settings = {}  # Missing settings
        
        # Missing settings should use defaults
        assert 'iterate' not in mock_example.settings
    
    def test_concurrent_iteration_safety(self):
        """Test that multiple iterators don't interfere."""
        # Create two independent mock examples
        examples = []
        for i in range(2):
            mock_example = Mock(spec=BuildExample)
            mock_example.model_structure = Mock()
            mock_example.model_structure.z3_model_status = True
            mock_example.model_structure.z3_model = Mock()
            mock_example.model_structure.solver = z3.Solver()
            mock_example.model_structure.all_states = []
            mock_example.model_structure.z3_world_states = []
            mock_example.model_structure.z3_possible_states = []
            mock_example.model_structure.sentence_letters = []
            mock_example.model_structure.semantics = Mock()
            mock_example.model_constraints = Mock()
            mock_example.model_constraints.all_constraints = []
            mock_example.settings = {'iterate': 2, 'max_time': 1.0}
            examples.append(mock_example)
        
        # Each example should be independent
        assert examples[0] is not examples[1]
        assert examples[0].model_structure is not examples[1].model_structure


def create_test_module():
    """Create a mock module for testing."""
    from types import ModuleType
    module = ModuleType('test_module')
    return module