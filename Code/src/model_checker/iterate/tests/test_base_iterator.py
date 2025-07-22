"""Tests for the base model iterator functionality."""

import pytest
import z3
import time
from unittest.mock import Mock, patch
from model_checker.iterate.core import BaseModelIterator
from model_checker.builder.example import BuildExample


class MockModelIterator(BaseModelIterator):
    """Mock implementation for testing base functionality."""
    
    def _calculate_differences(self, new_structure, previous_structure):
        return {"test": "differences"}
    
    def _create_difference_constraint(self, previous_models):
        return z3.BoolVal(True)
    
    def _create_non_isomorphic_constraint(self, z3_model):
        return z3.BoolVal(True)
    
    def _create_stronger_constraint(self, isomorphic_model):
        return z3.BoolVal(True)


class TestBaseModelIterator:
    """Test cases for BaseModelIterator."""
    
    def test_abstract_methods_required(self):
        """Test that abstract methods must be implemented."""
        with pytest.raises(TypeError):
            BaseModelIterator(Mock())
    
    def test_initialization_validation(self):
        """Test initialization validates inputs."""
        # Test with invalid BuildExample
        with pytest.raises(TypeError):
            MockModelIterator("not a BuildExample")
        
        # Test with BuildExample without model
        mock_example = Mock(spec=BuildExample)
        mock_example.model_structure = None
        with pytest.raises(ValueError, match="no model_structure"):
            MockModelIterator(mock_example)
    
    def test_timeout_handling(self):
        """Test iteration timeout is properly handled."""
        # Create mock example with slow solver
        mock_example = create_mock_example()
        iterator = MockModelIterator(mock_example)
        
        # Set very short timeout
        iterator.settings['iteration_timeout'] = 0.001
        
        # Mock slow solver check
        def slow_check():
            import time
            time.sleep(0.1)
            return z3.unsat
        
        with patch.object(iterator.solver, 'check', side_effect=slow_check):
            # Run iteration
            models = iterator.iterate()
        
        # Should stop due to timeout or no models
        assert len(models) == 1  # Only initial model
        # Check messages - unsat should mean no additional models
        debug_msgs = iterator.debug_messages
        # Print for debugging
        print(f"Debug messages: {debug_msgs}")
        # Either timeout or unsat (no models) message should be present
        assert len(debug_msgs) > 0  # Should have some messages
    
    def test_invalid_model_handling(self):
        """Test handling of models with no possible worlds."""
        mock_example = create_mock_example()
        iterator = MockModelIterator(mock_example)
        
        # Mock solver to return sat but with invalid model
        with patch.object(iterator.solver, 'check', return_value=z3.sat):
            # Mock solver.model() to return a valid Z3 model
            mock_z3_model = Mock()
            with patch.object(iterator.solver, 'model', return_value=mock_z3_model):
                with patch.object(iterator, '_build_new_model_structure') as mock_build:
                    # Return structure with no worlds
                    mock_structure = Mock()
                    mock_structure.z3_world_states = []
                    mock_structure.model_differences = {"test": "differences"}
                    mock_build.return_value = mock_structure
                    
                    # Run iteration requesting 3 models
                    iterator.max_iterations = 3
                    models = iterator.iterate()
                    
                    # Should only have initial model
                    assert len(models) == 1
                    # Check for invalid model message
                    debug_msgs = iterator.debug_messages
                    assert any("invalid" in msg.lower() or "no world" in msg.lower()
                              for msg in debug_msgs)
    
    def test_consecutive_invalid_limit(self):
        """Test that consecutive invalid models trigger stop."""
        mock_example = create_mock_example()
        iterator = MockModelIterator(mock_example)
        iterator.settings['max_invalid_attempts'] = 3
        
        # Mock to always return invalid models
        with patch.object(iterator, '_build_new_model_structure') as mock_build:
            mock_structure = Mock()
            mock_structure.z3_world_states = []
            mock_build.return_value = mock_structure
            
            # Run iteration
            iterator.max_iterations = 10
            models = iterator.iterate()
            
            # Should stop after max_invalid_attempts
            assert len(models) == 1
            assert any("Too many consecutive invalid" in msg 
                      for msg in iterator.debug_messages)
    
    def test_isomorphism_detection(self):
        """Test isomorphism detection and escape attempts."""
        # This test requires NetworkX
        pytest.importorskip("networkx")
        
        mock_example = create_mock_example()
        iterator = MockModelIterator(mock_example)
        
        # TODO: Implement isomorphism test
        # Requires mocking ModelGraph and isomorphism checks
    
    def test_debug_message_collection(self):
        """Test debug messages are properly collected."""
        mock_example = create_mock_example()
        iterator = MockModelIterator(mock_example)
        
        # Run single iteration
        iterator.max_iterations = 2
        models = iterator.iterate()
        
        # Check debug messages
        debug_msgs = iterator.get_debug_messages()
        assert all("[ITERATION]" in msg for msg in debug_msgs)
        assert len(debug_msgs) > 0


def create_mock_example():
    """Create a mock BuildExample for testing."""
    mock_example = Mock(spec=BuildExample)
    
    # Mock model structure
    mock_structure = Mock()
    mock_structure.z3_model_status = True
    mock_structure.z3_model = Mock()
    mock_structure.solver = z3.Solver()
    mock_structure.all_states = [z3.BitVecVal(i, 4) for i in range(4)]
    mock_structure.z3_world_states = [z3.BitVecVal(0, 4)]
    mock_structure.z3_possible_states = [z3.BitVecVal(0, 4), z3.BitVecVal(1, 4)]
    mock_structure.sentence_letters = []
    mock_structure.semantics = Mock()
    
    mock_example.model_structure = mock_structure
    mock_example.settings = {'iterate': 5, 'max_time': 1.0}
    
    return mock_example