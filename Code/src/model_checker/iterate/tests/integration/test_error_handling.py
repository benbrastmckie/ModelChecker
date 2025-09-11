"""Integration tests for error handling in iterate package."""

import pytest
from unittest.mock import Mock, patch
import z3
from model_checker.iterate.core import BaseModelIterator
from model_checker.iterate.iterator import IteratorCore
from model_checker.iterate.errors import (
    IterationStateError,
    ModelExtractionError,
    IterationTimeoutError
)


class TestIteratorErrorHandling:
    """Test error handling in IteratorCore."""
    
    def test_invalid_build_example_no_model_structure(self):
        """Test error when BuildExample has no model_structure."""
        mock_example = Mock()
        mock_example.model_structure = None
        
        with pytest.raises(IterationStateError) as exc_info:
            IteratorCore(mock_example)
        
        assert "has no model_structure" in str(exc_info.value)
        assert "Ensure the BuildExample has been properly built" in str(exc_info.value)
    
    def test_invalid_build_example_no_z3_model(self):
        """Test error when BuildExample has no Z3 model."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = None
        
        with pytest.raises(IterationStateError) as exc_info:
            IteratorCore(mock_example)
        
        assert "has no Z3 model" in str(exc_info.value)
        assert "Check that the Z3 solver successfully generated a model" in str(exc_info.value)
    
    def test_invalid_build_example_not_satisfiable(self):
        """Test error when BuildExample model is not satisfiable."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = False
        
        with pytest.raises(IterationStateError) as exc_info:
            IteratorCore(mock_example)
        
        assert "does not have a valid model" in str(exc_info.value)
        assert "Ensure the initial formula is satisfiable" in str(exc_info.value)
    
    def test_invalid_settings_iterate_value(self):
        """Test error with invalid iterate setting."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.settings = {'iterate': 'not_an_int'}
        
        with pytest.raises(IterationStateError) as exc_info:
            IteratorCore(mock_example)
        
        assert "iterate must be a positive integer" in str(exc_info.value)
        assert "Set 'iterate' to a positive integer value" in str(exc_info.value)
    
    def test_invalid_settings_timeout_value(self):
        """Test error with invalid timeout setting."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.settings = {'iterate': 5, 'timeout': -10}
        
        with pytest.raises(IterationStateError) as exc_info:
            IteratorCore(mock_example)
        
        assert "timeout must be positive" in str(exc_info.value)
        assert "Set 'timeout' to a positive number in seconds" in str(exc_info.value)
    
    def test_iterate_with_unsatisfiable_model(self):
        """Test error when model is not satisfiable."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = False  # Not satisfiable
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.z3_model_runtime = 0.1
        mock_example.model_structure._search_duration = 0.1
        mock_example.settings = {}
        
        # Should raise error since model is not satisfiable
        with pytest.raises(IterationStateError) as exc_info:
            IteratorCore(mock_example)
        
        assert "does not have a valid model" in str(exc_info.value)
    
    def test_iterate_single_model_requested(self):
        """Test iterate when only one model is requested."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.z3_model_runtime = 0.1
        mock_example.model_structure._search_duration = 0.1
        mock_example.model_structure._total_search_time = 0.1
        mock_example.model_structure.z3_world_states = []
        mock_example.model_structure.z3_possible_states = []
        mock_example.settings = {'iterate': 1}
        
        iterator = IteratorCore(mock_example)
        result = iterator.iterate()
        
        # Should return only the initial model structure
        assert len(result) == 1
        assert result[0] == mock_example.model_structure


class TestCoreErrorHandling:
    """Test error handling in BaseModelIterator core."""
    
    class ConcreteIterator(BaseModelIterator):
        """Concrete implementation for testing."""
        
        def _create_difference_constraint(self, previous_models):
            return z3.BoolVal(True)
        
        def _create_non_isomorphic_constraint(self, isomorphic_model):
            return z3.BoolVal(True)
        
        def _create_stronger_constraint(self, isomorphic_model):
            return z3.BoolVal(True)
    
    def test_iterate_with_model_extraction_error(self):
        """Test handling of ModelExtractionError during iteration."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.z3_world_states = [Mock()]
        mock_example.model_structure.z3_possible_states = [Mock()]
        mock_example.model_structure.z3_model_runtime = 0.1
        mock_example.model_structure._total_search_time = 0.1
        mock_example.settings = {'iterate': 3, 'timeout': 300}
        mock_example.syntax = Mock()
        mock_example.syntax.operator_dictionary = {}
        mock_example.model_structures = []
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        
        iterator = self.ConcreteIterator(mock_example)
        
        # Mock constraint generator to return sat
        with patch.object(iterator.constraint_generator, 'check_satisfiability', return_value='sat'):
            with patch.object(iterator.constraint_generator, 'get_model', return_value=Mock()):
                # Mock the model builder to raise ModelExtractionError
                with patch.object(iterator.model_builder, 'build_new_model_structure') as mock_build:
                    mock_build.side_effect = ModelExtractionError(
                        model_num=2,
                        reason="Test error",
                        suggestion="Fix the issue"
                    )
                    
                    # Should raise the error
                    with pytest.raises(ModelExtractionError) as exc_info:
                        list(iterator.iterate_generator())
                    
                    assert "Failed to extract model 2" in str(exc_info.value)
                    assert "Test error" in str(exc_info.value)
    
    def test_iterate_generator_keyboard_interrupt(self):
        """Test handling of keyboard interrupt during iteration."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.z3_world_states = [Mock()]
        mock_example.model_structure.z3_possible_states = [Mock()]
        mock_example.model_structure.z3_model_runtime = 0.1
        mock_example.model_structure._total_search_time = 0.1
        mock_example.settings = {'iterate': 5, 'timeout': 300}
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        
        iterator = self.ConcreteIterator(mock_example)
        
        # Mock constraint generator to raise KeyboardInterrupt
        with patch.object(iterator.constraint_generator, 'check_satisfiability') as mock_check:
            mock_check.side_effect = KeyboardInterrupt()
            
            # Should handle interrupt gracefully
            result = list(iterator.iterate_generator())
            
            # Should return empty since first iteration was interrupted
            assert result == []
    
    def test_reset_iterator(self):
        """Test resetting iterator to initial state."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.z3_world_states = [Mock()]
        mock_example.model_structure.z3_possible_states = [Mock()]
        mock_example.settings = {}
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        
        iterator = self.ConcreteIterator(mock_example)
        
        # Add some models
        iterator.found_models.append(Mock())
        iterator.model_structures.append(Mock())
        iterator.current_iteration = 3
        iterator.debug_messages.append("test message")
        iterator.checked_model_count = 5
        
        # Reset
        iterator.reset_iterator()
        
        # Should be back to initial state
        assert len(iterator.found_models) == 1  # Only initial model
        assert len(iterator.model_structures) == 1  # Only initial structure
        assert iterator.current_iteration == 1
        assert len(iterator.debug_messages) == 0
        assert iterator.checked_model_count == 1
    
    def test_get_debug_messages(self):
        """Test getting debug messages."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.z3_world_states = [Mock()]
        mock_example.model_structure.z3_possible_states = [Mock()]
        mock_example.settings = {}
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        
        iterator = self.ConcreteIterator(mock_example)
        
        # Add some debug messages to the internal iterator_core
        iterator.iterator_core.debug_messages = ["msg1", "msg2", "msg3"]
        
        # Get messages
        messages = iterator.get_debug_messages()
        
        # Should return copy of messages
        assert messages == ["msg1", "msg2", "msg3"]
        assert messages is not iterator.iterator_core.debug_messages  # Should be a copy
    
    def test_get_iteration_summary(self):
        """Test getting iteration summary."""
        mock_example = Mock()
        mock_example.model_structure = Mock()
        mock_example.model_structure.z3_model_status = True
        mock_example.model_structure.z3_model = Mock()
        mock_example.model_structure.solver = z3.Solver()
        mock_example.model_structure.z3_world_states = [Mock()]
        mock_example.model_structure.z3_possible_states = [Mock()]
        mock_example.settings = {}
        mock_example.model_constraints = Mock()
        mock_example.model_constraints.all_constraints = []
        
        iterator = self.ConcreteIterator(mock_example)
        
        # Get summary
        summary = iterator.get_iteration_summary()
        
        # Should return dict with statistics
        assert isinstance(summary, dict)
        assert 'total_models' in summary
        assert 'avg_worlds' in summary