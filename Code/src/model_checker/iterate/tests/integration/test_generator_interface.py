"""Tests for hybrid generator interface in iterator."""

import pytest
from unittest.mock import Mock, MagicMock, patch
import z3

from model_checker.iterate.core import BaseModelIterator
from model_checker.models.structure import ModelDefaults
from model_checker.builder.example import BuildExample


class ConcreteIterator(BaseModelIterator):
    """Concrete implementation for testing."""
    
    def _create_difference_constraint(self, model_diff):
        """Create a simple difference constraint."""
        # Return a simple non-false constraint
        return z3.Bool('diff') == True
        
    def _create_non_isomorphic_constraint(self, isomorphic_model):
        """Create a simple non-isomorphic constraint."""
        # Return a simple non-false constraint
        return z3.Bool('non_iso') == True


class TestGeneratorInterface:
    """Test hybrid generator interface."""
    
    def _create_test_example(self):
        """Create a mock BuildExample for testing."""
        example = Mock()
        example.settings = {
            'iterate': 3,
            'timeout': 10,
            'verbose': False,
            'N': 2
        }
        example.N = 2
        example.model = Mock()
        
        # Create more complete model structure mock
        example.model_structure = Mock()
        example.model_structure.z3_model_status = 'sat'
        example.model_structure.z3_world_states = []
        example.model_structure.z3_possible_states = []
        
        # Mock solver with proper spec
        mock_solver = Mock(spec=['check', 'model', 'assertions', 'push', 'pop', 'add', 'assert_and_track'])
        mock_solver.check.return_value = z3.sat
        mock_solver.model.return_value = Mock()
        mock_solver.assertions.return_value = []
        example.model_structure.solver = mock_solver
        example.model_structure.z3_model = Mock()
        example.model_structure.z3_model_runtime = 0.01  # Add runtime for report generation
        example.model_structure._search_duration = 0.01  # Fallback for report generation
        example.model_structure._total_search_time = 0.01  # Add total search time for iteration report
        
        # Mock semantic theory
        example.semantic_theory = {
            'semantics': Mock,
            'model': Mock,
            'proposition': Mock
        }
        
        # Mock model constraints
        mock_constraints = Mock()
        mock_constraints.all_constraints = []
        example.model_constraints = mock_constraints
        
        example.premises = []
        example.conclusions = []
        
        # Mock _unified_progress if it exists
        example._unified_progress = None  # No progress tracking in tests
        
        return example
    
    def _create_test_iterator(self, max_iterations=3):
        """Create a test iterator instance."""
        example = self._create_test_example()
        example.settings['iterate'] = max_iterations  # Set the correct max_iterations
        iterator = ConcreteIterator(example)
        
        # Mock the internal components to return predictable models
        iterator.constraint_generator.check_satisfiability = Mock(return_value='sat')
        iterator.constraint_generator.get_model = Mock(side_effect=[
            Mock(name=f"model_{i}") for i in range(max_iterations)
        ])
        
        # Mock model builder to return unique structures
        def create_structure(model):
            structure = Mock()
            structure.z3_model_status = 'sat'
            structure._model_id = id(model)
            structure.z3_world_states = [Mock()]  # Add at least one world state
            structure.z3_possible_states = [Mock(), Mock()]  # Add possible states
            structure.sentence_letters = []  # Empty list for sentence letters
            structure.model_differences = {}  # Empty dict for differences
            return structure
            
        iterator.model_builder.build_new_model_structure = Mock(side_effect=create_structure)
        
        # Mock isomorphism checker to always return False (no isomorphism)
        iterator.isomorphism_checker.check_isomorphism = Mock(return_value=(False, None))
        
        # Mock difference calculator to return empty dict
        iterator.difference_calculator.calculate_differences = Mock(return_value={})
        
        return iterator
    
    def test_iterate_generator_yields_incrementally(self):
        """Test that iterate_generator yields models one at a time."""
        iterator = self._create_test_iterator(max_iterations=3)
        
        # Check we have iterate_generator method
        assert hasattr(iterator, 'iterate_generator'), "iterate_generator method not found"
        
        gen = iterator.iterate_generator()
        
        # First model should be yielded immediately
        model1 = next(gen)
        assert model1 is not None
        # Internal state should have exactly two models (initial + new)
        assert len(iterator.model_structures) == 2
        
        # Second model
        model2 = next(gen)
        assert model2 is not None
        assert len(iterator.model_structures) == 3
        
        # Third model - won't be yielded since max_iterations=3 and we already have initial model
        with pytest.raises(StopIteration):
            next(gen)
        
        # Should raise StopIteration when exhausted
        with pytest.raises(StopIteration):
            next(gen)
            
    def test_generator_maintains_history(self):
        """Test that generator maintains complete history internally."""
        iterator = self._create_test_iterator(max_iterations=3)
        
        # Consume all models from generator
        models = list(iterator.iterate_generator())
        
        # Should have complete history for constraint generation
        assert len(iterator.found_models) == 3  # initial + 2 new
        assert len(iterator.model_structures) == 3  # initial + 2 new
        assert len(models) == 2  # only 2 new models yielded
        
    def test_backward_compatibility(self):
        """Test that iterate() still returns complete list."""
        iterator = self._create_test_iterator(max_iterations=3)
        models = iterator.iterate()
        
        assert isinstance(models, list)
        assert len(models) == 3  # includes initial model
        # Should include the initial model in the count
        assert len(iterator.model_structures) == 3
        
    def test_generator_with_no_models(self):
        """Test generator behavior when no models can be found."""
        iterator = self._create_test_iterator(max_iterations=3)
        # Mock to return unsat immediately
        iterator.constraint_generator.check_satisfiability = Mock(return_value='unsat')
        
        gen = iterator.iterate_generator()
        models = list(gen)
        
        assert len(models) == 0
        assert len(iterator.model_structures) == 1  # Still has initial model
        
    def test_generator_with_single_model(self):
        """Test generator with only one model found."""
        iterator = self._create_test_iterator(max_iterations=1)
        
        gen = iterator.iterate_generator()
        
        # Should be empty generator since max_iterations=1 (just initial model)
        models = list(gen)
        assert len(models) == 0
            
        # Should still have initial model
        assert len(iterator.model_structures) == 1
            
    def test_generator_handles_isomorphic_models(self):
        """Test that generator skips isomorphic models correctly."""
        iterator = self._create_test_iterator(max_iterations=2)
        
        # Make first model non-isomorphic, second isomorphic
        iterator.isomorphism_checker.check_isomorphism = Mock(
            side_effect=[(False, None), (True, Mock()), (False, None)]  # First non-iso, second iso, third non-iso
        )
        
        # Need more models since one will be skipped
        iterator.constraint_generator.get_model = Mock(side_effect=[
            Mock(name=f"model_{i}") for i in range(4)
        ])
        
        gen = iterator.iterate_generator()
        models = list(gen)
        
        # Should only yield non-isomorphic models (1 model - we only need 1 more after initial)
        assert len(models) == 1  # max_iterations=2, initial=1, so only 1 new model needed
        assert len(iterator.model_structures) == 2  # initial + 1 new