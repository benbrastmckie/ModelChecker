"""Tests for ModelIterator implementation.

This module tests the improved iteration flow and model presentation refactoring
based on the constraints.md recommendations.
"""

import pytest
import z3
from unittest.mock import patch, MagicMock

from model_checker.builder.iterate import ModelIterator

class TestModelIterator:
    """Test suite for ModelIterator functionality."""
    
    def setup_method(self):
        """Set up test fixtures before each test method is executed."""
        # Create a mock BuildExample
        self.mock_build_example = MagicMock()
        
        # Create a mock model structure
        self.mock_model_structure = MagicMock()
        self.mock_model_structure.z3_model_status = True
        self.mock_model_structure.z3_model = MagicMock()
        self.mock_model_structure.solver = MagicMock()
        self.mock_model_structure.solver.assertions.return_value = []
        
        # Attach the model structure to the build example
        self.mock_build_example.model_structure = self.mock_model_structure
        
        # Set up settings
        self.mock_build_example.settings = {
            'iterate': 3,
            'max_time': 1.0,
            'check_isomorphism': False,
            'max_attempts': 5,
            'max_escape_attempts': 3
        }
        
        # Create mock semantics
        self.mock_semantics = MagicMock()
        self.mock_model_structure.semantics = self.mock_semantics
        
        # Set up model constraints
        self.mock_model_constraints = MagicMock()
        self.mock_build_example.model_constraints = self.mock_model_constraints
        self.mock_model_constraints.semantics = self.mock_semantics
        
    @patch('model_checker.builder.iterate.z3.Solver')
    def test_initialization(self, mock_solver_class):
        """Test that ModelIterator initializes properly."""
        # Set up the mock solver
        mock_solver = MagicMock()
        mock_solver_class.return_value = mock_solver
        
        # Create iterator
        iterator = ModelIterator(self.mock_build_example)
        
        # Verify initialization
        assert iterator.build_example == self.mock_build_example
        assert iterator.max_iterations == 3
        assert iterator.current_iteration == 1
        assert iterator.distinct_models_found == 1
        assert iterator.checked_model_count == 1
        assert iterator.escape_attempts == 0
        assert len(iterator.found_models) == 1
        assert len(iterator.model_structures) == 1
        
    @patch('model_checker.builder.iterate.z3.Solver')
    def test_reset_iterator(self, mock_solver_class):
        """Test that reset_iterator properly resets all counters and structures."""
        # Set up the mock solver
        mock_solver = MagicMock()
        mock_solver_class.return_value = mock_solver
        
        # Create iterator
        iterator = ModelIterator(self.mock_build_example)
        
        # Modify attributes to test reset
        iterator.current_iteration = 3
        iterator._isomorphic_attempts = 2
        iterator.distinct_models_found = 3
        iterator.checked_model_count = 5
        iterator.escape_attempts = 2
        
        # Add fake models
        iterator.found_models.append(MagicMock())
        iterator.model_structures.append(MagicMock())
        
        # Reset
        iterator.reset_iterator()
        
        # Verify reset
        assert iterator.current_iteration == 1
        assert iterator._isomorphic_attempts == 0
        assert iterator.distinct_models_found == 1
        assert iterator.checked_model_count == 1
        assert iterator.escape_attempts == 0
        assert len(iterator.found_models) == 1
        assert len(iterator.model_structures) == 1
        
    @patch('model_checker.builder.iterate.z3.Solver')
    @patch('model_checker.builder.iterate.time')
    def test_iterate_with_no_additional_models(self, mock_time, mock_solver_class):
        """Test iteration when no additional models are found."""
        # Set up the mock solver
        mock_solver = MagicMock()
        mock_solver_class.return_value = mock_solver
        mock_solver.check.return_value = z3.unsat  # No additional models
        
        # Mock time to avoid timeout
        mock_time.time.return_value = 0
        
        # Create iterator
        iterator = ModelIterator(self.mock_build_example)
        
        # Call iterate
        result = iterator.iterate()
        
        # Should have just the initial model
        assert len(result) == 1
        assert iterator.current_iteration == 1
        assert iterator.distinct_models_found == 1
        assert iterator.checked_model_count == 1
        
    @patch('model_checker.builder.iterate.z3.Solver')
    @patch('model_checker.builder.iterate.time')
    def test_iterate_with_additional_models(self, mock_time, mock_solver_class):
        """Test iteration with additional models found."""
        # Set up the mock solver
        mock_solver = MagicMock()
        mock_solver_class.return_value = mock_solver
        
        # First call returns sat, second returns unsat (to end iteration)
        mock_solver.check.side_effect = [z3.sat, z3.unsat]
        
        # Mock new model
        mock_new_model = MagicMock()
        mock_solver.model.return_value = mock_new_model
        
        # Mock time to avoid timeout
        mock_time.time.return_value = 0
        
        # Create iterator with mocked _build_new_model_structure
        iterator = ModelIterator(self.mock_build_example)
        
        # Mock the model building method
        mock_new_structure = MagicMock()
        mock_new_structure._is_isomorphic = False
        iterator._build_new_model_structure = MagicMock(return_value=mock_new_structure)
        
        # Mock the difference constraint creation
        iterator._create_difference_constraint = MagicMock(return_value=z3.BoolVal(True))
        iterator._create_extended_constraints = MagicMock(return_value=[])
        
        # Call iterate
        result = iterator.iterate()
        
        # Should have found one additional model
        assert len(result) == 2
        assert iterator.current_iteration == 2
        assert iterator.distinct_models_found == 2
        assert iterator.checked_model_count == 2
        
    @patch('model_checker.builder.iterate.z3.Solver')
    @patch('model_checker.builder.iterate.time')
    @patch('model_checker.builder.iterate.HAS_NETWORKX', True)
    def test_iterate_with_isomorphic_models(self, mock_time, mock_solver_class):
        """Test iteration with isomorphic models that should be skipped."""
        # Set up the mock solver
        mock_solver = MagicMock()
        mock_solver_class.return_value = mock_solver
        
        # First two calls return sat, third returns unsat (to end iteration)
        mock_solver.check.side_effect = [z3.sat, z3.sat, z3.unsat]
        
        # Mock new models
        mock_new_model = MagicMock()
        mock_solver.model.return_value = mock_new_model
        
        # Mock time to avoid timeout
        mock_time.time.return_value = 0
        
        # Create iterator with mocked build and isomorphism check
        iterator = ModelIterator(self.mock_build_example)
        iterator.settings['check_isomorphism'] = True
        
        # Set up first model to be isomorphic, second to be non-isomorphic
        mock_iso_structure = MagicMock()
        mock_non_iso_structure = MagicMock()
        
        iterator._build_new_model_structure = MagicMock(side_effect=[mock_iso_structure, mock_non_iso_structure])
        iterator._check_isomorphism = MagicMock(side_effect=[True, False])
        
        # Mock the constraint creation methods
        iterator._create_difference_constraint = MagicMock(return_value=z3.BoolVal(True))
        iterator._create_extended_constraints = MagicMock(return_value=[])
        iterator._create_non_isomorphic_constraint = MagicMock(return_value=z3.BoolVal(True))
        
        # Call iterate
        result = iterator.iterate()
        
        # Should have the initial model, and one additional non-isomorphic model
        # The isomorphic model should be skipped
        assert len(result) == 2
        assert iterator.current_iteration == 2
        assert iterator.distinct_models_found == 2
        assert iterator.checked_model_count == 3  # Initial + 2 checks (1 iso, 1 non-iso)
        
    @patch('model_checker.builder.iterate.z3.Solver')
    @patch('model_checker.builder.iterate.time')
    @patch('model_checker.builder.iterate.HAS_NETWORKX', True)
    def test_escape_from_isomorphic_models(self, mock_time, mock_solver_class):
        """Test escaping from a series of isomorphic models with stronger constraints."""
        # Set up the mock solver
        mock_solver = MagicMock()
        mock_solver_class.return_value = mock_solver
        
        # Mock solver.check to always return sat
        mock_solver.check.return_value = z3.sat
        
        # Mock time to avoid timeout
        mock_time.time.return_value = 0
        
        # Create iterator with settings
        iterator = ModelIterator(self.mock_build_example)
        iterator.settings['check_isomorphism'] = True
        iterator.settings['max_attempts'] = 3
        iterator.settings['max_escape_attempts'] = 2
        
        # Mock structures - first 6 isomorphic, then 1 non-isomorphic
        structures = [MagicMock() for _ in range(8)]
        
        # Set first 6 as isomorphic
        for i in range(6):
            structures[i]._is_isomorphic = True
            
        # Set last one as non-isomorphic
        structures[6]._is_isomorphic = False
        
        # Mock build_new_model_structure to return these structures
        iterator._build_new_model_structure = MagicMock(side_effect=structures)
        
        # Mock _check_isomorphism to return True for first 6, False for last
        check_results = [True] * 6 + [False]
        iterator._check_isomorphism = MagicMock(side_effect=check_results)
        
        # Mock constraint creation methods
        iterator._create_difference_constraint = MagicMock(return_value=z3.BoolVal(True))
        iterator._create_extended_constraints = MagicMock(return_value=[])
        iterator._create_non_isomorphic_constraint = MagicMock(return_value=z3.BoolVal(True))
        iterator._create_stronger_constraint = MagicMock(return_value=z3.BoolVal(True))
        
        # Set max iterations higher to allow for finding the non-isomorphic model
        iterator.max_iterations = 10
        
        # Call iterate, limiting the number of models to try
        result = iterator.iterate()
        
        # Check we called _create_stronger_constraint
        assert iterator._create_stronger_constraint.called
        
        # Verify escape_attempts was tracked
        assert iterator.escape_attempts > 0
        
        # We should have found the non-isomorphic model eventually
        assert iterator.distinct_models_found > 1
        
    @patch('model_checker.builder.iterate.z3.Solver')
    def test_stronger_constraint_creation(self, mock_solver_class):
        """Test the creation of stronger constraints after isomorphism failures."""
        # Set up the mock solver
        mock_solver = MagicMock()
        mock_solver_class.return_value = mock_solver
        
        # Create iterator
        iterator = ModelIterator(self.mock_build_example)
        
        # Mock the model
        mock_model = MagicMock()
        
        # Set up mock semantics and structure
        mock_states = [0, 1, 2, 3, 4]
        mock_world_states = [0, 1, 2]
        
        iterator.build_example.model_structure.all_states = mock_states
        iterator.build_example.model_structure.z3_world_states = mock_world_states
        
        # Mock z3 calls to avoid errors
        with patch('model_checker.builder.iterate.z3.IntVal') as mock_int_val, \
             patch('model_checker.builder.iterate.z3.If') as mock_if, \
             patch('model_checker.builder.iterate.z3.And') as mock_and, \
             patch('model_checker.builder.iterate.z3.Or') as mock_or:
             
            # Set up return values
            mock_int_val.return_value = 0
            mock_if.return_value = 0
            mock_and.return_value = z3.BoolVal(True)
            mock_or.return_value = z3.BoolVal(True)
            
            # Test first escape attempt
            iterator.escape_attempts = 1
            result1 = iterator._create_stronger_constraint(mock_model)
            assert result1 is not None
            assert mock_or.called
            
            # Test second escape attempt (should create stronger constraints)
            iterator.escape_attempts = 2
            result2 = iterator._create_stronger_constraint(mock_model)
            assert result2 is not None
            assert mock_and.called
            
    @patch('model_checker.builder.iterate.z3.Solver')
    def test_settings_validation(self, mock_solver_class):
        """Test validation of iteration settings."""
        # Set up the mock solver
        mock_solver = MagicMock()
        mock_solver_class.return_value = mock_solver
        
        # Test with valid settings
        self.mock_build_example.settings = {
            'iterate': 5,
            'max_attempts': 3,
            'max_escape_attempts': 2,
            'check_isomorphism': True
        }
        
        iterator = ModelIterator(self.mock_build_example)
        settings = iterator.settings
        
        assert settings['iterate'] == 5
        assert settings['max_attempts'] == 3
        assert settings['max_escape_attempts'] == 2
        assert settings['check_isomorphism'] is True
        
        # Test with invalid settings (should use defaults)
        self.mock_build_example.settings = {
            'iterate': 'invalid',
            'max_attempts': -1,
            'max_escape_attempts': 0
        }
        
        iterator = ModelIterator(self.mock_build_example)
        settings = iterator.settings
        
        # Should coerce to integer or use defaults
        assert isinstance(settings['iterate'], int)
        assert settings['max_attempts'] > 0
        assert settings['max_escape_attempts'] > 0


def test_class_exists():
    """Simple test to verify the ModelIterator class exists."""
    assert hasattr(ModelIterator, 'iterate')
    assert hasattr(ModelIterator, '_create_stronger_constraint')
    assert hasattr(ModelIterator, 'reset_iterator')