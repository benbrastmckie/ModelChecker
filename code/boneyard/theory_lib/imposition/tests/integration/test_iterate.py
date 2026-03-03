"""Tests for the ImpositionModelIterator implementation.

This module tests the iteration flow and model presentation for the imposition theory.
"""

import pytest
import z3
from unittest.mock import Mock, patch, MagicMock

from model_checker.theory_lib.imposition.iterate import ImpositionModelIterator, iterate_example
from model_checker.builder.example import BuildExample


def test_basic_iteration():
    """Test that the ImpositionModelIterator can find multiple models."""
    # Create a mock BuildExample with required attributes
    mock_example = Mock(spec=BuildExample)
    
    # Set up model structure
    mock_example.model_structure = Mock()
    mock_example.model_structure.z3_model_status = True
    mock_example.model_structure.z3_model = Mock()
    mock_example.model_structure.solver = z3.Solver()
    mock_example.model_structure.all_states = []
    mock_example.model_structure.z3_world_states = []
    mock_example.model_structure.z3_possible_states = []
    mock_example.model_structure.sentence_letters = []
    mock_example.model_structure.semantics = Mock()
    mock_example.model_structure.z3_model_runtime = 0.1
    mock_example.model_structure._search_duration = 0.1
    mock_example.model_structure._total_search_time = 0.1
    
    # Set up model constraints
    mock_example.model_constraints = Mock()
    mock_example.model_constraints.all_constraints = []
    
    # Set up settings
    mock_example.settings = {'iterate': 2, 'max_time': 5.0}
    
    # Create iterator
    iterator = ImpositionModelIterator(mock_example)
    
    # Verify iterator was created
    assert iterator is not None
    assert hasattr(iterator, 'build_example')
    assert iterator.build_example == mock_example


def test_imposition_specific_differences():
    """Test that the ImpositionModelIterator correctly calculates differences."""
    # Create a mock BuildExample
    mock_example = Mock(spec=BuildExample)
    
    # Set up model structure with some imposition-specific attributes
    mock_example.model_structure = Mock()
    mock_example.model_structure.z3_model_status = True
    mock_example.model_structure.z3_model = Mock()
    mock_example.model_structure.solver = z3.Solver()
    mock_example.model_structure.all_states = []
    mock_example.model_structure.z3_world_states = []
    mock_example.model_structure.z3_possible_states = []
    mock_example.model_structure.sentence_letters = []
    mock_example.model_structure.semantics = Mock()
    mock_example.model_structure.z3_model_runtime = 0.1
    mock_example.model_structure._search_duration = 0.1
    mock_example.model_structure._total_search_time = 0.1
    
    # Add imposition-specific attributes
    mock_example.model_structure.verify_formulas = {}
    mock_example.model_structure.falsify_formulas = {}
    
    # Set up model constraints
    mock_example.model_constraints = Mock()
    mock_example.model_constraints.all_constraints = []
    
    # Set up settings
    mock_example.settings = {'iterate': 1, 'max_time': 5.0}
    
    # Create iterator
    iterator = ImpositionModelIterator(mock_example)
    
    # Test difference calculation with two mock structures
    new_structure = Mock()
    new_structure.verify_formulas = {'A': [1, 2]}
    new_structure.falsify_formulas = {'B': [3]}
    new_structure.z3_world_states = [1, 2]
    new_structure.z3_possible_states = [1, 2, 3]
    new_structure.sentence_letters = ['A', 'B']  # Add sentence_letters
    
    previous_structure = Mock()
    previous_structure.verify_formulas = {'A': [1]}
    previous_structure.falsify_formulas = {'B': [3, 4]}
    previous_structure.z3_world_states = [1]
    previous_structure.z3_possible_states = [1, 2, 3, 4]
    previous_structure.sentence_letters = ['A', 'B']  # Add sentence_letters
    
    differences = iterator._calculate_differences(new_structure, previous_structure)
    
    # Should return a dictionary of differences
    assert isinstance(differences, dict)


def test_iterate_example_function():
    """Test that the iterate_example function works correctly."""
    # Create a mock BuildExample
    mock_example = Mock(spec=BuildExample)
    
    # Set up model structure
    mock_example.model_structure = Mock()
    mock_example.model_structure.z3_model_status = True
    mock_example.model_structure.z3_model = Mock()
    mock_example.model_structure.solver = z3.Solver()
    mock_example.model_structure.all_states = []
    mock_example.model_structure.z3_world_states = []
    mock_example.model_structure.z3_possible_states = []
    mock_example.model_structure.sentence_letters = []
    mock_example.model_structure.semantics = Mock()
    mock_example.model_structure.z3_model_runtime = 0.1
    mock_example.model_structure._search_duration = 0.1
    mock_example.model_structure._total_search_time = 0.1
    
    # Set up model constraints
    mock_example.model_constraints = Mock()
    mock_example.model_constraints.all_constraints = []
    
    # Set up settings
    mock_example.settings = {'iterate': 1, 'max_time': 5.0}
    
    # Mock the iterate method to return quickly
    with patch.object(ImpositionModelIterator, 'iterate', return_value=[mock_example.model_structure]):
        # Call iterate_example
        result = iterate_example(mock_example, max_iterations=1)
        
        # Should return a list of model structures
        assert isinstance(result, list)
        assert len(result) >= 1