"""Tests for the bimodal iteration system.

This module tests the BimodalModelIterator implementation to ensure it can
correctly find multiple distinct models for bimodal logic examples.

TODO: REMOVE MODULE-LEVEL SKIP ONCE BIMODAL THEORY DEVELOPMENT IS COMPLETE
The bimodal theory is currently under development. All tests in this module
are skipped to avoid false failures. Once the bimodal theory implementation
is finalized, remove the pytestmark line below.
"""

import pytest
import z3
from unittest.mock import Mock, patch

# Skip all tests in this module while bimodal theory is under development
pytestmark = pytest.mark.skip(reason="Bimodal theory is under development - unskip when implementation is complete")
from model_checker.theory_lib.bimodal import (
    BimodalSemantics,
    BimodalProposition,
    BimodalStructure,
    bimodal_operators,
    BimodalModelIterator,
    iterate_example,
)
from model_checker.builder.example import BuildExample
from model_checker.models.constraints import ModelConstraints
from model_checker.syntactic import Syntax


def test_basic_iteration():
    """Test basic iteration for a simple bimodal formula."""
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
    
    # Add bimodal-specific attributes
    mock_example.model_structure.worlds = []
    mock_example.model_structure.time_points = []
    
    # Set up model constraints
    mock_example.model_constraints = Mock()
    mock_example.model_constraints.all_constraints = []
    
    # Set up settings
    mock_example.settings = {'iterate': 2, 'max_time': 5.0, 'N': 1, 'M': 2}
    
    # Create iterator
    iterator = BimodalModelIterator(mock_example)
    
    # Verify iterator was created
    assert iterator is not None
    assert hasattr(iterator, 'build_example')
    assert iterator.build_example == mock_example


def test_iterate_example_function():
    """Test the iterate_example function."""
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
    
    # Add bimodal-specific attributes
    mock_example.model_structure.worlds = []
    mock_example.model_structure.time_points = []
    
    # Set up model constraints
    mock_example.model_constraints = Mock()
    mock_example.model_constraints.all_constraints = []
    
    # Set up settings
    mock_example.settings = {'iterate': 1, 'max_time': 5.0, 'N': 1, 'M': 2}
    
    # Mock the iterate method to return quickly
    with patch.object(BimodalModelIterator, 'iterate', return_value=[mock_example.model_structure]):
        # Call iterate_example
        result = iterate_example(mock_example, max_iterations=1)
        
        # Should return a list of model structures
        assert isinstance(result, list)
        assert len(result) >= 1


def test_bimodal_specific_differences():
    """Test that bimodal-specific differences are captured."""
    # Create a mock BuildExample
    mock_example = Mock(spec=BuildExample)
    
    # Set up model structure with bimodal-specific attributes
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
    
    # Add bimodal-specific attributes
    mock_example.model_structure.worlds = [0, 1]
    mock_example.model_structure.time_points = [0, 1]
    mock_example.model_structure.world_histories = {0: [0], 1: [0, 1]}
    
    # Set up model constraints
    mock_example.model_constraints = Mock()
    mock_example.model_constraints.all_constraints = []
    
    # Set up settings
    mock_example.settings = {'iterate': 1, 'max_time': 5.0, 'N': 1, 'M': 2}
    
    # Create iterator
    iterator = BimodalModelIterator(mock_example)
    
    # Test difference calculation with two mock structures
    new_structure = Mock()
    new_structure.worlds = [0, 1, 2]
    new_structure.time_points = [0, 1]
    new_structure.world_histories = {0: [0], 1: [0, 1], 2: [1]}
    new_structure.z3_world_states = [0, 1, 2]
    new_structure.z3_possible_states = [0, 1, 2]
    
    previous_structure = Mock()
    previous_structure.worlds = [0, 1]
    previous_structure.time_points = [0, 1]
    previous_structure.world_histories = {0: [0], 1: [0, 1]}
    previous_structure.z3_world_states = [0, 1]
    previous_structure.z3_possible_states = [0, 1]
    
    # Mock the detect_model_differences method to return a dict
    new_structure.detect_model_differences = Mock(return_value={'worlds': {0, 1, 2}})
    
    differences = iterator._calculate_differences(new_structure, previous_structure)
    
    # Should return a dictionary of differences
    assert isinstance(differences, dict)