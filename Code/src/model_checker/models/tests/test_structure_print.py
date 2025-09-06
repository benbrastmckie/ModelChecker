"""Tests for print methods in ModelDefaults structure.

This module tests the print_all() method and its helper methods
that were added/refactored during the models package refactor.
"""

import io
import sys
from unittest.mock import Mock, MagicMock, patch

import pytest

from model_checker.models.structure import ModelDefaults


class TestPrintAllMethod:
    """Test the print_all() method and its components."""
    
    @pytest.fixture
    def mock_model(self):
        """Create a mock ModelDefaults instance for testing."""
        model = Mock(spec=ModelDefaults)
        model.z3_model = Mock()  # Valid Z3 model
        model.settings = {'print_z3': False}
        model.premises = []
        model.conclusions = []
        model.model_constraints = Mock()
        model.model_constraints.all_constraints = []
        model.model_constraints.frame_constraints = []
        model.model_constraints.model_constraints = []
        model.model_constraints.premise_constraints = []
        model.model_constraints.conclusion_constraints = []
        return model
    
    def test_print_all_calls_required_methods(self, mock_model):
        """Test that print_all calls the required print methods."""
        buffer = io.StringIO()
        
        # Mock the methods that print_all should call
        mock_model.print_input_sentences = Mock()
        mock_model.print_grouped_constraints = Mock()
        mock_model.print_model = Mock()
        
        # Call the actual print_all method
        ModelDefaults.print_all(mock_model, output=buffer)
        
        # Verify the methods were called
        mock_model.print_input_sentences.assert_called_once_with(buffer)
        mock_model.print_grouped_constraints.assert_called_once_with(buffer)
        mock_model.print_model.assert_called_once_with(buffer)
    
    def test_print_all_with_default_output(self, mock_model):
        """Test print_all with default sys.stdout output."""
        mock_model.print_input_sentences = Mock()
        mock_model.print_grouped_constraints = Mock()
        mock_model.print_model = Mock()
        
        # Call without specifying output
        ModelDefaults.print_all(mock_model)
        
        # Should use sys.stdout by default
        mock_model.print_input_sentences.assert_called_once_with(sys.stdout)
        mock_model.print_grouped_constraints.assert_called_once_with(sys.stdout)
        mock_model.print_model.assert_called_once_with(sys.stdout)


class TestPrintHelperMethods:
    """Test the extracted helper methods for constraint printing."""
    
    @pytest.fixture
    def mock_model(self):
        """Create a mock ModelDefaults with constraint setup."""
        model = Mock(spec=ModelDefaults)
        model.z3_model = Mock()
        model.unsat_core = None
        model.constraint_dict = {}
        
        # Setup model_constraints
        model.model_constraints = Mock()
        model.model_constraints.all_constraints = ['c1', 'c2', 'c3']
        model.model_constraints.frame_constraints = ['c1']
        model.model_constraints.model_constraints = ['c2']
        model.model_constraints.premise_constraints = ['c3']
        model.model_constraints.conclusion_constraints = []
        
        return model
    
    def test_get_relevant_constraints_satisfiable(self, mock_model):
        """Test _get_relevant_constraints when model is satisfiable."""
        buffer = io.StringIO()
        
        constraints = ModelDefaults._get_relevant_constraints(mock_model, buffer)
        
        assert constraints == ['c1', 'c2', 'c3']
        assert "SATISFIABLE CONSTRAINTS:" in buffer.getvalue()
    
    def test_get_relevant_constraints_unsatisfiable(self, mock_model):
        """Test _get_relevant_constraints when model is unsatisfiable."""
        mock_model.z3_model = None
        mock_model.unsat_core = ['core1', 'core2']
        mock_model.constraint_dict = {
            'core1': 'constraint1',
            'core2': 'constraint2'
        }
        buffer = io.StringIO()
        
        constraints = ModelDefaults._get_relevant_constraints(mock_model, buffer)
        
        assert constraints == ['constraint1', 'constraint2']
        assert "UNSATISFIABLE CORE CONSTRAINTS:" in buffer.getvalue()
    
    def test_get_relevant_constraints_no_model(self, mock_model):
        """Test _get_relevant_constraints with no model or unsat core."""
        mock_model.z3_model = None
        mock_model.unsat_core = None
        buffer = io.StringIO()
        
        constraints = ModelDefaults._get_relevant_constraints(mock_model, buffer)
        
        assert constraints == []
        assert "NO CONSTRAINTS AVAILABLE" in buffer.getvalue()
    
    def test_print_constraint_summary(self, mock_model):
        """Test _print_constraint_summary output format."""
        buffer = io.StringIO()
        constraints = ['c1', 'c2', 'c3']
        
        ModelDefaults._print_constraint_summary(mock_model, constraints, buffer)
        
        output = buffer.getvalue()
        assert "Frame constraints: 1" in output
        assert "Model constraints: 1" in output
        assert "Premise constraints: 1" in output
        assert "Conclusion constraints: 0" in output
    
    def test_organize_constraint_groups(self, mock_model):
        """Test _organize_constraint_groups categorization."""
        constraints = ['c1', 'c2', 'c3']
        
        groups = ModelDefaults._organize_constraint_groups(mock_model, constraints)
        
        assert groups == {
            'FRAME': ['c1'],
            'MODEL': ['c2'],
            'PREMISES': ['c3'],
            'CONCLUSIONS': []
        }
    
    def test_print_constraint_groups(self, mock_model):
        """Test _print_constraint_groups formatting."""
        buffer = io.StringIO()
        groups = {
            'FRAME': ['frame_constraint'],
            'MODEL': ['model_constraint'],
            'PREMISES': [],
            'CONCLUSIONS': []
        }
        
        ModelDefaults._print_constraint_groups(mock_model, groups, buffer)
        
        output = buffer.getvalue()
        assert "FRAME CONSTRAINTS:" in output
        assert "1. frame_constraint" in output
        assert "MODEL CONSTRAINTS:" in output
        assert "1. model_constraint" in output
        # Empty groups should not be printed
        assert "PREMISES CONSTRAINTS:" not in output
        assert "CONCLUSIONS CONSTRAINTS:" not in output


class TestSentencePrintHelpers:
    """Test the sentence printing helper methods."""
    
    @pytest.fixture
    def mock_model(self):
        """Create a mock ModelDefaults with sentence setup."""
        model = Mock(spec=ModelDefaults)
        model.z3_model = Mock()
        model.main_point = {'state': 0}
        
        # Create mock sentences
        premise = Mock()
        premise.sentence_letter = 'A'
        conclusion = Mock()
        conclusion.sentence_letter = 'B'
        
        model.premises = [premise]
        model.conclusions = [conclusion]
        model.recursive_print = Mock()
        
        return model
    
    def test_print_sentence_group_singular_title(self, mock_model):
        """Test _print_sentence_group with single sentence."""
        buffer = io.StringIO()
        sentences = [Mock()]
        
        ModelDefaults._print_sentence_group(
            mock_model,
            "SINGLE:",
            "MULTIPLE:",
            sentences,
            1,
            buffer
        )
        
        output = buffer.getvalue()
        assert "SINGLE:" in output
        assert "MULTIPLE:" not in output
        assert "1." in output
    
    def test_print_sentence_group_plural_title(self, mock_model):
        """Test _print_sentence_group with multiple sentences."""
        buffer = io.StringIO()
        sentences = [Mock(), Mock()]
        
        ModelDefaults._print_sentence_group(
            mock_model,
            "SINGLE:",
            "MULTIPLE:",
            sentences,
            1,
            buffer
        )
        
        output = buffer.getvalue()
        assert "SINGLE:" not in output
        assert "MULTIPLE:" in output
        assert "1." in output
        assert "2." in output
    
    def test_print_sentence_group_empty(self, mock_model):
        """Test _print_sentence_group with no sentences."""
        buffer = io.StringIO()
        sentences = []
        
        ModelDefaults._print_sentence_group(
            mock_model,
            "SINGLE:",
            "MULTIPLE:",
            sentences,
            1,
            buffer
        )
        
        # Should print nothing for empty sentence list
        assert buffer.getvalue() == ""


class TestModelDifferenceHelpers:
    """Test the model difference printing helper methods."""
    
    @pytest.fixture
    def mock_model(self):
        """Create a mock ModelDefaults with differences."""
        model = Mock(spec=ModelDefaults)
        model.model_differences = {
            'sentence_letters': {
                'A': {'old': True, 'new': False},
                'B': {'old': False, 'new': True}
            },
            'semantic_functions': {
                'verify': {
                    '(0, A)': {'old': True, 'new': False}
                }
            },
            'model_structure': {
                'worlds': {'old': 2, 'new': 3}
            }
        }
        model.z3_world_states = [0, 1, 2]
        return model
    
    def test_print_sentence_letter_differences(self, mock_model):
        """Test _print_sentence_letter_differences output."""
        buffer = io.StringIO()
        
        ModelDefaults._print_sentence_letter_differences(mock_model, buffer)
        
        output = buffer.getvalue()
        assert "Sentence Letter Changes:" in output
        assert "A: True → False" in output
        assert "B: False → True" in output
    
    def test_print_semantic_function_differences(self, mock_model):
        """Test _print_semantic_function_differences output."""
        buffer = io.StringIO()
        
        ModelDefaults._print_semantic_function_differences(mock_model, buffer)
        
        output = buffer.getvalue()
        assert "Semantic Function Changes:" in output
        assert "verify:" in output
        assert "Input (0, A): True → False" in output
    
    def test_print_model_structure_differences(self, mock_model):
        """Test _print_model_structure_differences output."""
        buffer = io.StringIO()
        
        ModelDefaults._print_model_structure_differences(mock_model, buffer)
        
        output = buffer.getvalue()
        assert "Model Structure Changes:" in output
        assert "worlds: 2 → 3" in output
    
    def test_print_structural_metrics(self, mock_model):
        """Test _print_structural_metrics output."""
        buffer = io.StringIO()
        
        ModelDefaults._print_structural_metrics(mock_model, buffer)
        
        output = buffer.getvalue()
        assert "Structural Properties:" in output
        assert "Worlds: 3" in output