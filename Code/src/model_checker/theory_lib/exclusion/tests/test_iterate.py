"""Simple tests for exclusion theory model iteration."""

import pytest
from model_checker.theory_lib.exclusion import (
    WitnessSemantics, WitnessProposition, WitnessStructure, 
    witness_operators, iterate_example, ExclusionModelIterator
)
from model_checker.builder.example import BuildExample
from model_checker.builder.module import BuildModule
from unittest.mock import Mock, MagicMock
from types import SimpleNamespace


class TestExclusionIterator:
    """Simple test cases for exclusion theory iteration."""
    
    def test_basic_iteration(self):
        """Test that iteration works with exclusion theory."""
        # Create a mock build module
        mock_module = Mock()
        mock_module.general_settings = {
            'N': 3,
            'contingent': False,
            'disjoint': False,
            'non_empty': True,
            'non_null': True,
            'print_constraints': False,
            'save_output': False,
            'print_impossible': False,
            'print_z3': False,
            'max_time': 1
        }
        mock_module.module_flags = SimpleNamespace(
            contingent=False,
            disjoint=False,
            non_empty=False,
            non_null=False,
            print_constraints=False,
            save_output=False,
            print_impossible=False,
            print_z3=False,
            maximize=False
        )
        
        # Create semantic theory
        semantic_theory = {
            "semantics": WitnessSemantics,
            "proposition": WitnessProposition,
            "model": WitnessStructure,
            "operators": witness_operators,
        }
        
        # Create example case
        example_case = [
            [],  # premises
            ["\\func_unineg A"],  # conclusions
            {'N': 3, 'iterate': 2}  # settings
        ]
        
        # Create build example
        example = BuildExample(mock_module, semantic_theory, example_case)
        
        # Test that the iterator can be created
        iterator = ExclusionModelIterator(example)
        assert iterator is not None
        assert hasattr(iterator, 'iterate')
        
    def test_iterate_example_function(self):
        """Test the iterate_example convenience function."""
        # Create a mock build module
        mock_module = Mock()
        mock_module.general_settings = {
            'N': 2,
            'contingent': False,
            'disjoint': False,
            'non_empty': True,
            'non_null': True,
            'print_constraints': False,
            'save_output': False,
            'print_impossible': False,
            'print_z3': False,
            'max_time': 1
        }
        mock_module.module_flags = SimpleNamespace(
            contingent=False,
            disjoint=False,
            non_empty=False,
            non_null=False,
            print_constraints=False,
            save_output=False,
            print_impossible=False,
            print_z3=False,
            maximize=False
        )
        
        # Create semantic theory
        semantic_theory = {
            "semantics": WitnessSemantics,
            "proposition": WitnessProposition,
            "model": WitnessStructure,
            "operators": witness_operators,
        }
        
        # Create example case - use a formula that should have multiple models
        example_case = [
            [],  # premises
            ["A"],  # conclusions - simple atomic formula
            {'N': 2}  # settings without iterate
        ]
        
        # Create build example
        example = BuildExample(mock_module, semantic_theory, example_case)
        
        # Use iterate_example to find models
        models = iterate_example(example, max_iterations=2)
        
        # Should find at least one model
        assert len(models) >= 1
        assert hasattr(example, '_iterator')