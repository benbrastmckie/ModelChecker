"""Simple tests for logos theory model iteration."""

import pytest
from model_checker.theory_lib.logos import (
    LogosSemantics, LogosProposition, LogosModelStructure, 
    LogosOperatorRegistry, iterate_example, LogosModelIterator
)
from model_checker.builder.example import BuildExample
from model_checker.builder.module import BuildModule
from unittest.mock import Mock, MagicMock
from types import SimpleNamespace


class TestLogosIterator:
    """Simple test cases for logos theory iteration."""
    
    def test_basic_iteration(self):
        """Test that iteration works with logos theory."""
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
        
        # Create operator registry
        logos_registry = LogosOperatorRegistry()
        logos_registry.load_subtheories(['extensional', 'modal'])
        
        # Create semantic theory
        semantic_theory = {
            "semantics": LogosSemantics,
            "proposition": LogosProposition,
            "model": LogosModelStructure,
            "operators": logos_registry.get_operators(),
        }
        
        # Create example case
        example_case = [
            [],  # premises
            ["A"],  # conclusions - simple atomic formula
            {'N': 2, 'iterate': 2}  # settings
        ]
        
        # Create build example
        example = BuildExample(mock_module, semantic_theory, example_case)
        
        # Test that the iterator can be created
        iterator = LogosModelIterator(example)
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
        
        # Create operator registry
        logos_registry = LogosOperatorRegistry()
        logos_registry.load_subtheories(['extensional'])
        
        # Create semantic theory
        semantic_theory = {
            "semantics": LogosSemantics,
            "proposition": LogosProposition,
            "model": LogosModelStructure,
            "operators": logos_registry.get_operators(),
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
    
    def test_difference_detection(self):
        """Test that differences are properly detected between models."""
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
        
        # Create operator registry
        logos_registry = LogosOperatorRegistry()
        logos_registry.load_subtheories(['extensional'])
        
        # Create semantic theory
        semantic_theory = {
            "semantics": LogosSemantics,
            "proposition": LogosProposition,
            "model": LogosModelStructure,
            "operators": logos_registry.get_operators(),
        }
        
        # Create example case
        example_case = [
            [],  # premises
            ["\\neg A"],  # conclusions - use negation operator
            {'N': 2, 'iterate': 2}  # settings with iteration
        ]
        
        # Create build example
        example = BuildExample(mock_module, semantic_theory, example_case)
        
        # Use iterate_example to find models
        models = iterate_example(example)
        
        # Check second model has differences if multiple models found
        if len(models) > 1:
            second_model = models[1]
            assert hasattr(second_model, 'model_differences')
            assert second_model.model_differences is not None