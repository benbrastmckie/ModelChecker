"""
Test exclusion theory examples.

This module tests that the exclusion theory examples run correctly
and produce expected results.
"""

import pytest
from model_checker import (
    ModelConstraints,
    Syntax,
    run_test,
)
from model_checker.theory_lib.exclusion import examples
from model_checker.theory_lib.exclusion.semantic import (
    WitnessSemantics,
    WitnessProposition,
    WitnessStructure,
)
from model_checker.theory_lib.exclusion.operators import witness_operators


class TestExclusionExamples:
    """Test exclusion theory example implementations."""
    
    def test_examples_module_exists(self):
        """Test that examples module exists and has expected structure."""
        assert hasattr(examples, 'example_range')
        assert hasattr(examples, 'semantic_theories')
        assert hasattr(examples, 'unit_tests')
        assert hasattr(examples, 'test_example_range')
        
    def test_example_structure(self):
        """Test that examples have proper structure."""
        example_range = examples.example_range
        
        # Should have at least some examples
        assert len(example_range) > 0
        
        # Check example structure
        for name, example_data in example_range.items():
            assert isinstance(example_data, list)
            assert len(example_data) == 3
            premises, conclusions, settings = example_data
            assert isinstance(premises, list)
            assert isinstance(conclusions, list)
            assert isinstance(settings, dict)


# Create parameterized tests for all examples
@pytest.mark.parametrize("example_name, example_case", examples.unit_tests.items())
def test_exclusion_examples(example_name, example_case):
    """Test each exclusion example case."""
    
    result = run_test(
        example_case,
        WitnessSemantics,
        WitnessProposition,
        witness_operators,
        Syntax,
        ModelConstraints,
        WitnessStructure,
    )
    
    # The run_test function returns True if the model matches expectations, False otherwise
    assert result, f"Test failed for example: {example_name}. Model result did not match expectation value in settings."


if __name__ == "__main__":
    pytest.main([__file__])