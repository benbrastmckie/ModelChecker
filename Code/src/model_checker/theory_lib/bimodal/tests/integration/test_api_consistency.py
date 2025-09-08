"""
Tests for API consistency in bimodal theory.

This module tests the consistency of method signatures across the bimodal theory
implementation to ensure proper parameter passing and API usage.
"""

import inspect
import pytest
from model_checker.theory_lib.bimodal import (
    BimodalSemantics,
    BimodalProposition,
    bimodal_operators,
)
from model_checker.syntactic import Operator, DefinedOperator

def test_find_truth_condition_consistency():
    """Test that find_truth_condition methods have consistent parameters across operators."""
    
    # Check each operator in the bimodal_operators collection
    for operator_name, operator_class in bimodal_operators.operator_dictionary.items():
        # Skip DefinedOperators as they use the derived implementation
        if issubclass(operator_class, DefinedOperator):
            continue
            
        if issubclass(operator_class, Operator) and hasattr(operator_class, 'find_truth_condition'):
            # Get the method signature
            signature = inspect.signature(operator_class.find_truth_condition)
            parameters = list(signature.parameters.keys())
            
            # First parameter should be 'self'
            assert parameters[0] == 'self', f"First parameter of {operator_class.__name__}.find_truth_condition should be 'self'"
            
            # The eval_point should be the last parameter (after self and arguments)
            assert parameters[-1] == 'eval_point', (
                f"In {operator_class.__name__}.find_truth_condition, eval_point should be the last parameter. "
                f"Current parameters: {parameters}"
            )

def test_bimodal_proposition_extension_correct_args():
    """Test that BimodalProposition.find_extension is using eval_point dictionary."""
    
    # Get the source code of the find_extension method
    source = inspect.getsource(BimodalProposition.find_extension)
    
    # Check that it creates and uses an eval_point dictionary
    assert "eval_point = {" in source or "eval_point={" in source, (
        "BimodalProposition.find_extension should create an eval_point dictionary"
    )
    
    # Check that it passes eval_point to find_truth_condition
    assert "self.operator.find_truth_condition(*arguments, eval_point)" in source, (
        "BimodalProposition.find_extension should pass eval_point to find_truth_condition"
    )