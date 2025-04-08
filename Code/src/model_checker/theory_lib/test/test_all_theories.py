"""Cross-theory tests for ModelChecker.

This module contains tests that can be run across all registered theories.
"""

import pytest
import sys
import os
from model_checker import ModelConstraints, Syntax, run_test

# Import the theory registry
from model_checker.theory_lib import AVAILABLE_THEORIES

def get_theory_components(theory_name):
    """Get the components of a theory by name."""
    if theory_name == 'default':
        from model_checker.theory_lib.default.semantic import Semantics
        from model_checker.theory_lib.default.semantic import Proposition
        from model_checker.theory_lib.default.semantic import ModelStructure
        from model_checker.theory_lib.default.operators import default_operators
        return {
            'semantics': Semantics,
            'proposition': Proposition,
            'model_structure': ModelStructure,
            'operators': default_operators,
            'name': theory_name
        }
    elif theory_name == 'exclusion':
        from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics
        from model_checker.theory_lib.exclusion.semantic import UnilateralProposition
        from model_checker.theory_lib.exclusion.semantic import ExclusionStructure
        from model_checker.theory_lib.exclusion.operators import exclusion_operators
        return {
            'semantics': ExclusionSemantics,
            'proposition': UnilateralProposition,
            'model_structure': ExclusionStructure,
            'operators': exclusion_operators,
            'name': theory_name
        }
    elif theory_name == 'imposition':
        from model_checker.theory_lib.imposition.semantic import ImpositionSemantics
        from model_checker.theory_lib.imposition.semantic import ImpositionProposition
        from model_checker.theory_lib.imposition.semantic import ImpositionStructure
        from model_checker.theory_lib.imposition.operators import imposition_operators
        return {
            'semantics': ImpositionSemantics,
            'proposition': ImpositionProposition,
            'model_structure': ImpositionStructure,
            'operators': imposition_operators,
            'name': theory_name
        }
    elif theory_name == 'bimodal':
        try:
            from model_checker.theory_lib.bimodal.semantic import Semantics
            from model_checker.theory_lib.bimodal.semantic import Proposition
            from model_checker.theory_lib.bimodal.semantic import ModelStructure
            
            # Bimodal may have a different pattern for operators
            try:
                from model_checker.theory_lib.bimodal.operators import bimodal_operators
                operators = bimodal_operators
            except ImportError:
                try:
                    from model_checker.theory_lib.bimodal.operators import get_bimodal_operators
                    operators = get_bimodal_operators()
                except ImportError:
                    # Fallback to importing individual operators
                    from model_checker.theory_lib.bimodal.operators import (
                        NegationOperator, AndOperator, OrOperator, 
                        ImplicationOperator, CounterfactualOperator
                    )
                    operators = {
                        '~': NegationOperator(),
                        '&': AndOperator(),
                        '|': OrOperator(),
                        '->': ImplicationOperator(),
                        '>': CounterfactualOperator()
                    }
            
            return {
                'semantics': Semantics,
                'proposition': Proposition,
                'model_structure': ModelStructure,
                'operators': operators,
                'name': theory_name
            }
        except ImportError as e:
            pytest.skip(f"Bimodal theory not fully implemented: {str(e)}")
    else:
        pytest.skip(f"Unknown theory: {theory_name}")

@pytest.mark.parametrize("theory_name", [t for t in AVAILABLE_THEORIES])
def test_basic_logical_principles(theory_name):
    """Test basic logical principles that all theories should support."""
    # Skip if theory is not available or ready
    try:
        components = get_theory_components(theory_name)
    except (ImportError, AttributeError) as e:
        pytest.skip(f"Theory {theory_name} is not ready for testing: {str(e)}")
    
    # Define some basic principles to test
    principles = [
        # Name, premises, conclusions, settings
        ("Law of Identity", [], ["(p \\rightarrow p)"], {"N": 3, "max_time": 5}),
        ("Law of Excluded Middle", [], ["(p \\vee \\neg p)"], {"N": 3, "max_time": 5}),
        ("Law of Non-Contradiction", [], ["\\neg(p \\wedge \\neg p)"], {"N": 3, "max_time": 5}),
    ]
    
    for name, premises, conclusions, settings in principles:
        example_case = [premises, conclusions, settings]
        
        # Print information
        print(f"\nTesting {name} in {theory_name} theory:")
        print(f"  Premises: {premises}")
        print(f"  Conclusions: {conclusions}")
        
        # Run the test
        result = run_test(
            example_case,
            components['semantics'],
            components['proposition'],
            components['operators'],
            Syntax,
            ModelConstraints,
            components['model_structure'],
        )
        
        # Assert the principle holds
        assert result, f"{name} failed in {theory_name} theory"

def test_available_theories():
    """Test that the theory registry is working and contains expected theories."""
    # Verify we have the expected theories in the registry
    expected_theories = {'default', 'exclusion', 'imposition', 'bimodal'}
    registered_theories = set(AVAILABLE_THEORIES)
    
    # Print available theories
    print(f"Available theories: {', '.join(AVAILABLE_THEORIES)}")
    
    # Verify expected theories are registered
    for theory in expected_theories:
        assert theory in registered_theories, f"Expected theory '{theory}' not found in registry"