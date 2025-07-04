#!/usr/bin/env python3
"""
Test the simplified modules before integration.
"""

import sys
from pathlib import Path

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

# Import the simplified modules
from model_checker.theory_lib.exclusion.operators_simplified import exclusion_operators
from model_checker.theory_lib.exclusion.semantic_simplified import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure
)
from model_checker.syntactic import Syntax
from model_checker.model import ModelConstraints

def test_basic_example():
    """Test a basic example with the simplified modules."""
    print("Testing simplified modules with basic example...")
    print("=" * 50)
    
    # Simple example: A, therefore not not A
    premises = ["A"]
    conclusions = ["\\exclude \\exclude A"]
    
    settings = {
        'N': 2,
        'contingent': True,
        'non_null': True,
    }
    
    # Create semantics
    combined_settings = {**ExclusionSemantics.DEFAULT_EXAMPLE_SETTINGS, **settings}
    semantics = ExclusionSemantics(combined_settings)
    
    # Create syntax
    syntax = Syntax(premises, conclusions, exclusion_operators)
    
    # Create model constraints
    constraints = ModelConstraints(combined_settings, syntax, semantics, UnilateralProposition)
    
    # Create structure
    structure = ExclusionStructure(constraints, combined_settings)
    
    # Check if model was found
    print(f"Model found: {structure.z3_model_status}")
    
    if structure.z3_model_status:
        # Check premise truth
        for i, premise in enumerate(syntax.premises):
            prop = UnilateralProposition(premise, structure)
            truth = prop.evaluate()
            print(f"Premise {i+1} '{premise}' is {truth}")
            
        # Check conclusion truth
        for i, conclusion in enumerate(syntax.conclusions):
            prop = UnilateralProposition(conclusion, structure)
            truth = prop.evaluate()
            print(f"Conclusion {i+1} '{conclusion}' is {truth}")
            
        # Check operator type
        print(f"\nExclusion operator type: {type(exclusion_operators['\\exclude']).__name__}")
        
    print("\nSimplified modules test complete!")

def test_problematic_example():
    """Test DN_ELIM which has false premise issues."""
    print("\n\nTesting DN_ELIM example...")
    print("=" * 50)
    
    premises = ["\\exclude \\exclude A"]
    conclusions = ["A"]
    
    settings = {
        'N': 3,
        'contingent': True,
        'non_null': True,
    }
    
    # Create semantics
    combined_settings = {**ExclusionSemantics.DEFAULT_EXAMPLE_SETTINGS, **settings}
    semantics = ExclusionSemantics(combined_settings)
    
    # Create syntax
    syntax = Syntax(premises, conclusions, exclusion_operators)
    
    # Create model constraints
    constraints = ModelConstraints(combined_settings, syntax, semantics, UnilateralProposition)
    
    # Create structure
    structure = ExclusionStructure(constraints, combined_settings)
    
    # Check if model was found
    print(f"Model found: {structure.z3_model_status}")
    
    if structure.z3_model_status:
        # Check premise truth
        for i, premise in enumerate(syntax.premises):
            prop = UnilateralProposition(premise, structure)
            truth = prop.evaluate()
            print(f"Premise {i+1} '{premise}' is {truth}")
            if not truth:
                print("  ⚠️  FALSE PREMISE DETECTED!")
            
        # Check conclusion truth
        for i, conclusion in enumerate(syntax.conclusions):
            prop = UnilateralProposition(conclusion, structure)
            truth = prop.evaluate()
            print(f"Conclusion {i+1} '{conclusion}' is {truth}")
            if truth:
                print("  ⚠️  TRUE CONCLUSION DETECTED!")

if __name__ == "__main__":
    test_basic_example()
    test_problematic_example()