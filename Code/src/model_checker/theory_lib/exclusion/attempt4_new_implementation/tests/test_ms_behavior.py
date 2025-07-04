#!/usr/bin/env python3
"""
Test the current MS (Multi-Sort) strategy behavior on a specific example.
"""

import sys
from pathlib import Path

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from model_checker.syntactic import Syntax
from model_checker.theory_lib.exclusion import (
    ExclusionSemantics, 
    UnilateralProposition,
    ExclusionStructure,
    exclusion_operators
)

def test_double_negation_elimination():
    """Test the DN_ELIM example which has a false premise issue."""
    
    print("Testing Double Negation Elimination (DN_ELIM)")
    print("=" * 50)
    
    # Example setup from baseline
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
    
    # Create syntax for parsing
    syntax = Syntax(premises, conclusions, exclusion_operators)
    
    # Create structure
    structure = ExclusionStructure(semantics, combined_settings)
    
    # Set premises and conclusions
    for p in syntax.premises:
        structure.set_premise(p)
    for c in syntax.conclusions:
        structure.set_conclusion(c)
    
    # Generate model
    print("Generating model...")
    has_model = structure.generate()
    
    if not has_model:
        print("No model found!")
        return
        
    print(f"Model found! Z3 model has {len(structure.z3_model)} declarations")
    
    # Check premise truth values
    print("\nChecking premise truth values:")
    for i, premise in enumerate(syntax.premises):
        prop = UnilateralProposition(premise, structure)
        truth_value = prop.evaluate()
        print(f"  Premise {i+1} '{premise}': {truth_value}")
        if not truth_value:
            print(f"    ⚠️  FALSE PREMISE DETECTED!")
            
    # Check conclusion truth values
    print("\nChecking conclusion truth values:")
    for i, conclusion in enumerate(syntax.conclusions):
        prop = UnilateralProposition(conclusion, structure)
        truth_value = prop.evaluate()
        print(f"  Conclusion {i+1} '{conclusion}': {truth_value}")
        if truth_value:
            print(f"    ⚠️  TRUE CONCLUSION DETECTED!")
            
    # Print some model details
    print("\nModel details:")
    print(f"  Main world: {structure.z3_model.eval(semantics.main_world)}")
    
    # Check which exclusion strategy is being used
    print(f"\nExclusion operator class: {type(exclusion_operators['\\exclude']).__name__}")

if __name__ == "__main__":
    test_double_negation_elimination()