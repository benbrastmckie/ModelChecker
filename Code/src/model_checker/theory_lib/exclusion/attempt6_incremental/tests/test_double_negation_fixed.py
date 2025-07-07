#!/usr/bin/env python3
"""
Test double negation elimination with incremental approach.

This test checks if the incremental approach solves the FALSE PREMISE PROBLEM
where ~~A |- A was incorrectly showing as invalid due to Skolem function 
inaccessibility.
"""

import sys
import os
sys.path.insert(0, '.')

from src.model_checker.theory_lib.exclusion.attempt6_incremental.semantic import ExclusionSemantics, UnilateralProposition
from src.model_checker.theory_lib.exclusion.attempt6_incremental.operators import exclusion_operators
from src.model_checker.theory_lib.exclusion.attempt6_incremental.incremental_model import IncrementalModelStructure
from src.model_checker import syntactic
from src.model_checker.model import ModelConstraints

def test_double_negation():
    """Test double negation elimination: ~~A |- A"""
    
    # Settings for the test
    settings = {
        "N": 3,
        "max_time": 5,
        "expectation": True,
        "contingent": False,
        "non_empty": False,
        "non_null": False,
        "disjoint": False,
        "fusion_closure": False
    }
    
    # Create semantics
    semantics = ExclusionSemantics(settings)
    
    # Create the double negation example
    premises = ['\\exclude \\exclude A']
    conclusions = ['A']
    
    print("Testing double negation elimination: \\exclude \\exclude A |- A")
    print(f"Premises: {premises}")
    print(f"Conclusions: {conclusions}")
    print()
    
    try:
        # Create syntax
        syntax = syntactic.Syntax(premises, conclusions, exclusion_operators)
        
        print(f"Created syntax with {len(syntax.premises)} premises and {len(syntax.conclusions)} conclusions")
        
        # Create model constraints
        model_constraints = ModelConstraints(
            settings,
            syntax,
            semantics,
            UnilateralProposition
        )
        
        print("Created model constraints")
        
        # Create incremental model structure
        print("Creating incremental model structure...")
        incremental_model = IncrementalModelStructure(model_constraints, settings)
        
        print(f"Model found: {incremental_model.z3_model_status}")
        print(f"Runtime: {incremental_model.z3_model_runtime}")
        
        if incremental_model.z3_model_status:
            print()
            print("❌ COUNTERMODEL FOUND - Double negation elimination is INVALID")
            print("   This suggests the FALSE PREMISE PROBLEM persists")
            print("   (The incremental approach has not solved the issue)")
            return False
        else:
            print()
            print("✅ NO COUNTERMODEL - Double negation elimination is VALID")
            print("   This suggests the FALSE PREMISE PROBLEM is SOLVED!")
            print("   (The incremental approach successfully accessed witness functions)")
            return True
            
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        return False

if __name__ == "__main__":
    success = test_double_negation()
    sys.exit(0 if success else 1)