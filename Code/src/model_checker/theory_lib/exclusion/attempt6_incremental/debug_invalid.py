#!/usr/bin/env python3
"""
Debug why invalid cases are showing as valid.
"""

import sys
import os
sys.path.insert(0, '.')

from src.model_checker.theory_lib.exclusion.attempt6_incremental.semantic import ExclusionSemantics, UnilateralProposition
from src.model_checker.theory_lib.exclusion.attempt6_incremental.operators import exclusion_operators
from src.model_checker.theory_lib.exclusion.attempt6_incremental.incremental_model import IncrementalModelStructure
from src.model_checker import syntactic
from src.model_checker.model import ModelConstraints

def test_invalid_case():
    """Test A |- ¬A which should be INVALID (countermodel should be found)."""
    
    # Settings for the test
    settings = {
        "N": 2,  # Small N for debugging
        "max_time": 5,
        "expectation": True,
        "contingent": False,
        "non_empty": False,
        "non_null": False,
        "disjoint": False,
        "fusion_closure": False
    }
    
    premises = ['\\exclude A']
    conclusions = ['A']
    
    print(f"Testing ¬A |- A (should find countermodel)")
    print(f"Premises: {premises}")
    print(f"Conclusions: {conclusions}")
    print()
    
    try:
        # Create semantics
        semantics = ExclusionSemantics(settings)
        
        # Create syntax
        syntax = syntactic.Syntax(premises, conclusions, exclusion_operators)
        
        print(f"Parsed premises: {[str(p) for p in syntax.premises]}")
        print(f"Parsed conclusions: {[str(c) for c in syntax.conclusions]}")
        
        # Create model constraints
        model_constraints = ModelConstraints(
            settings, syntax, semantics, UnilateralProposition
        )
        
        print(f"Model constraints created")
        print(f"Frame constraints: {len(model_constraints.frame_constraints)}")
        print(f"Model constraints: {len(model_constraints.model_constraints)}")  
        print(f"Premise constraints: {len(model_constraints.premise_constraints)}")
        print(f"Conclusion constraints: {len(model_constraints.conclusion_constraints)}")
        print()
        
        # Create incremental model structure
        incremental_model = IncrementalModelStructure(model_constraints, settings)
        
        print(f"Final result:")
        print(f"  Countermodel found: {incremental_model.z3_model_status}")
        print(f"  Runtime: {incremental_model.z3_model_runtime}")
        
        if incremental_model.z3_model_status:
            print("✅ CORRECT - Countermodel found (A |- ¬A is invalid)")
        else:
            print("❌ INCORRECT - No countermodel found (A |- ¬A should be invalid)")
            
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    test_invalid_case()