"""
Quick test of double negation example to see if incremental approach works.
"""

import sys
import os

# Add current directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from semantic import ExclusionSemantics, UnilateralProposition
from operators import exclusion_operators
from incremental_model import IncrementalModelStructure
from model_checker import syntactic
from model_checker.model import ModelConstraints

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
    
    try:
        # Create syntax
        operators = syntactic.OperatorCollection(exclusion_operators)
        syntax = syntactic.Syntax(premises, conclusions, operators)
        
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
            print("COUNTERMODEL FOUND - Double negation elimination is INVALID")
            print("This suggests the FALSE PREMISE PROBLEM persists")
        else:
            print("NO COUNTERMODEL - Double negation elimination is VALID")
            print("This suggests the FALSE PREMISE PROBLEM is SOLVED!")
            
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    test_double_negation()