#!/usr/bin/env python3
"""
Debug the operator signature issue.
"""

import sys
import os
sys.path.insert(0, '.')

from src.model_checker.theory_lib.exclusion.attempt6_incremental.semantic import ExclusionSemantics
from src.model_checker.theory_lib.exclusion.attempt6_incremental.operators import exclusion_operators
from src.model_checker import syntactic

def test_simple_disjunction():
    """Test simple disjunction parsing."""
    
    # Settings for the test
    settings = {
        "N": 2,
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
    
    try:
        # Create simple syntax with disjunction - try different formats
        test_formulas = [
            '\\univee A B',
            '(\\univee A B)',
            '\\univee (A) (B)',
            '\\univee{A}{B}'
        ]
        
        for formula in test_formulas:
            print(f"\n--- Testing formula: '{formula}' ---")
            try:
                premises = [formula]
        conclusions = []
        
        # Test manual parsing
        print(f"Testing manual parsing...")
        test_formula = '\\univee A B'
        print(f"Input formula: '{test_formula}'")
        
        print(f"Testing premises: {premises}")
        print(f"Operator collection type: {type(exclusion_operators)}")
        
        # Create syntax - this is where the error occurs
        syntax = syntactic.Syntax(premises, conclusions, exclusion_operators)
        
        print(f"✅ Syntax created successfully")
        print(f"Premises parsed: {[str(p) for p in syntax.premises]}")
        
        # Test calling true_at directly
        premise_sentence = syntax.premises[0]
        print(f"Premise sentence: {premise_sentence}")
        print(f"Operator: {premise_sentence.operator}")
        print(f"Operator name: {premise_sentence.operator.name}")
        print(f"Operator arity: {premise_sentence.operator.arity}")
        print(f"Arguments: {premise_sentence.arguments}")
        print(f"Number of arguments: {len(premise_sentence.arguments)}")
        
        for i, arg in enumerate(premise_sentence.arguments):
            print(f"  Arg {i}: {arg} (type: {type(arg)})")
        
        # Call true_at manually with correct number of args
        main_point = {"world": semantics.main_point["world"]}
        if len(premise_sentence.arguments) == 2:
            result = premise_sentence.operator.true_at(premise_sentence.arguments[0], premise_sentence.arguments[1], main_point)
        else:
            print(f"❌ Expected 2 arguments for binary operator, got {len(premise_sentence.arguments)}")
            return
        print(f"✅ true_at call successful")
        print(f"Result type: {type(result)}")
        
    except Exception as e:
        print(f"❌ Error: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    test_simple_disjunction()