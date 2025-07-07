#!/usr/bin/env python3
"""
Simple debug for operator parsing.
"""

import sys
import os
sys.path.insert(0, '.')

from src.model_checker.theory_lib.exclusion.attempt6_incremental.operators import exclusion_operators
from src.model_checker import syntactic

def test_formula_parsing(formula):
    """Test parsing a single formula."""
    print(f"\n=== Testing formula: '{formula}' ===")
    
    try:
        syntax = syntactic.Syntax([formula], [], exclusion_operators)
        
        if len(syntax.premises) > 0:
            sentence = syntax.premises[0]
            print(f"✅ Parsed successfully")
            print(f"   Sentence: {sentence}")
            print(f"   Operator: {sentence.operator.name if sentence.operator else 'None'}")
            print(f"   Arity: {sentence.operator.arity if sentence.operator else 'None'}")
            print(f"   Arguments: {sentence.arguments}")
            print(f"   Arg count: {len(sentence.arguments)}")
            
            # Check if arguments are parsed correctly
            if sentence.operator and sentence.operator.arity != len(sentence.arguments):
                print(f"❌ MISMATCH: Expected {sentence.operator.arity} args, got {len(sentence.arguments)}")
            else:
                print(f"✅ Argument count matches arity")
                
        else:
            print("❌ No premises parsed")
            
    except Exception as e:
        print(f"❌ Parse error: {e}")
        import traceback
        traceback.print_exc()

def main():
    """Test various formula formats."""
    
    formulas = [
        # Basic tests
        'A',
        '\\exclude A',
        
        # Binary operator tests - different formats
        '\\univee A B',
        '(\\univee A B)',
        '\\univee (A) (B)',
        '(\\univee (A) (B))',
        
        # Nested tests
        '\\exclude \\exclude A',
        '\\univee A (\\exclude B)',
        '\\uniwedge (\\exclude A) B'
    ]
    
    for formula in formulas:
        test_formula_parsing(formula)
    
    print("\n=== Summary ===")
    print("Check which formulas parse correctly and which have arity mismatches.")

if __name__ == "__main__":
    main()