#!/usr/bin/env python3
"""
Test simple cases with pure incremental approach.
"""

import sys
import os
sys.path.insert(0, '.')

from src.model_checker.theory_lib.exclusion.attempt6_incremental.semantic import ExclusionSemantics, UnilateralProposition
from src.model_checker.theory_lib.exclusion.attempt6_incremental.operators import exclusion_operators
from src.model_checker.theory_lib.exclusion.attempt6_incremental.incremental_model import IncrementalModelStructure
from src.model_checker import syntactic
from src.model_checker.model import ModelConstraints

def test_case(name, premises, conclusions, expected_valid):
    """Test a single case."""
    print(f"\n=== {name} ===")
    print(f"Premises: {premises}")
    print(f"Conclusions: {conclusions}")
    print(f"Expected: {'VALID' if expected_valid else 'INVALID'}")
    
    settings = {
        "N": 2,  # Small N for speed
        "max_time": 5,
        "expectation": True,
        "contingent": False,
        "non_empty": False,
        "non_null": False,
        "disjoint": False,
        "fusion_closure": False
    }
    
    try:
        semantics = ExclusionSemantics(settings)
        syntax = syntactic.Syntax(premises, conclusions, exclusion_operators)
        model_constraints = ModelConstraints(settings, syntax, semantics, UnilateralProposition)
        incremental_model = IncrementalModelStructure(model_constraints, settings)
        
        countermodel_found = incremental_model.z3_model_status
        runtime = incremental_model.z3_model_runtime
        
        print(f"Countermodel found: {countermodel_found}")
        print(f"Runtime: {runtime}s")
        
        if expected_valid:
            if not countermodel_found:
                print("✅ CORRECT - Valid (no countermodel)")
                return True
            else:
                print("❌ WRONG - Should be valid but found countermodel")
                return False
        else:
            if countermodel_found:
                print("✅ CORRECT - Invalid (countermodel found)")
                return True
            else:
                print("❌ WRONG - Should be invalid but no countermodel")
                return False
                
    except Exception as e:
        print(f"❌ ERROR: {e}")
        return False

def main():
    """Test basic cases to verify pure incremental approach."""
    
    test_cases = [
        # Simple valid case
        ("A ⊢ A", ['A'], ['A'], True),
        
        # Simple invalid cases
        ("A ⊢ ¬A", ['A'], ['\\exclude A'], False),
        ("¬A ⊢ A", ['\\exclude A'], ['A'], False),
        
        # Double negation elimination (the key test)
        ("¬¬A ⊢ A", ['\\exclude \\exclude A'], ['A'], True),
        
        # Another valid case with exclusion
        ("¬¬¬A ⊢ ¬A", ['\\exclude \\exclude \\exclude A'], ['\\exclude A'], True),
    ]
    
    passed = 0
    total = len(test_cases)
    
    for name, premises, conclusions, expected_valid in test_cases:
        if test_case(name, premises, conclusions, expected_valid):
            passed += 1
    
    print(f"\n=== SUMMARY ===")
    print(f"Passed: {passed}/{total}")
    
    if passed == total:
        print("🎉 ALL TESTS PASSED!")
        print("The pure incremental approach is working correctly!")
        return True
    else:
        print("❌ Some tests failed.")
        print("The incremental approach needs further debugging.")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)