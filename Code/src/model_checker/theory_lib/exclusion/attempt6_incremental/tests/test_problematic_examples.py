#!/usr/bin/env python3
"""
Test the problematic exclusion examples that were failing due to the FALSE PREMISE PROBLEM.

These tests should now pass with the incremental approach that properly accesses
witness functions during constraint generation.
"""

import sys
import os
sys.path.insert(0, '.')

from src.model_checker.theory_lib.exclusion.attempt6_incremental.semantic import ExclusionSemantics, UnilateralProposition
from src.model_checker.theory_lib.exclusion.attempt6_incremental.operators import exclusion_operators
from src.model_checker.theory_lib.exclusion.attempt6_incremental.incremental_model import IncrementalModelStructure
from src.model_checker import syntactic
from src.model_checker.model import ModelConstraints


def test_example(name, premises, conclusions, expected_valid=True):
    """Test a specific example and return whether it passed."""
    print(f"\n=== Testing {name} ===")
    print(f"Premises: {premises}")
    print(f"Conclusions: {conclusions}")
    print(f"Expected: {'VALID' if expected_valid else 'INVALID'}")
    
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
    
    try:
        # Create semantics
        semantics = ExclusionSemantics(settings)
        
        # Create syntax
        syntax = syntactic.Syntax(premises, conclusions, exclusion_operators)
        
        # Create model constraints
        model_constraints = ModelConstraints(
            settings, syntax, semantics, UnilateralProposition
        )
        
        # Create incremental model structure
        incremental_model = IncrementalModelStructure(model_constraints, settings)
        
        # Check results
        countermodel_found = incremental_model.z3_model_status
        runtime = incremental_model.z3_model_runtime
        
        print(f"Countermodel found: {countermodel_found}")
        print(f"Runtime: {runtime}")
        
        if expected_valid:
            # Should be valid (no countermodel)
            if not countermodel_found:
                print("✅ PASS - No countermodel found (correctly valid)")
                return True
            else:
                print("❌ FAIL - Countermodel found (incorrectly invalid)")
                return False
        else:
            # Should be invalid (countermodel found)  
            if countermodel_found:
                print("✅ PASS - Countermodel found (correctly invalid)")
                return True
            else:
                print("❌ FAIL - No countermodel found (incorrectly valid)")
                return False
                
    except Exception as e:
        print(f"❌ ERROR: {e}")
        import traceback
        traceback.print_exc()
        return False


def main():
    """Run all problematic examples."""
    print("Testing problematic exclusion examples with incremental approach...")
    
    test_cases = [
        # Double negation elimination - should be VALID
        ("Double Negation Elimination", 
         ['\\exclude \\exclude A'], ['A'], True),
        
        # Triple negation elimination - should be VALID
        ("Triple Negation Elimination",
         ['\\exclude \\exclude \\exclude A'], ['\\exclude A'], True),
        
        # Disjunctive syllogism - should be VALID
        ("Disjunctive Syllogism",
         ['(A \\univee B)', '\\exclude A'], ['B'], True),
        
        # Simple invalid case - should be INVALID
        ("Simple Invalid Case",
         ['A'], ['\\exclude A'], False),
        
        # Complex invalid case - should be INVALID
        ("Complex Invalid Case",
         ['\\exclude A'], ['A'], False),
    ]
    
    passed = 0
    total = len(test_cases)
    
    for name, premises, conclusions, expected_valid in test_cases:
        if test_example(name, premises, conclusions, expected_valid):
            passed += 1
    
    print(f"\n=== SUMMARY ===")
    print(f"Passed: {passed}/{total}")
    
    if passed == total:
        print("🎉 ALL TESTS PASSED!")
        print("The FALSE PREMISE PROBLEM has been SOLVED!")
        print("The incremental approach successfully enables witness function access.")
        return True
    else:
        print("❌ Some tests failed.")
        print("The incremental approach may need further refinement.")
        return False


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)