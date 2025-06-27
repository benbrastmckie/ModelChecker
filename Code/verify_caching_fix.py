#!/usr/bin/env python3
"""
Verify the caching fix is working correctly.
"""

import sys
sys.path.insert(0, 'src')

from fix_premise_evaluation import test_with_cache
from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example, DISJ_DM_RL_example

def verify_fix():
    """Verify the fix in detail."""
    print("VERIFYING CONSTRAINT CACHING FIX")
    print("="*60)
    
    # Test Triple Negation which expects a counterexample
    print("\n1. Triple Negation Entailment (expects counterexample):")
    print("   Premise: \\exclude \\exclude \\exclude A")
    print("   Conclusion: \\exclude A")
    print("   Expected: Premise TRUE, Conclusion FALSE")
    
    result = test_with_cache("Triple Negation", TN_ENTAIL_example)
    
    if result.model_found:
        print(f"\n   Actual: Premise {result.premise_evaluations[0]}, Conclusion {result.conclusion_evaluations[0]}")
        
        if result.premise_evaluations[0] and not result.conclusion_evaluations[0]:
            print("   ✓ Correct counterexample!")
        else:
            print("   ✗ Incorrect - both are true, this is not a counterexample")
            print("\n   The issue: We're using premise constraints for conclusions too")
            print("   Conclusions should use conclusion_constraints which are negated")

if __name__ == "__main__":
    verify_fix()