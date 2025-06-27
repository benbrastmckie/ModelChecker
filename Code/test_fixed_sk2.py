#!/usr/bin/env python3
"""
Test SK2 with a fix for the Skolem function mismatch.
"""

import sys
sys.path.insert(0, 'src')

import z3
from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example, DISJ_DM_RL_example
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection, ExclusionOperatorBase
from model_checker import Syntax, ModelConstraints
from model_checker.utils import run_enhanced_test, Exists

# Create a fixed version of the exclusion operator's true_at
original_true_at = ExclusionOperatorBase.true_at

def fixed_true_at(self, arg, eval_point):
    """Fixed version that ensures Skolem functions are created during constraint generation."""
    semantics = self.semantics
    eval_world = eval_point["world"] if isinstance(eval_point, dict) else eval_point
    
    # Pre-populate the cache by calling true_at on the argument
    # This ensures Skolem functions are created during constraint generation
    arg_true_formula = semantics.true_at(arg, eval_point)
    
    # Now use the standard exclusion formula
    x = z3.BitVec(f"ver_exclude_{arg}", semantics.N)
    return Exists(
        x,
        z3.And(
            semantics.extended_verify(x, arg, eval_point),
            semantics.is_part_of(x, eval_world)
        )
    )

def test_with_fix(name, example_data, strategy="SK2"):
    """Test with the fixed true_at method."""
    print(f"\n{'='*60}")
    print(f"Testing: {name} with {strategy} (Fixed)")
    print('='*60)
    
    # Apply the fix
    ExclusionOperatorBase.true_at = fixed_true_at
    
    try:
        # Get operator collection
        operator_collection = create_operator_collection(strategy)
        
        # Run test
        result = run_enhanced_test(
            example_case=example_data,
            semantic_class=ExclusionSemantics,
            proposition_class=UnilateralProposition,
            operator_collection=operator_collection,
            syntax_class=Syntax,
            model_constraints=ModelConstraints,
            model_structure=ExclusionStructure,
            strategy_name=strategy
        )
        
        # Display results
        print(f"\nResults:")
        print(f"  Model found: {result.model_found}")
        print(f"  Premise evaluations: {result.premise_evaluations}")
        print(f"  Conclusion evaluations: {result.conclusion_evaluations}")
        
        if result.premise_evaluations and all(result.premise_evaluations):
            print("  ✓ ALL PREMISES TRUE!")
        elif result.premise_evaluations and any(p is False for p in result.premise_evaluations):
            print("  ⚠️  FALSE PREMISE DETECTED!")
            
        return result
        
    finally:
        # Restore original
        ExclusionOperatorBase.true_at = original_true_at

def main():
    """Test the fix."""
    print("TESTING SK2 WITH SKOLEM FUNCTION FIX")
    
    # Test Triple Negation
    tn_result = test_with_fix("Triple Negation Entailment", TN_ENTAIL_example)
    
    # Test Disjunctive DeMorgan
    dm_result = test_with_fix("Disjunctive DeMorgan's RL", DISJ_DM_RL_example)
    
    # Summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    
    tn_fixed = tn_result.model_found and all(tn_result.premise_evaluations) if tn_result.premise_evaluations else False
    dm_fixed = dm_result.model_found and all(dm_result.premise_evaluations) if dm_result.premise_evaluations else False
    
    print(f"\nTriple Negation: {'✓ FIXED' if tn_fixed else '✗ Still broken'}")
    print(f"Disjunctive DeMorgan: {'✓ FIXED' if dm_fixed else '✗ Still broken'}")
    
    if tn_fixed and dm_fixed:
        print("\n🎉 SUCCESS! The Skolemization fix eliminates false premises!")
    elif tn_fixed or dm_fixed:
        print("\n⚠️  PARTIAL SUCCESS: Some examples are fixed")
    else:
        print("\n✗ The fix did not work")

if __name__ == "__main__":
    main()