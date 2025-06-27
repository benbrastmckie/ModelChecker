#!/usr/bin/env python3
"""
Test SK2 with Skolemized atomic sentences.
"""

import sys
sys.path.insert(0, 'src')

from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example, DISJ_DM_RL_example
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import Syntax, ModelConstraints
from model_checker.utils import run_enhanced_test

# Monkey patch ExclusionSemantics to enable Skolemization for SK2
original_init = ExclusionSemantics.__init__

def patched_init(self, settings):
    original_init(self, settings)
    # Enable Skolemization for atomic sentences
    self.use_skolem_for_atoms = True

def test_sk2_example_with_skolem(name, example_data, strategy="SK2"):
    """Test a single example with SK2 strategy and Skolemized atoms."""
    print(f"\n{'='*60}")
    print(f"Testing: {name} with {strategy} (Skolemized atoms)")
    print('='*60)
    
    # Temporarily patch ExclusionSemantics
    ExclusionSemantics.__init__ = patched_init
    
    try:
        # Get operator collection for SK2
        operator_collection = create_operator_collection(strategy)
        
        # Run enhanced test
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
        print(f"\nResults for {name}:")
        print(f"  Model found: {result.model_found}")
        print(f"  Check result: {result.check_result}")
        print(f"  Solving time: {result.solving_time:.3f}s")
        print(f"  Z3 status: {result.z3_model_status}")
        
        if result.model_found:
            print(f"  Premise evaluations: {result.premise_evaluations}")
            print(f"  Conclusion evaluations: {result.conclusion_evaluations}")
            
            # Check for false premise
            if result.premise_evaluations and any(p is False for p in result.premise_evaluations):
                print("  ⚠️  FALSE PREMISE DETECTED!")
            else:
                print("  ✓ No false premises")
                
            if result.is_valid_countermodel():
                print("  ✓ Valid countermodel (all premises true, all conclusions false)")
        else:
            print("  ✗ No model found")
            
        if result.error_message:
            print(f"  Error: {result.error_message}")
        
        return result
        
    finally:
        # Restore original
        ExclusionSemantics.__init__ = original_init

def main():
    """Test SK2 with Skolemized atomic sentences."""
    print("SK2 STRATEGY WITH SKOLEMIZED ATOMS TEST")
    print("Testing the True Skolemization implementation with Skolemized atomic sentences")
    
    # Test Triple Negation Entailment
    tn_result = test_sk2_example_with_skolem("Triple Negation Entailment", TN_ENTAIL_example, "SK2")
    
    # Test Disjunctive DeMorgan's RL
    dm_result = test_sk2_example_with_skolem("Disjunctive DeMorgan's RL", DISJ_DM_RL_example, "SK2")
    
    # For comparison, test with MS (without Skolemized atoms)
    print("\n" + "="*60)
    print("COMPARISON WITH MS STRATEGY (Original)")
    print("="*60)
    
    # MS tests without patching
    tn_ms_result = test_sk2_example_with_skolem("Triple Negation Entailment", TN_ENTAIL_example, "MS")
    dm_ms_result = test_sk2_example_with_skolem("Disjunctive DeMorgan's RL", DISJ_DM_RL_example, "MS")
    
    # Summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    
    print("\nTriple Negation Entailment:")
    print(f"  MS (Original):  Model={tn_ms_result.model_found}, False premises={any(p is False for p in tn_ms_result.premise_evaluations if tn_ms_result.premise_evaluations)}")
    print(f"  SK2 (Skolem):   Model={tn_result.model_found}, False premises={any(p is False for p in tn_result.premise_evaluations if tn_result.premise_evaluations)}")
    
    print("\nDisjunctive DeMorgan's RL:")
    print(f"  MS (Original):  Model={dm_ms_result.model_found}, False premises={any(p is False for p in dm_ms_result.premise_evaluations if dm_ms_result.premise_evaluations)}")
    print(f"  SK2 (Skolem):   Model={dm_result.model_found}, False premises={any(p is False for p in dm_result.premise_evaluations if dm_result.premise_evaluations)}")
    
    # Check if SK2 with Skolemization solved the problem
    sk2_fixed_tn = tn_result.model_found and all(tn_result.premise_evaluations) if tn_result.premise_evaluations else False
    sk2_fixed_dm = dm_result.model_found and all(dm_result.premise_evaluations) if dm_result.premise_evaluations else False
    
    if sk2_fixed_tn and sk2_fixed_dm:
        print("\n✓ SUCCESS: SK2 with Skolemized atoms eliminates false premises in both examples!")
    elif sk2_fixed_tn or sk2_fixed_dm:
        print("\n⚠️  PARTIAL SUCCESS: SK2 with Skolemized atoms fixes some but not all false premises")
    else:
        print("\n✗ SK2 with Skolemized atoms did not eliminate false premises")

if __name__ == "__main__":
    main()