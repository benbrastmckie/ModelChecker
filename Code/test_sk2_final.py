#!/usr/bin/env python3
"""
Final test of SK2 strategy on problematic examples.
"""

import sys
sys.path.insert(0, 'src')

from model_checker.theory_lib.exclusion.examples import TN_ENTAIL_example, DISJ_DM_RL_example
from model_checker.theory_lib.exclusion.semantic import ExclusionSemantics, UnilateralProposition, ExclusionStructure
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker import Syntax, ModelConstraints
from model_checker.utils import run_enhanced_test

def test_sk2_example(name, example_data, strategy="SK2"):
    """Test a single example with SK2 strategy."""
    print(f"\n{'='*60}")
    print(f"Testing: {name} with {strategy}")
    print('='*60)
    
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

def main():
    """Test SK2 on both problematic examples."""
    print("SK2 STRATEGY FINAL TEST")
    print("Testing the True Skolemization implementation")
    
    # Test Triple Negation Entailment
    tn_result = test_sk2_example("Triple Negation Entailment", TN_ENTAIL_example, "SK2")
    
    # Test Disjunctive DeMorgan's RL
    dm_result = test_sk2_example("Disjunctive DeMorgan's RL", DISJ_DM_RL_example, "SK2")
    
    # For comparison, also test with MS
    print("\n" + "="*60)
    print("COMPARISON WITH MS STRATEGY")
    print("="*60)
    
    tn_ms_result = test_sk2_example("Triple Negation Entailment", TN_ENTAIL_example, "MS")
    dm_ms_result = test_sk2_example("Disjunctive DeMorgan's RL", DISJ_DM_RL_example, "MS")
    
    # Summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    
    print("\nTriple Negation Entailment:")
    print(f"  MS:  Model={tn_ms_result.model_found}, False premises={any(p is False for p in tn_ms_result.premise_evaluations if tn_ms_result.premise_evaluations)}")
    print(f"  SK2: Model={tn_result.model_found}, False premises={any(p is False for p in tn_result.premise_evaluations if tn_result.premise_evaluations)}")
    
    print("\nDisjunctive DeMorgan's RL:")
    print(f"  MS:  Model={dm_ms_result.model_found}, False premises={any(p is False for p in dm_ms_result.premise_evaluations if dm_ms_result.premise_evaluations)}")
    print(f"  SK2: Model={dm_result.model_found}, False premises={any(p is False for p in dm_result.premise_evaluations if dm_result.premise_evaluations)}")
    
    # Check if SK2 solved the problem
    sk2_fixed_tn = tn_result.model_found and all(tn_result.premise_evaluations) if tn_result.premise_evaluations else False
    sk2_fixed_dm = dm_result.model_found and all(dm_result.premise_evaluations) if dm_result.premise_evaluations else False
    
    if sk2_fixed_tn and sk2_fixed_dm:
        print("\n✓ SUCCESS: SK2 eliminates false premises in both examples!")
    elif sk2_fixed_tn or sk2_fixed_dm:
        print("\n⚠️  PARTIAL SUCCESS: SK2 fixes some but not all false premises")
    else:
        print("\n✗ SK2 did not eliminate false premises")

if __name__ == "__main__":
    main()