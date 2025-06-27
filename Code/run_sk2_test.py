#!/usr/bin/env python3
"""
Test SK2 strategy using the analyze_strategies.py pattern.
"""

import sys
sys.path.insert(0, 'src')

import json
import time
from model_checker.utils import run_test

# Import exclusion theory components
from model_checker.theory_lib.exclusion.semantic import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
)
from model_checker.theory_lib.exclusion import operators

# Test specific examples
test_examples = {
    "TN_ENTAIL": {
        "premises": ['\\exclude \\exclude \\exclude A'],
        "conclusions": ['\\exclude A'],
        "settings": {'N': 3}
    },
    "DISJ_DM_RL": {
        "premises": ['(\\exclude A \\uniwedge \\exclude B)'],
        "conclusions": ['\\exclude (A \\univee B)'],
        "settings": {'N': 3}
    }
}

def test_strategy(strategy_name):
    """Test a strategy on specific examples."""
    print(f"\n{'='*60}")
    print(f"Testing {strategy_name} Strategy")
    print(f"{'='*60}\n")
    
    # Create exclusion theory with the specified strategy
    exclusion_operators = operators.create_operator_collection(strategy_name)
    
    exclusion_theory = {
        'semantics': ExclusionSemantics,
        'proposition': UnilateralProposition,
        'model_structure': ExclusionStructure,
        'operators': exclusion_operators,
    }
    
    results = {}
    
    for example_name, example_data in test_examples.items():
        print(f"\nTesting: {example_name}")
        
        example = [
            example_data['premises'],
            example_data['conclusions'],
            example_data['settings']
        ]
        
        semantic_theories = {'exclusion': exclusion_theory}
        
        try:
            start_time = time.time()
            result = run_test(example, semantic_theories)
            elapsed_time = time.time() - start_time
            
            print(f"  Result: {result}")
            print(f"  Time: {elapsed_time:.3f}s")
            
            # Check if it's a countermodel
            if result != 'theorem':
                print(f"  Countermodel found")
                # Can't easily check for false premises with this approach
                # but we know SK2 should eliminate them
            
            results[example_name] = {
                'result': result,
                'time': elapsed_time
            }
            
        except Exception as e:
            print(f"  ERROR: {e}")
            results[example_name] = {
                'result': 'error',
                'time': 0,
                'error': str(e)
            }
    
    return results

def main():
    """Test SK2 and compare with MS."""
    
    # Test SK2
    print("\n" + "="*60)
    print("SK2 STRATEGY TEST")
    print("="*60)
    sk2_results = test_strategy("SK2")
    
    # Test MS for comparison
    print("\n" + "="*60)
    print("MS STRATEGY TEST (for comparison)")
    print("="*60)
    ms_results = test_strategy("MS")
    
    # Summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    
    print(f"\n{'Example':<20} {'SK2 Result':<20} {'MS Result':<20}")
    print("-" * 60)
    
    for example_name in test_examples:
        sk2_res = sk2_results.get(example_name, {}).get('result', 'N/A')
        ms_res = ms_results.get(example_name, {}).get('result', 'N/A')
        print(f"{example_name:<20} {sk2_res:<20} {ms_res:<20}")
    
    # Save results
    with open("sk2_test_results.json", "w") as f:
        json.dump({
            'SK2': sk2_results,
            'MS': ms_results
        }, f, indent=2)
    
    print(f"\nResults saved to sk2_test_results.json")
    
    # Analysis
    print("\n" + "="*60)
    print("ANALYSIS")
    print("="*60)
    print("\nThe SK2 strategy uses true Skolemization to eliminate existential quantifiers.")
    print("This should solve the false premise issue by making all functions explicit.")
    print("\nKey differences from other strategies:")
    print("- No existential quantifiers at all")
    print("- Both h and y are Skolem functions")
    print("- Functions are directly in the Z3 model")
    print("- Evaluation should be consistent with solving")

if __name__ == "__main__":
    main()