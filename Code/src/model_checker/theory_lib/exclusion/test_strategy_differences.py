#!/usr/bin/env python3
"""
Test script to explore differences between the new exclusion strategies.
This script tests more complex formulas to see if they reveal performance differences.
"""

import sys
import os
import time

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))

from model_checker import ModelConstraints, Syntax
from model_checker.theory_lib.exclusion import (
    ExclusionStructure,
    UnilateralProposition,
    ExclusionSemantics,
)
from model_checker.theory_lib.exclusion.operators import STRATEGY_REGISTRY, create_operator_collection
from model_checker.utils import run_strategy_test

# Define more complex test cases that might differentiate strategies
complex_examples = {
    # Nested exclusion formulas
    "DOUBLE_EXCLUDE": {
        "premises": [],
        "conclusions": ["\\exclude \\exclude A"],
        "settings": {'N': 3, 'max_time': 10}
    },
    
    "TRIPLE_EXCLUDE": {
        "premises": [],
        "conclusions": ["\\exclude \\exclude \\exclude A"],
        "settings": {'N': 3, 'max_time': 10}
    },
    
    # Complex nested operations
    "NESTED_OPERATIONS": {
        "premises": ["\\exclude (A \\uniwedge (B \\univee \\exclude C))"],
        "conclusions": ["(\\exclude A \\univee \\exclude (B \\univee \\exclude C))"],
        "settings": {'N': 4, 'max_time': 15}
    },
    
    # Multiple exclusions
    "MULTI_EXCLUDE": {
        "premises": ["\\exclude A", "\\exclude B", "\\exclude C"],
        "conclusions": ["\\exclude (A \\univee B \\univee C)"],
        "settings": {'N': 4, 'max_time': 15}
    },
    
    # Long chains
    "CHAIN_EXCLUDE": {
        "premises": ["(\\exclude A \\uniwedge \\exclude B \\uniwedge \\exclude C)"],
        "conclusions": ["\\exclude (A \\univee B \\univee C)"],
        "settings": {'N': 4, 'max_time': 15}
    },
    
    # Deeply nested
    "DEEP_NEST": {
        "premises": [],
        "conclusions": ["(\\exclude (A \\uniwedge (B \\univee (C \\uniwedge \\exclude D))))"],
        "settings": {'N': 5, 'max_time': 20}
    },
    
    # Identity with multiple variables
    "COMPLEX_IDENTITY": {
        "premises": [],
        "conclusions": ["((A \\uniwedge B \\uniwedge C) \\uniequiv (A \\uniwedge B \\uniwedge C))"],
        "settings": {'N': 4, 'max_time': 10}
    },
    
    # Mixed operators
    "MIXED_OPS": {
        "premises": ["(A \\uniequiv \\exclude B)", "(B \\uniequiv \\exclude C)"],
        "conclusions": ["(A \\uniequiv \\exclude \\exclude C)"],
        "settings": {'N': 4, 'max_time': 15}
    }
}

def test_strategy_on_complex_examples(strategy_name):
    """Test a specific strategy on complex examples."""
    print(f"\n=== Testing {strategy_name} Strategy ===")
    
    results = {}
    total_time = 0
    successful = 0
    valid = 0
    
    for example_name, example_data in complex_examples.items():
        start_time = time.time()
        
        example_case = [
            example_data["premises"],
            example_data["conclusions"],
            example_data["settings"]
        ]
        
        try:
            result = run_strategy_test(example_case, strategy_name)
            elapsed = time.time() - start_time
            total_time += elapsed
            
            if result.model_found:
                successful += 1
                if result.is_valid_countermodel():
                    valid += 1
                    
            results[example_name] = {
                "model_found": result.model_found,
                "valid": result.is_valid_countermodel() if result.model_found else None,
                "time": elapsed,
                "error": result.error_message
            }
            
            print(f"  {example_name}: {'✓' if result.model_found else '✗'} " +
                  f"{'(valid)' if result.model_found and result.is_valid_countermodel() else '(invalid)' if result.model_found else ''} " +
                  f"{elapsed:.3f}s")
                  
        except Exception as e:
            results[example_name] = {
                "model_found": False,
                "valid": None,
                "time": time.time() - start_time,
                "error": str(e)
            }
            print(f"  {example_name}: ✗ (error: {str(e)[:50]}...)")
    
    print(f"\nSummary for {strategy_name}:")
    print(f"  Total examples: {len(complex_examples)}")
    print(f"  Models found: {successful}/{len(complex_examples)} ({successful/len(complex_examples)*100:.1f}%)")
    print(f"  Valid models: {valid}/{successful if successful > 0 else 1} ({valid/successful*100 if successful > 0 else 0:.1f}%)")
    print(f"  Total time: {total_time:.3f}s")
    print(f"  Average time: {total_time/len(complex_examples):.3f}s")
    
    return results

def main():
    """Test all new strategies on complex examples."""
    print("Testing new exclusion strategies on complex examples...")
    print("=" * 60)
    
    strategies_to_test = ["SK", "CD", "MS", "UF"]
    all_results = {}
    
    for strategy in strategies_to_test:
        all_results[strategy] = test_strategy_on_complex_examples(strategy)
    
    # Compare results
    print("\n" + "=" * 60)
    print("COMPARATIVE ANALYSIS")
    print("=" * 60)
    
    # Check if results differ
    differences_found = False
    for example_name in complex_examples:
        results_for_example = {
            strategy: all_results[strategy][example_name]["model_found"] 
            for strategy in strategies_to_test
        }
        
        if len(set(results_for_example.values())) > 1:
            differences_found = True
            print(f"\nDifference found in {example_name}:")
            for strategy in strategies_to_test:
                result = all_results[strategy][example_name]
                print(f"  {strategy}: {'Model found' if result['model_found'] else 'No model'} " +
                      f"({'valid' if result['valid'] else 'invalid' if result['valid'] is False else 'N/A'})")
    
    if not differences_found:
        print("\nNo differences found - all strategies produced identical results!")
        
    # Performance comparison
    print("\n" + "-" * 40)
    print("Performance Comparison:")
    for strategy in strategies_to_test:
        total_time = sum(r["time"] for r in all_results[strategy].values())
        print(f"  {strategy}: {total_time:.3f}s total")

if __name__ == "__main__":
    main()