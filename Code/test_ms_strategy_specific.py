#!/usr/bin/env python3
"""
Test script specifically for MS strategy with various N values and edge cases.
"""

import sys
import os
import time
import json

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from model_checker import ModelConstraints, Syntax
from model_checker.theory_lib.exclusion import (
    ExclusionStructure,
    UnilateralProposition,
    ExclusionSemantics,
)
from model_checker.theory_lib.exclusion.operators import STRATEGY_REGISTRY, create_operator_collection
from model_checker.utils import run_strategy_test

# Define test cases
test_cases = {
    # 1. N=7 with simple exclusion
    "SIMPLE_EXCLUDE_N7": {
        "premises": [],
        "conclusions": ["\\exclude A"],
        "settings": {'N': 7, 'max_time': 10}
    },
    
    # 2. N=1 edge case
    "EDGE_CASE_N1": {
        "premises": [],
        "conclusions": ["\\exclude A"],
        "settings": {'N': 1, 'max_time': 5}
    },
    
    # 3. Quadruple nested exclusion
    "QUADRUPLE_EXCLUDE": {
        "premises": [],
        "conclusions": ["\\exclude \\exclude \\exclude \\exclude A"],
        "settings": {'N': 4, 'max_time': 5}
    },
    
    # 4. Performance scaling tests N=3 to N=6
    "DOUBLE_EXCLUDE_N3": {
        "premises": [],
        "conclusions": ["\\exclude \\exclude A"],
        "settings": {'N': 3, 'max_time': 3}
    },
    
    "DOUBLE_EXCLUDE_N4": {
        "premises": [],
        "conclusions": ["\\exclude \\exclude A"],
        "settings": {'N': 4, 'max_time': 5}
    },
    
    "DOUBLE_EXCLUDE_N5": {
        "premises": [],
        "conclusions": ["\\exclude \\exclude A"],
        "settings": {'N': 5, 'max_time': 8}
    },
    
    "DOUBLE_EXCLUDE_N6": {
        "premises": [],
        "conclusions": ["\\exclude \\exclude A"],
        "settings": {'N': 6, 'max_time': 10}
    },
    
    # Additional complex cases for thorough testing
    "COMPLEX_EXCLUDE_N5": {
        "premises": ["\\exclude (A \\uniwedge B)"],
        "conclusions": ["(\\exclude A \\univee \\exclude B)"],
        "settings": {'N': 5, 'max_time': 8}
    },
    
    "MULTI_VAR_N6": {
        "premises": [],
        "conclusions": ["\\exclude (A \\uniwedge B \\uniwedge C)"],
        "settings": {'N': 6, 'max_time': 10}
    },
    
    # Test with identity
    "IDENTITY_N4": {
        "premises": [],
        "conclusions": ["(A \\uniequiv A)"],
        "settings": {'N': 4, 'max_time': 3}
    }
}

def test_ms_strategy():
    """Test MS strategy on specific cases."""
    print("=== Testing MS Strategy with Various N Values and Edge Cases ===")
    print("=" * 70)
    
    results = {}
    total_time = 0
    successful = 0
    valid = 0
    
    # Group results by N value for analysis
    results_by_n = {}
    
    for example_name, example_data in test_cases.items():
        print(f"\nTesting {example_name} (N={example_data['settings']['N']})...")
        start_time = time.time()
        
        example_case = [
            example_data["premises"],
            example_data["conclusions"],
            example_data["settings"]
        ]
        
        try:
            result = run_strategy_test(example_case, "MS")
            elapsed = time.time() - start_time
            total_time += elapsed
            
            n_value = example_data['settings']['N']
            if n_value not in results_by_n:
                results_by_n[n_value] = []
            
            if result.model_found:
                successful += 1
                if result.is_valid_countermodel():
                    valid += 1
                    
            result_data = {
                "model_found": result.model_found,
                "valid": result.is_valid_countermodel() if result.model_found else None,
                "time": elapsed,
                "error": result.error_message,
                "n_value": n_value,
                "formula": example_data["conclusions"][0]
            }
            
            results[example_name] = result_data
            results_by_n[n_value].append(result_data)
            
            print(f"  Result: {'✓ Model found' if result.model_found else '✗ No model'}")
            if result.model_found:
                print(f"  Valid: {'Yes' if result.is_valid_countermodel() else 'No'}")
            print(f"  Time: {elapsed:.3f}s")
            
            if result.error_message:
                print(f"  Error: {result.error_message}")
                
        except Exception as e:
            elapsed = time.time() - start_time
            result_data = {
                "model_found": False,
                "valid": None,
                "time": elapsed,
                "error": str(e),
                "n_value": example_data['settings']['N'],
                "formula": example_data["conclusions"][0]
            }
            results[example_name] = result_data
            results_by_n[example_data['settings']['N']].append(result_data)
            print(f"  Error: {str(e)[:100]}...")
    
    # Summary statistics
    print("\n" + "=" * 70)
    print("OVERALL SUMMARY")
    print("=" * 70)
    print(f"Total examples tested: {len(test_cases)}")
    print(f"Models found: {successful}/{len(test_cases)} ({successful/len(test_cases)*100:.1f}%)")
    print(f"Valid models: {valid}/{successful if successful > 0 else 1} ({valid/successful*100 if successful > 0 else 0:.1f}%)")
    print(f"Total time: {total_time:.3f}s")
    print(f"Average time: {total_time/len(test_cases):.3f}s")
    
    # Performance by N value
    print("\n" + "-" * 50)
    print("PERFORMANCE BY N VALUE")
    print("-" * 50)
    print(f"{'N':<5} {'Tests':<8} {'Success':<10} {'Avg Time':<12} {'Notes':<30}")
    print("-" * 65)
    
    for n in sorted(results_by_n.keys()):
        n_results = results_by_n[n]
        n_successful = sum(1 for r in n_results if r['model_found'])
        n_avg_time = sum(r['time'] for r in n_results) / len(n_results)
        
        notes = []
        if n == 1:
            notes.append("Edge case")
        if n >= 6:
            notes.append("Large state space")
        if any("\\exclude \\exclude \\exclude \\exclude" in r['formula'] for r in n_results):
            notes.append("Quadruple nested")
            
        print(f"{n:<5} {len(n_results):<8} {n_successful}/{len(n_results):<10} {n_avg_time:<12.3f} {', '.join(notes):<30}")
    
    # Scaling analysis for double exclusion
    print("\n" + "-" * 50)
    print("SCALING ANALYSIS: Double Exclusion (\\exclude \\exclude A)")
    print("-" * 50)
    print(f"{'N':<5} {'Time (s)':<10} {'Growth Factor':<15}")
    print("-" * 30)
    
    double_exclude_times = []
    for n in range(3, 7):
        test_name = f"DOUBLE_EXCLUDE_N{n}"
        if test_name in results:
            time_taken = results[test_name]['time']
            double_exclude_times.append((n, time_taken))
    
    for i, (n, time_taken) in enumerate(double_exclude_times):
        if i == 0:
            print(f"{n:<5} {time_taken:<10.3f} -")
        else:
            prev_time = double_exclude_times[i-1][1]
            growth = time_taken / prev_time if prev_time > 0 else 0
            print(f"{n:<5} {time_taken:<10.3f} {growth:<15.2f}x")
    
    # Save detailed results
    output_data = {
        "strategy": "MS",
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        "summary": {
            "total_tests": len(test_cases),
            "successful_models": successful,
            "valid_models": valid,
            "success_rate": successful/len(test_cases),
            "validity_rate": valid/successful if successful > 0 else 0,
            "total_time": total_time,
            "average_time": total_time/len(test_cases)
        },
        "results_by_test": results,
        "results_by_n": {str(k): v for k, v in results_by_n.items()},
        "scaling_analysis": {
            "double_exclude_times": double_exclude_times
        }
    }
    
    output_file = "ms_strategy_analysis.json"
    with open(output_file, 'w') as f:
        json.dump(output_data, f, indent=2)
    print(f"\nDetailed results saved to: {output_file}")
    
    return results

if __name__ == "__main__":
    test_ms_strategy()