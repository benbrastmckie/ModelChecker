#!/usr/bin/env python3
"""
Stress Testing Script for MS (Multi-Sort) Strategy
Phase 4.2.1: Extended validation with larger models and edge cases

This script tests the MS strategy under various stress conditions:
1. Larger models (N > 6)
2. Complex nested formulas
3. Edge cases with extreme parameters
4. Performance profiling
"""

import sys
import os
import time
import traceback
from collections import defaultdict

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../../..'))

from model_checker import ModelConstraints, Syntax
from model_checker.theory_lib.exclusion import (
    ExclusionStructure,
    UnilateralProposition,
    ExclusionSemantics,
)
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker.utils import run_strategy_test

# Test categories
STRESS_TEST_CATEGORIES = {
    "LARGE_MODELS": "Testing with N > 6 (larger state spaces)",
    "DEEP_NESTING": "Testing deeply nested exclusion formulas",
    "EDGE_CASES": "Testing edge cases and extreme parameters",
    "PERFORMANCE": "Performance profiling under load"
}

# Large model tests (N > 6)
large_model_tests = {
    "LARGE_SIMPLE": {
        "premises": [],
        "conclusions": ["\\exclude A"],
        "settings": {'N': 7, 'max_time': 30},
        "description": "Simple exclusion with N=7"
    },
    
    "LARGE_COMPLEX": {
        "premises": ["(\\exclude A \\univee \\exclude B)"],
        "conclusions": ["\\exclude (A \\uniwedge B)"],
        "settings": {'N': 8, 'max_time': 60},
        "description": "Complex formula with N=8"
    },
    
    "LARGE_NESTED": {
        "premises": [],
        "conclusions": ["\\exclude \\exclude \\exclude A"],
        "settings": {'N': 7, 'max_time': 45},
        "description": "Triple nested exclusion with N=7"
    },
    
    "LARGE_MULTIPLE_VARS": {
        "premises": [],
        "conclusions": ["(\\exclude A \\uniwedge \\exclude B \\uniwedge \\exclude C \\uniwedge \\exclude D)"],
        "settings": {'N': 9, 'max_time': 90},
        "description": "Multiple variables with N=9"
    }
}

# Deep nesting tests
deep_nesting_tests = {
    "QUAD_NESTED": {
        "premises": [],
        "conclusions": ["\\exclude \\exclude \\exclude \\exclude A"],
        "settings": {'N': 5, 'max_time': 30},
        "description": "Quadruple nested exclusion"
    },
    
    "PENTA_NESTED": {
        "premises": [],
        "conclusions": ["\\exclude \\exclude \\exclude \\exclude \\exclude A"],
        "settings": {'N': 4, 'max_time': 45},
        "description": "Pentuple nested exclusion"
    },
    
    "NESTED_COMPLEX": {
        "premises": [],
        "conclusions": ["\\exclude (\\exclude A \\uniwedge \\exclude (B \\univee \\exclude C))"],
        "settings": {'N': 5, 'max_time': 40},
        "description": "Complex nested operations"
    },
    
    "NESTED_IDENTITY": {
        "premises": [],
        "conclusions": ["(\\exclude \\exclude A \\uniequiv A)"],
        "settings": {'N': 5, 'max_time': 30},
        "description": "Double negation identity"
    }
}

# Edge case tests
edge_case_tests = {
    "MINIMAL_N": {
        "premises": [],
        "conclusions": ["\\exclude A"],
        "settings": {'N': 1, 'max_time': 10},
        "description": "Minimal state space (N=1)"
    },
    
    "ALL_VARIABLES": {
        "premises": [],
        "conclusions": ["(A \\uniwedge B \\uniwedge C \\uniwedge D \\uniwedge E \\uniwedge F)"],
        "settings": {'N': 6, 'max_time': 30},
        "description": "Using all available variables"
    },
    
    "EMPTY_PREMISE_COMPLEX": {
        "premises": [],
        "conclusions": ["\\exclude (A \\uniwedge B \\uniwedge C \\uniwedge D \\uniwedge E)"],
        "settings": {'N': 6, 'max_time': 40},
        "description": "Complex conclusion with no premises"
    },
    
    "MANY_PREMISES": {
        "premises": ["\\exclude A", "\\exclude B", "\\exclude C", "\\exclude D"],
        "conclusions": ["\\exclude (A \\univee B \\univee C \\univee D)"],
        "settings": {'N': 5, 'max_time': 35},
        "description": "Many premises"
    }
}

# Performance profiling tests
performance_tests = {
    "PERF_BASELINE": {
        "premises": [],
        "conclusions": ["\\exclude A"],
        "settings": {'N': 3, 'max_time': 10},
        "description": "Baseline performance test"
    },
    
    "PERF_SCALING_4": {
        "premises": ["\\exclude (A \\uniwedge B)"],
        "conclusions": ["(\\exclude A \\univee \\exclude B)"],
        "settings": {'N': 4, 'max_time': 20},
        "description": "Performance at N=4"
    },
    
    "PERF_SCALING_5": {
        "premises": ["\\exclude (A \\uniwedge B)"],
        "conclusions": ["(\\exclude A \\univee \\exclude B)"],
        "settings": {'N': 5, 'max_time': 30},
        "description": "Performance at N=5"
    },
    
    "PERF_SCALING_6": {
        "premises": ["\\exclude (A \\uniwedge B)"],
        "conclusions": ["(\\exclude A \\univee \\exclude B)"],
        "settings": {'N': 6, 'max_time': 40},
        "description": "Performance at N=6"
    }
}

def run_stress_test_category(category_name, test_cases):
    """Run a category of stress tests and collect results."""
    print(f"\n{'='*60}")
    print(f"Running {category_name}: {STRESS_TEST_CATEGORIES[category_name]}")
    print(f"{'='*60}")
    
    results = {}
    category_stats = {
        "total": len(test_cases),
        "successful": 0,
        "valid": 0,
        "timed_out": 0,
        "errors": 0,
        "total_time": 0
    }
    
    for test_name, test_data in test_cases.items():
        print(f"\n{test_name}: {test_data['description']}")
        print("-" * 40)
        
        start_time = time.time()
        
        try:
            # Create test case
            test_case = [
                test_data["premises"],
                test_data["conclusions"],
                test_data["settings"]
            ]
            
            # Run with MS strategy (default)
            result = run_strategy_test(test_case, "MS")
            elapsed = time.time() - start_time
            
            # Collect results
            results[test_name] = {
                "model_found": result.model_found,
                "valid": result.is_valid_countermodel() if result.model_found else None,
                "time": elapsed,
                "error": result.error_message,
                "timed_out": elapsed >= test_data["settings"]["max_time"]
            }
            
            # Update stats
            category_stats["total_time"] += elapsed
            if result.model_found:
                category_stats["successful"] += 1
                if result.is_valid_countermodel():
                    category_stats["valid"] += 1
            if elapsed >= test_data["settings"]["max_time"]:
                category_stats["timed_out"] += 1
            if result.error_message:
                category_stats["errors"] += 1
            
            # Print result
            status = "✓ Model found" if result.model_found else "✗ No model"
            if result.model_found:
                validity = "(valid)" if result.is_valid_countermodel() else "(invalid - false premise)"
                status += f" {validity}"
            if elapsed >= test_data["settings"]["max_time"]:
                status += " [TIMEOUT]"
            
            print(f"  Status: {status}")
            print(f"  Time: {elapsed:.3f}s")
            print(f"  N={test_data['settings']['N']}")
            
            if result.error_message:
                print(f"  Error: {result.error_message}")
                
        except Exception as e:
            elapsed = time.time() - start_time
            results[test_name] = {
                "model_found": False,
                "valid": None,
                "time": elapsed,
                "error": str(e),
                "timed_out": False
            }
            category_stats["errors"] += 1
            category_stats["total_time"] += elapsed
            
            print(f"  Status: ✗ Exception occurred")
            print(f"  Error: {str(e)}")
            if "--verbose" in sys.argv:
                traceback.print_exc()
    
    # Print category summary
    print(f"\n{category_name} Summary:")
    print(f"  Total tests: {category_stats['total']}")
    print(f"  Models found: {category_stats['successful']}/{category_stats['total']} ({category_stats['successful']/category_stats['total']*100:.1f}%)")
    if category_stats['successful'] > 0:
        print(f"  Valid models: {category_stats['valid']}/{category_stats['successful']} ({category_stats['valid']/category_stats['successful']*100:.1f}%)")
    print(f"  Timeouts: {category_stats['timed_out']}")
    print(f"  Errors: {category_stats['errors']}")
    print(f"  Total time: {category_stats['total_time']:.3f}s")
    print(f"  Average time: {category_stats['total_time']/category_stats['total']:.3f}s")
    
    return results, category_stats

def analyze_performance_scaling(performance_results):
    """Analyze performance scaling with increasing N."""
    print("\n" + "="*60)
    print("Performance Scaling Analysis")
    print("="*60)
    
    # Extract scaling data
    scaling_data = []
    for test_name in ["PERF_BASELINE", "PERF_SCALING_4", "PERF_SCALING_5", "PERF_SCALING_6"]:
        if test_name in performance_results:
            n_value = performance_tests[test_name]["settings"]["N"]
            time_value = performance_results[test_name]["time"]
            success = performance_results[test_name]["model_found"]
            scaling_data.append((n_value, time_value, success))
    
    # Sort by N
    scaling_data.sort(key=lambda x: x[0])
    
    print("\nScaling with N (DeMorgan's Law formula):")
    print("N | Time (s) | Status")
    print("--|----------|--------")
    
    for n, t, success in scaling_data:
        status = "Success" if success else "Failed"
        print(f"{n} | {t:8.3f} | {status}")
    
    # Calculate scaling factor
    if len(scaling_data) >= 2:
        print("\nScaling factors:")
        for i in range(1, len(scaling_data)):
            n1, t1, _ = scaling_data[i-1]
            n2, t2, _ = scaling_data[i]
            if t1 > 0:
                factor = t2 / t1
                print(f"  N={n1} → N={n2}: {factor:.2f}x slower")

def main():
    """Run all stress tests for MS strategy."""
    print("MS Strategy Stress Testing Suite")
    print("Phase 4.2.1: Extended Validation")
    print("="*60)
    
    all_results = {}
    all_stats = {}
    
    # Run each category of tests
    test_categories = [
        ("LARGE_MODELS", large_model_tests),
        ("DEEP_NESTING", deep_nesting_tests),
        ("EDGE_CASES", edge_case_tests),
        ("PERFORMANCE", performance_tests)
    ]
    
    for category_name, test_cases in test_categories:
        results, stats = run_stress_test_category(category_name, test_cases)
        all_results[category_name] = results
        all_stats[category_name] = stats
    
    # Analyze performance scaling
    if "PERFORMANCE" in all_results:
        analyze_performance_scaling(all_results["PERFORMANCE"])
    
    # Overall summary
    print("\n" + "="*60)
    print("OVERALL STRESS TEST SUMMARY")
    print("="*60)
    
    total_tests = sum(stats["total"] for stats in all_stats.values())
    total_successful = sum(stats["successful"] for stats in all_stats.values())
    total_valid = sum(stats["valid"] for stats in all_stats.values())
    total_timeouts = sum(stats["timed_out"] for stats in all_stats.values())
    total_errors = sum(stats["errors"] for stats in all_stats.values())
    total_time = sum(stats["total_time"] for stats in all_stats.values())
    
    print(f"\nTotal tests run: {total_tests}")
    print(f"Models found: {total_successful}/{total_tests} ({total_successful/total_tests*100:.1f}%)")
    if total_successful > 0:
        print(f"Valid models: {total_valid}/{total_successful} ({total_valid/total_successful*100:.1f}%)")
    print(f"Timeouts: {total_timeouts}")
    print(f"Errors: {total_errors}")
    print(f"Total execution time: {total_time:.3f}s")
    
    # Key findings
    print("\nKEY FINDINGS:")
    print("-" * 40)
    
    # Check large model performance
    if "LARGE_MODELS" in all_stats:
        large_success = all_stats["LARGE_MODELS"]["successful"] / all_stats["LARGE_MODELS"]["total"]
        print(f"1. Large models (N>6): {large_success*100:.1f}% success rate")
        if all_stats["LARGE_MODELS"]["timed_out"] > 0:
            print(f"   - {all_stats['LARGE_MODELS']['timed_out']} timeouts indicate scalability limits")
    
    # Check deep nesting
    if "DEEP_NESTING" in all_stats:
        deep_success = all_stats["DEEP_NESTING"]["successful"] / all_stats["DEEP_NESTING"]["total"]
        print(f"2. Deep nesting: {deep_success*100:.1f}% success rate")
        if deep_success < 0.5:
            print("   - Deep nesting remains challenging for MS strategy")
    
    # Check edge cases
    if "EDGE_CASES" in all_stats:
        edge_success = all_stats["EDGE_CASES"]["successful"] / all_stats["EDGE_CASES"]["total"]
        print(f"3. Edge cases: {edge_success*100:.1f}% success rate")
    
    # Performance scaling
    print("4. Performance scaling: See analysis above")
    
    # Return summary for further processing
    return {
        "total_tests": total_tests,
        "success_rate": total_successful / total_tests if total_tests > 0 else 0,
        "validity_rate": total_valid / total_successful if total_successful > 0 else 0,
        "timeout_rate": total_timeouts / total_tests if total_tests > 0 else 0,
        "error_rate": total_errors / total_tests if total_tests > 0 else 0,
        "average_time": total_time / total_tests if total_tests > 0 else 0,
        "category_stats": all_stats
    }

if __name__ == "__main__":
    summary = main()
    
    # Write summary to file for documentation
    with open("ms_stress_test_results.txt", "w") as f:
        f.write("MS Strategy Stress Test Results\n")
        f.write("="*60 + "\n")
        f.write(f"Success Rate: {summary['success_rate']*100:.1f}%\n")
        f.write(f"Validity Rate: {summary['validity_rate']*100:.1f}%\n")
        f.write(f"Timeout Rate: {summary['timeout_rate']*100:.1f}%\n")
        f.write(f"Error Rate: {summary['error_rate']*100:.1f}%\n")
        f.write(f"Average Time: {summary['average_time']:.3f}s\n")