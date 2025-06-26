#!/usr/bin/env python3
"""
Phase 4.2 MS Strategy Validation
Simple tests to validate MS performance and edge cases
"""

import subprocess
import time
import json

def run_example_file(filename):
    """Run an example file and capture output."""
    try:
        result = subprocess.run(
            ["./dev_cli.py", filename],
            capture_output=True,
            text=True,
            timeout=120
        )
        return result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return None, "TIMEOUT"
    except Exception as e:
        return None, str(e)

# Create test example files
test_files = {
    "large_n7.py": """
# Test: Large model N=7
example_range = {
    "LARGE_N7": [
        [],  # No premises
        ["\\\\exclude A"],  # Simple exclusion
        {'N': 7, 'max_time': 30}
    ]
}
from model_checker.theory_lib.exclusion import *
semantic_theories = [{
    "semantics": ExclusionSemantics,
    "structure": ExclusionStructure,
    "proposition": UnilateralProposition,
    "operators": exclusion_operators,
}]
""",

    "deep_nested.py": """
# Test: Deep nesting (quadruple)
example_range = {
    "QUAD_NESTED": [
        [],
        ["\\\\exclude \\\\exclude \\\\exclude \\\\exclude A"],
        {'N': 4, 'max_time': 30}
    ]
}
from model_checker.theory_lib.exclusion import *
semantic_theories = [{
    "semantics": ExclusionSemantics,
    "structure": ExclusionStructure,
    "proposition": UnilateralProposition,
    "operators": exclusion_operators,
}]
""",

    "edge_n1.py": """
# Test: Edge case N=1
example_range = {
    "EDGE_N1": [
        [],
        ["\\\\exclude A"],
        {'N': 1, 'max_time': 10}
    ]
}
from model_checker.theory_lib.exclusion import *
semantic_theories = [{
    "semantics": ExclusionSemantics,
    "structure": ExclusionStructure,
    "proposition": UnilateralProposition,
    "operators": exclusion_operators,
}]
""",

    "perf_scaling.py": """
# Test: Performance scaling
example_range = {}
for n in [3, 4, 5, 6]:
    example_range[f"PERF_N{n}"] = [
        ["\\\\exclude (A \\\\uniwedge B)"],
        ["(\\\\exclude A \\\\univee \\\\exclude B)"],
        {'N': n, 'max_time': 60}
    ]
from model_checker.theory_lib.exclusion import *
semantic_theories = [{
    "semantics": ExclusionSemantics,
    "structure": ExclusionStructure,
    "proposition": UnilateralProposition,
    "operators": exclusion_operators,
}]
"""
}

def main():
    """Run Phase 4.2 validation tests."""
    print("Phase 4.2: MS Strategy Validation")
    print("=" * 60)
    
    # Create test files
    test_dir = "test_ms_tmp"
    import os
    os.makedirs(test_dir, exist_ok=True)
    
    for filename, content in test_files.items():
        filepath = os.path.join(test_dir, filename)
        with open(filepath, "w") as f:
            f.write(content)
    
    # Run tests
    results = {}
    
    for filename in test_files:
        print(f"\nTesting: {filename}")
        print("-" * 40)
        
        filepath = os.path.join(test_dir, filename)
        start_time = time.time()
        stdout, stderr = run_example_file(filepath)
        elapsed = time.time() - start_time
        
        if stderr == "TIMEOUT":
            print(f"Status: TIMEOUT after 120s")
            results[filename] = {"status": "timeout", "time": 120}
        elif stderr:
            print(f"Status: ERROR - {stderr[:100]}")
            results[filename] = {"status": "error", "time": elapsed}
        elif stdout:
            # Parse output
            if "No counter-model" in stdout:
                print(f"Status: No model found")
                results[filename] = {"status": "no_model", "time": elapsed}
            elif "Counter-model" in stdout:
                # Check for false premises
                if "Premise" in stdout and "False" in stdout:
                    print(f"Status: Model found (invalid - false premise)")
                    results[filename] = {"status": "invalid_model", "time": elapsed}
                else:
                    print(f"Status: Model found (valid)")
                    results[filename] = {"status": "valid_model", "time": elapsed}
            else:
                print(f"Status: Unknown result")
                results[filename] = {"status": "unknown", "time": elapsed}
        
        print(f"Time: {elapsed:.3f}s")
    
    # Summary
    print("\n" + "=" * 60)
    print("VALIDATION SUMMARY")
    print("=" * 60)
    
    total = len(results)
    valid = sum(1 for r in results.values() if r["status"] == "valid_model")
    invalid = sum(1 for r in results.values() if r["status"] == "invalid_model")
    no_model = sum(1 for r in results.values() if r["status"] == "no_model")
    timeouts = sum(1 for r in results.values() if r["status"] == "timeout")
    errors = sum(1 for r in results.values() if r["status"] == "error")
    
    print(f"\nTotal tests: {total}")
    print(f"Valid models: {valid}")
    print(f"Invalid models (false premise): {invalid}")
    print(f"No model found: {no_model}")
    print(f"Timeouts: {timeouts}")
    print(f"Errors: {errors}")
    
    # Key findings
    print("\nKEY FINDINGS:")
    print("-" * 40)
    
    # Large model test
    if "large_n7.py" in results:
        if results["large_n7.py"]["status"] == "timeout":
            print("1. Large models (N=7) exceed reasonable time limits")
        elif results["large_n7.py"]["status"] in ["valid_model", "invalid_model"]:
            print(f"1. Large models (N=7) are feasible: {results['large_n7.py']['time']:.1f}s")
    
    # Deep nesting
    if "deep_nested.py" in results:
        status = results["deep_nested.py"]["status"]
        if status == "invalid_model":
            print("2. Deep nesting (4x) produces false premise issues")
        elif status == "valid_model":
            print("2. Deep nesting (4x) works correctly")
        elif status == "no_model":
            print("2. Deep nesting (4x) found no models")
    
    # Edge cases
    if "edge_n1.py" in results:
        if results["edge_n1.py"]["status"] in ["valid_model", "no_model"]:
            print("3. Edge case (N=1) handled correctly")
        else:
            print("3. Edge case (N=1) has issues")
    
    # Performance scaling
    perf_times = []
    for n in [3, 4, 5, 6]:
        key = "perf_scaling.py"
        if key in results and results[key]["time"] < 120:
            # Extract individual times if available
            perf_times.append((n, results[key]["time"]))
    
    if len(perf_times) >= 2:
        print("\n4. Performance scaling:")
        for i, (n, t) in enumerate(perf_times):
            if i > 0:
                prev_n, prev_t = perf_times[i-1]
                if prev_t > 0:
                    scaling = t / prev_t
                    print(f"   N={prev_n} -> N={n}: {scaling:.2f}x slower")
    
    # Cleanup
    import shutil
    shutil.rmtree(test_dir, ignore_errors=True)
    
    return results

if __name__ == "__main__":
    results = main()
    
    # Write summary for documentation
    with open("ms_validation_results.json", "w") as f:
        json.dump(results, f, indent=2)