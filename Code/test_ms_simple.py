#!/usr/bin/env python3
"""
Simplified test script for MS strategy with specific test cases.
"""

import sys
import os
import time

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from model_checker import ModelConstraints, Syntax
from model_checker.theory_lib.exclusion import (
    ExclusionStructure,
    UnilateralProposition,
    ExclusionSemantics,
)
from model_checker.theory_lib.exclusion.operators import create_operator_collection
from model_checker.utils import run_strategy_test

print("=== Testing MS Strategy - Simplified Version ===")
print("=" * 50)

# Test 1: N=1 edge case
print("\n1. Testing N=1 edge case...")
try:
    start = time.time()
    result = run_strategy_test([[], ["\\exclude A"], {'N': 1, 'max_time': 2}], "MS")
    elapsed = time.time() - start
    print(f"   Result: {'Model found' if result.model_found else 'No model found'}")
    if result.model_found:
        print(f"   Valid: {result.is_valid_countermodel()}")
    print(f"   Time: {elapsed:.3f}s")
except Exception as e:
    print(f"   Error: {str(e)}")

# Test 2: Simple exclusion with N=7
print("\n2. Testing N=7 with simple exclusion...")
try:
    start = time.time()
    result = run_strategy_test([[], ["\\exclude A"], {'N': 7, 'max_time': 5}], "MS")
    elapsed = time.time() - start
    print(f"   Result: {'Model found' if result.model_found else 'No model found'}")
    if result.model_found:
        print(f"   Valid: {result.is_valid_countermodel()}")
    print(f"   Time: {elapsed:.3f}s")
except Exception as e:
    print(f"   Error: {str(e)}")

# Test 3: Quadruple nested exclusion
print("\n3. Testing quadruple nested exclusion...")
try:
    start = time.time()
    result = run_strategy_test([[], ["\\exclude \\exclude \\exclude \\exclude A"], {'N': 4, 'max_time': 3}], "MS")
    elapsed = time.time() - start
    print(f"   Result: {'Model found' if result.model_found else 'No model found'}")
    if result.model_found:
        print(f"   Valid: {result.is_valid_countermodel()}")
    print(f"   Time: {elapsed:.3f}s")
except Exception as e:
    print(f"   Error: {str(e)}")

# Test 4: Performance scaling from N=3 to N=6 with double exclusion
print("\n4. Performance scaling test (double exclusion):")
times = []
for n in range(3, 7):
    print(f"   N={n}...", end='', flush=True)
    try:
        start = time.time()
        result = run_strategy_test([[], ["\\exclude \\exclude A"], {'N': n, 'max_time': 3}], "MS")
        elapsed = time.time() - start
        times.append((n, elapsed, result.model_found))
        print(f" {elapsed:.3f}s ({'found' if result.model_found else 'not found'})")
    except Exception as e:
        print(f" Error: {str(e)}")
        times.append((n, None, False))

# Scaling analysis
print("\n=== Scaling Analysis ===")
print(f"{'N':<5} {'Time (s)':<10} {'Growth':<10}")
print("-" * 25)
prev_time = None
for n, t, found in times:
    if t is not None:
        if prev_time is not None and prev_time > 0:
            growth = t / prev_time
            print(f"{n:<5} {t:<10.3f} {growth:<10.2f}x")
        else:
            print(f"{n:<5} {t:<10.3f} -")
        prev_time = t
    else:
        print(f"{n:<5} Failed")

print("\n=== Test Complete ===")