#!/usr/bin/env python3
"""
Simple MS Strategy Test - Phase 4.2 Validation
Tests MS strategy with edge cases and performance scenarios
"""

import time

# Test 1: Large model (N=7)
print("Test 1: Large Model (N=7)")
print("-" * 40)

large_model_example = [
    [],  # No premises
    ["\\exclude A"],  # Simple exclusion
    {'N': 7, 'max_time': 30}
]

# Test 2: Deep nesting
print("\nTest 2: Deep Nesting")
print("-" * 40)

deep_nested_example = [
    [],
    ["\\exclude \\exclude \\exclude \\exclude A"],
    {'N': 4, 'max_time': 30}
]

# Test 3: Edge case - minimal N
print("\nTest 3: Edge Case - Minimal N=1")
print("-" * 40)

minimal_example = [
    [],
    ["\\exclude A"],
    {'N': 1, 'max_time': 10}
]

# Test 4: Performance scaling
print("\nTest 4: Performance Scaling")
print("-" * 40)

for n in [3, 4, 5, 6]:
    print(f"\nTesting with N={n}:")
    perf_example = [
        ["\\exclude (A \\uniwedge B)"],
        ["(\\exclude A \\univee \\exclude B)"],
        {'N': n, 'max_time': 30}
    ]

# Export examples for testing
test_example_range = {
    "LARGE_MODEL": large_model_example,
    "DEEP_NESTED": deep_nested_example,
    "MINIMAL_N": minimal_example,
    "PERF_N_3": [["\\exclude (A \\uniwedge B)"], ["(\\exclude A \\univee \\exclude B)"], {'N': 3, 'max_time': 30}],
    "PERF_N_4": [["\\exclude (A \\uniwedge B)"], ["(\\exclude A \\univee \\exclude B)"], {'N': 4, 'max_time': 30}],
    "PERF_N_5": [["\\exclude (A \\uniwedge B)"], ["(\\exclude A \\univee \\exclude B)"], {'N': 5, 'max_time': 30}],
    "PERF_N_6": [["\\exclude (A \\uniwedge B)"], ["(\\exclude A \\univee \\exclude B)"], {'N': 6, 'max_time': 30}]
}

# Import necessary modules
import sys, os
current_dir = os.path.dirname(os.path.abspath(__file__))
if current_dir not in sys.path:
    sys.path.insert(0, current_dir)

from semantic import ExclusionSemantics
from model import ExclusionStructure
from syntactic import UnilateralProposition
from operators import exclusion_operators

# Semantic Theories
exclusion_theory = {
    "semantics": ExclusionSemantics,
    "structure": ExclusionStructure,
    "proposition": UnilateralProposition,
    "operators": exclusion_operators,
}

semantic_theories = [exclusion_theory]

# Test selected examples
example_range = {
    "LARGE_MODEL_N7": large_model_example,
    "DEEP_NESTED_4X": deep_nested_example,
    "MINIMAL_N1": minimal_example,
}

# Settings
use_all_frame_constraints = False
exhaust = True
save_all_models = False
print_constraints = False
max_time = 30

# Run if executed directly
if __name__ == "__main__":
    print("\nMS Strategy Edge Case Testing")
    print("=" * 60)
    print("Testing with default MS strategy...")
    print("\nNote: Run with dev_cli.py for full model checking")