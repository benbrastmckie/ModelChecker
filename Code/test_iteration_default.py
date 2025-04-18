#!/usr/bin/env python3
"""Test script to verify iteration settings work with default theory.

This script tests the 'iterate', 'iteration_timeout', and 'iteration_attempts' settings
to confirm they are properly used in the model iteration mechanism for default theory.
"""

import time
import sys
import os

# Add the src directory to the Python path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), 'src')))

from model_checker.builder.example import BuildExample
from model_checker import get_theory

def test_iteration_settings():
    # Get the default theory
    theory = get_theory("default")
    
    # Define a simple formula that should have multiple models
    premises = []
    conclusions = ["p | ~p"]
    
    # Test with default iteration settings
    default_settings = {
        'N': 3,
        'max_time': 1,
        'iterate': 1,
    }
    
    # Create the example
    example_case = [premises, conclusions, default_settings]
    model = BuildExample("test_default", theory, example_case)
    
    print("\nTesting default settings (iterate=1):")
    print(f"Found {len(model.model_structures)} model(s)")
    
    # Test with increased iteration count
    iteration_settings = {
        'N': 3,
        'max_time': 1,
        'iterate': 3,
        'iteration_timeout': 0.5,
        'iteration_attempts': 2,
    }
    
    # Create the example with iteration settings
    example_case = [premises, conclusions, iteration_settings]
    model = BuildExample("test_iteration", theory, example_case)
    
    # Import the iteration function
    from model_checker.theory_lib.default.iterate import iterate_example
    
    print("\nTesting iteration settings (iterate=3, iteration_timeout=0.5, iteration_attempts=2):")
    start_time = time.time()
    model_structures = iterate_example(model, max_iterations=3)
    end_time = time.time()
    
    print(f"Found {len(model_structures)} model(s)")
    print(f"Time taken: {end_time - start_time:.2f}s")
    
    # Verify the timeout mechanism by using a very short timeout
    short_timeout_settings = {
        'N': 3,
        'max_time': 1,
        'iterate': 3,
        'iteration_timeout': 0.001,  # Very short timeout to trigger timeout handling
        'iteration_attempts': 2,
    }
    
    # Create the example with short timeout settings
    example_case = [premises, conclusions, short_timeout_settings]
    model = BuildExample("test_timeout", theory, example_case)
    
    print("\nTesting short timeout settings (iteration_timeout=0.001):")
    start_time = time.time()
    model_structures = iterate_example(model, max_iterations=3)
    end_time = time.time()
    
    print(f"Found {len(model_structures)} model(s)")
    print(f"Time taken: {end_time - start_time:.2f}s")

if __name__ == "__main__":
    test_iteration_settings()