#!/usr/bin/env python3
"""Script to capture baseline outputs for model checker theories."""

import os
import sys
import subprocess
from datetime import datetime

def run_theory_examples(theory_name, iterations=3):
    """Run examples for a specific theory and capture output."""
    
    # Create a temporary test file that imports and runs the theory examples
    test_content = f"""
from model_checker import BuildExample
from model_checker.theory_lib.{theory_name} import {theory_name}_theory

# Run through all examples
if hasattr({theory_name}_theory, 'semantic_theories') and {theory_name}_theory.semantic_theories:
    # Run with semantic theories if available
    example = BuildExample('{theory_name}_test', {theory_name}_theory)
    example.set_settings({{'iterate': {iterations}}})
    example.run()
else:
    # Run normal examples
    example = BuildExample('{theory_name}_test', {theory_name}_theory)
    example.set_settings({{'iterate': {iterations}}})
    example.run()
"""
    
    # Write temporary test file
    test_file = f"test_{theory_name}_baseline.py"
    with open(test_file, 'w') as f:
        f.write(test_content)
    
    # Run the test file using dev_cli.py
    output_file = f"docs/specs/baselines/phase1/{theory_name}_examples_new.txt"
    cmd = f"./dev_cli.py {test_file}"
    
    print(f"Capturing baseline for {theory_name} with {iterations} iterations...")
    
    with open(output_file, 'w') as out:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        out.write(result.stdout)
        if result.stderr:
            out.write("\n=== STDERR ===\n")
            out.write(result.stderr)
    
    # Clean up temp file
    os.remove(test_file)
    
    return output_file

def capture_subtheory_examples(theory_name, subtheory_name, iterations=2):
    """Run examples for a specific subtheory."""
    
    test_content = f"""
from model_checker import BuildExample
from model_checker.theory_lib.{theory_name}.subtheories.{subtheory_name} import {subtheory_name}_subtheory

# Run subtheory examples
example = BuildExample('{subtheory_name}_test', {subtheory_name}_subtheory)
example.set_settings({{'iterate': {iterations}}})
example.run()
"""
    
    # Write temporary test file
    test_file = f"test_{theory_name}_{subtheory_name}_baseline.py"
    with open(test_file, 'w') as f:
        f.write(test_content)
    
    # Run the test file
    output_file = f"docs/specs/baselines/phase1/{theory_name}_{subtheory_name}_examples.txt"
    cmd = f"./dev_cli.py {test_file}"
    
    print(f"Capturing baseline for {theory_name}/{subtheory_name} with {iterations} iterations...")
    
    with open(output_file, 'w') as out:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        out.write(result.stdout)
        if result.stderr:
            out.write("\n=== STDERR ===\n")
            out.write(result.stderr)
    
    # Clean up temp file
    os.remove(test_file)
    
    return output_file

def main():
    # Ensure baseline directory exists
    os.makedirs("docs/specs/baselines/phase1", exist_ok=True)
    
    # Capture main theory baselines
    theories = ["logos", "bimodal", "exclusion", "imposition"]
    for theory in theories:
        run_theory_examples(theory, iterations=3)
    
    # Capture logos subtheory baselines
    logos_subtheories = ["constitutive", "counterfactual", "extensional", "modal", "relevance"]
    for subtheory in logos_subtheories:
        capture_subtheory_examples("logos", subtheory, iterations=2)
    
    print("\nBaseline capture complete!")
    print(f"Results saved in: docs/specs/baselines/phase1/")

if __name__ == "__main__":
    main()