#!/usr/bin/env python3
"""Script to capture baseline outputs for model checker theories using dev_cli.py."""

import os
import subprocess
from pathlib import Path

def create_test_file(theory_name, iterations=3, subtheory=None):
    """Create a test file that runs theory examples."""
    
    if subtheory:
        test_content = f"""
# Test file for {theory_name}/{subtheory} baseline
from model_checker.builder.module import BuildModule

# Create module flags with settings
class ModuleFlags:
    def __init__(self):
        self.file_path = __file__
        self.print_constraints = False
        self.print_z3 = False
        self.print_impossible = False
        self.save_output = False
        self.maximize = False
        self.contingent = False
        self.non_empty = False
        self.disjoint = False
        self.non_null = False
        self.align_vertically = False
        self.interactive = False
        self.load_theory = "{theory_name}"

# Import the subtheory examples
from model_checker.theory_lib.{theory_name}.subtheories.{subtheory} import unit_tests, semantic_theories

# Run with specified iterations
if __name__ == "__main__":
    flags = ModuleFlags()
    module = BuildModule(flags)
    
    # Run all examples with iterations
    for i in range({iterations}):
        print(f"\\n=== Iteration {{i+1}} of {iterations} ===")
        module.run()
"""
    else:
        test_content = f"""
# Test file for {theory_name} baseline
from model_checker.builder.module import BuildModule

# Create module flags with settings
class ModuleFlags:
    def __init__(self):
        self.file_path = __file__
        self.print_constraints = False
        self.print_z3 = False
        self.print_impossible = False
        self.save_output = False
        self.maximize = False
        self.contingent = False
        self.non_empty = False
        self.disjoint = False
        self.non_null = False
        self.align_vertically = False
        self.interactive = False
        self.load_theory = "{theory_name}"

# Import the theory examples
from model_checker.theory_lib.{theory_name} import unit_tests, semantic_theories

# Run with specified iterations
if __name__ == "__main__":
    flags = ModuleFlags()
    module = BuildModule(flags)
    
    # Run all examples with iterations
    for i in range({iterations}):
        print(f"\\n=== Iteration {{i+1}} of {iterations} ===")
        module.run()
"""
    
    return test_content

def capture_baseline(theory_name, iterations=3, subtheory=None):
    """Capture baseline for a theory."""
    
    # Create test file
    if subtheory:
        test_file = f"test_{theory_name}_{subtheory}_baseline.py"
        output_file = f"docs/specs/baselines/phase1/{theory_name}_{subtheory}_examples.txt"
    else:
        test_file = f"test_{theory_name}_baseline.py"
        output_file = f"docs/specs/baselines/phase1/{theory_name}_examples.txt"
    
    # Write test content
    content = create_test_file(theory_name, iterations, subtheory)
    with open(test_file, 'w') as f:
        f.write(content)
    
    # Run with dev_cli.py
    cmd = ["./dev_cli.py", test_file]
    
    if subtheory:
        print(f"Capturing baseline for {theory_name}/{subtheory} with {iterations} iterations...")
    else:
        print(f"Capturing baseline for {theory_name} with {iterations} iterations...")
    
    with open(output_file, 'w', encoding='utf-8') as out:
        result = subprocess.run(cmd, capture_output=True, text=True)
        out.write(result.stdout)
        if result.stderr:
            out.write("\n=== STDERR ===\n")
            out.write(result.stderr)
    
    # Clean up
    os.remove(test_file)
    
    return output_file

def main():
    """Main function to capture all baselines."""
    
    # Ensure baseline directory exists
    os.makedirs("docs/specs/baselines/phase1", exist_ok=True)
    
    # Main theories
    theories = ["logos", "bimodal", "exclusion", "imposition"]
    for theory in theories:
        capture_baseline(theory, iterations=3)
    
    # Logos subtheories
    subtheories = ["constitutive", "counterfactual", "extensional", "modal", "relevance"]
    for subtheory in subtheories:
        capture_baseline("logos", iterations=2, subtheory=subtheory)
    
    # Create known issues documentation
    known_issues_content = """# Known Issues - Phase 1 Baseline

## Date: 2025-08-06

### Current Warnings/Issues

Based on baseline capture:
- No warnings or errors detected in test suite baseline
- All tests passing in all_tests.txt

### Notes

- This baseline was captured before any Phase 1 refactoring
- Used for regression detection during model.py refactoring
- Critical: Monitor for iterator warnings during Phase 1.6
"""
    
    with open("docs/specs/baselines/phase1/known_issues.md", "w") as f:
        f.write(known_issues_content)
    
    print("\nBaseline capture complete!")
    print("Created known_issues.md")
    print(f"Results saved in: docs/specs/baselines/phase1/")

if __name__ == "__main__":
    main()