#!/usr/bin/env python3
"""Simple baseline capture using direct examples.py files."""

import os
import shutil
import subprocess
from pathlib import Path

def capture_theory_baseline(theory_name, iterations=3):
    """Capture baseline for a theory by copying and running its examples.py."""
    
    # Source and destination paths
    src_path = f"src/model_checker/theory_lib/{theory_name}/examples.py"
    test_file = f"test_{theory_name}_baseline.py"
    output_file = f"docs/specs/baselines/phase1/{theory_name}_iterations.txt"
    
    if not os.path.exists(src_path):
        print(f"Warning: {src_path} not found, skipping {theory_name}")
        return None
    
    # Copy the examples file
    shutil.copy(src_path, test_file)
    
    print(f"Capturing baseline for {theory_name} with {iterations} iterations...")
    
    # Run with dev_cli.py multiple times to test iteration
    with open(output_file, 'w', encoding='utf-8') as out:
        for i in range(iterations):
            out.write(f"\n{'='*60}\n")
            out.write(f"=== ITERATION {i+1} of {iterations} ===\n")
            out.write(f"{'='*60}\n\n")
            
            cmd = ["./dev_cli.py", test_file]
            result = subprocess.run(cmd, capture_output=True, text=True)
            
            out.write(result.stdout)
            if result.stderr:
                out.write("\n=== STDERR ===\n")
                out.write(result.stderr)
    
    # Clean up
    os.remove(test_file)
    
    return output_file

def capture_subtheory_baseline(theory_name, subtheory_name, iterations=2):
    """Capture baseline for a subtheory."""
    
    # Source and destination paths
    src_path = f"src/model_checker/theory_lib/{theory_name}/subtheories/{subtheory_name}/examples.py"
    test_file = f"test_{theory_name}_{subtheory_name}_baseline.py"
    output_file = f"docs/specs/baselines/phase1/{theory_name}_{subtheory_name}_iterations.txt"
    
    if not os.path.exists(src_path):
        print(f"Warning: {src_path} not found, skipping {theory_name}/{subtheory_name}")
        return None
    
    # Copy the examples file
    shutil.copy(src_path, test_file)
    
    print(f"Capturing baseline for {theory_name}/{subtheory_name} with {iterations} iterations...")
    
    # Run with dev_cli.py multiple times
    with open(output_file, 'w', encoding='utf-8') as out:
        for i in range(iterations):
            out.write(f"\n{'='*60}\n")
            out.write(f"=== ITERATION {i+1} of {iterations} ===\n")
            out.write(f"{'='*60}\n\n")
            
            cmd = ["./dev_cli.py", test_file]
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
    
    # Capture main theory baselines
    theories = ["logos", "bimodal", "exclusion", "imposition"]
    for theory in theories:
        capture_theory_baseline(theory, iterations=3)
    
    # Capture logos subtheory baselines
    subtheories = ["constitutive", "counterfactual", "extensional", "modal", "relevance"]
    for subtheory in subtheories:
        capture_subtheory_baseline("logos", subtheory, iterations=2)
    
    # Also capture test script outputs to ensure compatibility
    print("\nCapturing test script comparison script...")
    
    comparison_script = """#!/bin/bash
# Script to compare baseline outputs with current outputs

echo "=== Baseline Comparison Script ==="
echo "This script will help compare baseline outputs with current outputs after refactoring."
echo ""

# Function to run comparison
compare_outputs() {
    local theory=$1
    local baseline_file="docs/specs/baselines/phase1/${theory}_iterations.txt"
    local current_file="docs/specs/baselines/phase1/${theory}_current.txt"
    
    echo "Comparing $theory..."
    
    # Generate current output
    python scripts/capture_baseline_simple.py --theory $theory --output $current_file
    
    # Compare
    if diff -u "$baseline_file" "$current_file" > /dev/null; then
        echo "✓ $theory: No changes detected"
    else
        echo "✗ $theory: Changes detected!"
        echo "  Run: diff -u $baseline_file $current_file"
    fi
}

# Compare all theories
for theory in logos bimodal exclusion imposition; do
    compare_outputs $theory
done
"""
    
    with open("scripts/compare_baseline.sh", "w") as f:
        f.write(comparison_script)
    
    os.chmod("scripts/compare_baseline.sh", 0o755)
    
    print("\nBaseline capture complete!")
    print(f"Results saved in: docs/specs/baselines/phase1/")
    print("Created comparison script: scripts/compare_baseline.sh")

if __name__ == "__main__":
    main()