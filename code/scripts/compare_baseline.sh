#!/bin/bash
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
