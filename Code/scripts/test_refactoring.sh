#!/bin/bash
# Test script for model.py refactoring - captures baseline and compares outputs

set -e  # Exit on error

BASELINE_DIR="docs/specs/baselines/phase1"

# Function to run theory examples with iteration
run_theory_test() {
    local theory=$1
    local iterations=$2
    local output_file=$3
    
    echo "Testing $theory with $iterations iterations..."
    
    # Create a minimal test file that properly loads the theory
    cat > temp_test_$theory.py << EOF
#!/usr/bin/env python3
"""Test runner for $theory theory with iterations."""

from model_checker.builder.module import BuildModule
import sys

class ModuleFlags:
    def __init__(self):
        self.file_path = "src/model_checker/theory_lib/$theory/examples.py"
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
        self.load_theory = "$theory"

# Run iterations
flags = ModuleFlags()
for i in range($iterations):
    print(f"\\n{'='*60}")
    print(f"ITERATION {i+1} of $iterations")
    print(f"{'='*60}\\n")
    
    try:
        module = BuildModule(flags)
        module.run()
    except Exception as e:
        print(f"Error during iteration {i+1}: {e}")
        import traceback
        traceback.print_exc()
EOF
    
    # Run the test
    python temp_test_$theory.py > "$output_file" 2>&1
    
    # Clean up
    rm -f temp_test_$theory.py
}

# Function to capture all baselines
capture_baselines() {
    echo "=== Capturing baselines for model.py refactoring ==="
    mkdir -p "$BASELINE_DIR"
    
    # Run comprehensive test suite
    echo "Running comprehensive test suite..."
    ./run_tests.py --unit --examples --package > "$BASELINE_DIR/all_tests_final.txt" 2>&1
    
    # Run theory tests with iterations
    for theory in logos bimodal exclusion imposition; do
        run_theory_test "$theory" 3 "$BASELINE_DIR/${theory}_final.txt"
    done
    
    # Run specific logos subtheory tests
    echo "Testing logos subtheories..."
    for subtheory in constitutive counterfactual extensional modal relevance; do
        cat > temp_test_logos_${subtheory}.py << EOF
#!/usr/bin/env python3
from model_checker.builder.module import BuildModule

class ModuleFlags:
    def __init__(self):
        self.file_path = "src/model_checker/theory_lib/logos/subtheories/$subtheory/examples.py"
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
        self.load_theory = "logos"

flags = ModuleFlags()
for i in range(2):
    print(f"\\nITERATION {i+1} of 2\\n")
    try:
        module = BuildModule(flags)
        module.run()
    except Exception as e:
        print(f"Error: {e}")
EOF
        
        python temp_test_logos_${subtheory}.py > "$BASELINE_DIR/logos_${subtheory}_final.txt" 2>&1
        rm -f temp_test_logos_${subtheory}.py
    done
    
    echo "Baseline capture complete!"
}

# Function to compare current output with baseline
compare_with_baseline() {
    local test_name=$1
    local baseline_file="$BASELINE_DIR/${test_name}_final.txt"
    local current_file="$BASELINE_DIR/${test_name}_current.txt"
    
    if [ ! -f "$baseline_file" ]; then
        echo "✗ No baseline found for $test_name"
        return 1
    fi
    
    # Filter out timestamps and other variable content
    grep -v "Time:" "$baseline_file" | grep -v "Date:" > "${baseline_file}.filtered"
    grep -v "Time:" "$current_file" | grep -v "Date:" > "${current_file}.filtered"
    
    if diff -u "${baseline_file}.filtered" "${current_file}.filtered" > /dev/null; then
        echo "✓ $test_name: No regression detected"
        rm -f "${baseline_file}.filtered" "${current_file}.filtered"
        return 0
    else
        echo "✗ $test_name: Changes detected!"
        echo "  View diff: diff -u $baseline_file $current_file"
        rm -f "${baseline_file}.filtered" "${current_file}.filtered"
        return 1
    fi
}

# Main execution
if [ "$1" == "baseline" ]; then
    capture_baselines
elif [ "$1" == "test" ]; then
    echo "=== Running regression tests ==="
    
    # Run current tests
    ./run_tests.py --unit --examples --package > "$BASELINE_DIR/all_tests_current.txt" 2>&1
    
    # Compare
    compare_with_baseline "all_tests"
    
    # Test specific theories
    for theory in logos bimodal exclusion imposition; do
        run_theory_test "$theory" 3 "$BASELINE_DIR/${theory}_current.txt"
        compare_with_baseline "$theory"
    done
else
    echo "Usage: $0 [baseline|test]"
    echo "  baseline - Capture baseline outputs"
    echo "  test     - Run tests and compare with baseline"
    exit 1
fi