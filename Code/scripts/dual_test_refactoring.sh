#!/bin/bash
# Dual testing script for model.py refactoring
# Demonstrates both test runner and dev_cli.py testing methods

set -e  # Exit on error

echo "=========================================="
echo "Dual Testing for ModelChecker Refactoring"
echo "=========================================="
echo ""

# Method 1: Test Runner (TDD approach)
echo "METHOD 1: Test Runner (TDD)"
echo "---------------------------"

echo "Running models package tests..."
./run_tests.py --package --components models

echo ""
echo "Running full regression test..."
./run_tests.py --unit --package | tail -10

# Method 2: Direct CLI Testing with dev_cli.py
echo ""
echo "METHOD 2: Direct CLI Testing (dev_cli.py)"
echo "-----------------------------------------"

# Test each theory
for theory in logos bimodal exclusion imposition; do
    echo ""
    echo "Testing $theory theory..."
    
    # Run and check for errors
    if timeout 5 ./dev_cli.py "src/model_checker/theory_lib/$theory/examples.py" 2>&1 | head -100 | grep -E "WARNING|Error|AttributeError" > /dev/null; then
        echo "✗ FAILED: Found warnings/errors in $theory"
        exit 1
    else
        echo "✓ PASSED: No warnings/errors in $theory"
    fi
done

# Test with iteration (critical for catching iterator regressions)
echo ""
echo "Testing iteration functionality..."
for i in 1 2 3; do
    echo -n "  Testing with $i iterations... "
    if timeout 10 ./dev_cli.py -i $i "src/model_checker/theory_lib/logos/examples.py" 2>&1 | head -200 | grep -E "WARNING|AttributeError" > /dev/null; then
        echo "✗ FAILED"
        exit 1
    else
        echo "✓ PASSED"
    fi
done

# Test constraint printing
echo ""
echo "Testing constraint printing..."
if timeout 5 ./dev_cli.py -p "src/model_checker/theory_lib/logos/examples.py" 2>&1 | head -100 | grep -q "constraint"; then
    echo "✓ PASSED: Constraints printing correctly"
else
    echo "✗ FAILED: No constraints found"
fi

echo ""
echo "=========================================="
echo "All dual tests completed successfully!"
echo "=========================================="