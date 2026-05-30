#!/usr/bin/env bash
# compare_bimodal_baseline.sh
# Run bimodal test suite and compare pass/fail list against saved baseline.
# Usage: ./code/scripts/compare_bimodal_baseline.sh [baseline_file]
# Task 97: Bimodal constraint optimization baseline comparison tool

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
BASELINE="${1:-${REPO_ROOT}/specs/097_optimize_build_frame_constraints/baseline_results.txt}"

if [ ! -f "$BASELINE" ]; then
    echo "ERROR: Baseline file not found: $BASELINE"
    exit 1
fi

echo "Running bimodal test suite..."
cd "$REPO_ROOT"
CURRENT=$(python -m pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py \
    -v --tb=short --timeout=120 2>&1 | grep -E "PASSED|FAILED|ERROR|SKIPPED" | \
    sed 's/.*test_example_cases\[/RESULT test_example_cases[/')

# Extract baseline results (ignore comment lines)
BASELINE_RESULTS=$(grep -v '^#' "$BASELINE" | grep -v '^$' | \
    sed 's/^/RESULT /')

# Compare
CURRENT_SORTED=$(echo "$CURRENT" | sort)
BASELINE_SORTED=$(echo "$BASELINE_RESULTS" | sort | sed 's/^RESULT //')

CURRENT_NAMES=$(echo "$CURRENT" | grep -oP 'test_example_cases\[[^\]]+\]' | sort)
BASELINE_NAMES=$(grep -v '^#' "$BASELINE" | grep -v '^$' | \
    grep -oP 'test_example_cases\[[^\]]+\]' | sort)

# Check for missing tests
MISSING=$(comm -23 <(echo "$BASELINE_NAMES") <(echo "$CURRENT_NAMES") || true)
EXTRA=$(comm -13 <(echo "$BASELINE_NAMES") <(echo "$CURRENT_NAMES") || true)

# Count results
PASSED=$(echo "$CURRENT" | grep -c "PASSED" || true)
FAILED=$(echo "$CURRENT" | grep -c "FAILED" || true)
TOTAL=$((PASSED + FAILED))
BASELINE_PASSED=$(grep -c "^PASSED" "$BASELINE" || true)

echo ""
echo "=== Baseline Comparison ==="
echo "Baseline: $BASELINE_PASSED passed"
echo "Current:  $PASSED passed, $FAILED failed, total=$TOTAL"

if [ -n "$MISSING" ]; then
    echo ""
    echo "MISSING tests (in baseline but not current):"
    echo "$MISSING" | sed 's/^/  - /'
fi

if [ -n "$EXTRA" ]; then
    echo ""
    echo "EXTRA tests (in current but not baseline):"
    echo "$EXTRA" | sed 's/^/  + /'
fi

# Check for status regressions
if [ "$PASSED" -lt "$BASELINE_PASSED" ]; then
    echo ""
    echo "REGRESSIONS DETECTED: $((BASELINE_PASSED - PASSED)) fewer passing tests"
    echo ""
    echo "Failed tests:"
    echo "$CURRENT" | grep "FAILED" | sed 's/^/  FAIL: /'
    exit 1
elif [ "$PASSED" -gt "$BASELINE_PASSED" ]; then
    echo ""
    echo "IMPROVEMENT: $((PASSED - BASELINE_PASSED)) more passing tests than baseline"
else
    echo ""
    echo "OK: 0 regressions (matches baseline)"
fi

exit 0
