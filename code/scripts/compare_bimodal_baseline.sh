#!/usr/bin/env bash
# compare_bimodal_baseline.sh
# Run bimodal test suite and compare pass/fail list against saved baseline.
# Usage: ./code/scripts/compare_bimodal_baseline.sh [baseline_file]
# Task 97: Bimodal constraint optimization baseline comparison tool

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
# specs/097_optimize_build_frame_constraints/ was archived to specs/archive/ once
# task 97 completed; the default falls back there so running this script with no
# argument (as its own usage comment above advertises) still finds the baseline.
BASELINE="${1:-${REPO_ROOT}/specs/archive/097_optimize_build_frame_constraints/baseline_results.txt}"

if [ ! -f "$BASELINE" ]; then
    echo "ERROR: Baseline file not found: $BASELINE"
    exit 1
fi

echo "Running bimodal test suite..."
cd "$REPO_ROOT"

# Capture pytest's raw output and exit code separately.
#
# `set -euo pipefail` is deliberately kept on for the rest of this script, but the pytest run
# below MUST be exempted from it. A failing test suite makes pytest exit 1, pipefail propagates
# that through the pipeline, and `set -e` then aborts the command substitution -- so the script
# would die immediately after printing "Running bimodal test suite..." having compared nothing,
# while its caller reported "compare_bimodal_baseline.sh reported regressions". That message was
# reached without any comparison ever running. Comparing a failing suite against the baseline is
# this script's entire purpose, so exit 1 is an EXPECTED input here, not an error.
#
# Exit 1 is not blanket-suppressed: pytest's other exit codes mean the run itself is untrustworthy
# and are still hard errors, because comparing counts scraped from an interrupted or
# internally-errored run would silently understate the pass count and manufacture a fake
# regression.
#   0 = all passed, 1 = tests failed        -> both comparable, continue
#   2 = interrupted, 3 = internal error,
#   4 = usage error, 5 = no tests collected -> not comparable, fail loudly
set +e
RAW_OUTPUT=$(python -m pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py \
    -v --tb=short --timeout=120 2>&1)
PYTEST_RC=$?
set -e

if [ "$PYTEST_RC" -gt 1 ]; then
    echo "ERROR: pytest exited $PYTEST_RC (not 0 or 1), so its results are not comparable."
    case "$PYTEST_RC" in
        2) echo "  Cause: run interrupted (SIGINT or --exitfirst)." ;;
        3) echo "  Cause: internal pytest error." ;;
        4) echo "  Cause: pytest usage/command-line error." ;;
        5) echo "  Cause: no tests were collected -- check the test path and PYTHONPATH." ;;
        *) echo "  Cause: unrecognized pytest exit code." ;;
    esac
    echo ""
    echo "Last 20 lines of pytest output:"
    echo "$RAW_OUTPUT" | tail -20 | sed 's/^/  /'
    exit 2
fi

# Match only pytest's per-test progress lines (each ends in a "[ NN%]" progress
# marker), NOT the "short test summary info" section's restated FAILED/ERROR
# lines. Without this restriction, every failing test is captured twice (once
# from its progress line, once from the summary restatement), which desyncs
# CURRENT_NAMES from BASELINE_NAMES's one-line-per-test format below and makes
# comm(1) misreport the failing test's duplicate occurrence as "EXTRA" (present
# in current but not baseline) even though it is simply double-counted, not new.
CURRENT=$(echo "$RAW_OUTPUT" | grep -E "(PASSED|FAILED|ERROR|SKIPPED) *\[[ ]*[0-9]+%\]" | \
    sed 's/.*test_example_cases\[/RESULT test_example_cases[/' || true)

if [ -z "$CURRENT" ]; then
    echo "ERROR: pytest exited $PYTEST_RC but no PASSED/FAILED/ERROR/SKIPPED lines were parsed."
    echo "This usually means the -v output format changed; the comparison below would report a"
    echo "false 'all tests missing' result, so it is refused rather than reported."
    echo ""
    echo "Last 20 lines of pytest output:"
    echo "$RAW_OUTPUT" | tail -20 | sed 's/^/  /'
    exit 2
fi

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
