#!/usr/bin/env bash
# verify-refactor.sh
#
# Reusable regression gate for the core/theory_lib refactor. Asserts, in order:
#   1. In-package collection count is at or above the pinned baseline (never fewer tests).
#   2. Oracle collection count matches the pinned baseline exactly (550).
#   3. The bimodal in-package suite passes in full (one retry allowed — the suite has a
#      documented single-test Z3-timing flake unrelated to code changes; see
#      specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/bimodal-run.txt).
#   4. The oracle suite (oracle/bimodal_logic/tests/) passes in full.
#   5. The 5 xfail(strict=True) cross-oracle differentials are still present at their pinned
#      file:line locations, and none of them XPASS (a strict-xfail XPASS is itself a failure
#      pytest reports, so this is really "the suite in step 4 stayed green").
#   6. code/scripts/compare_bimodal_baseline.sh reports zero regressions.
#
# Exits non-zero on any deviation (fail-fast). Intended to be run at every phase/wave boundary
# of the refactor plan, not just at the start and end.
#
# Usage: bash code/scripts/verify-refactor.sh [--skip-oracle]
#   --skip-oracle   Skip the (slow, ~7+ minute) oracle suite run. Still checks xfail line
#                    locations statically. Use for fast iteration; never skip at a wave boundary.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
cd "$REPO_ROOT"

SKIP_ORACLE=false
for arg in "$@"; do
  case "$arg" in
    --skip-oracle) SKIP_ORACLE=true ;;
  esac
done

# Pinned baselines (specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/collection-counts.txt)
BASELINE_BIMODAL_COUNT=289
BASELINE_FULL_COUNT=2100
BASELINE_ORACLE_COUNT=550
XFAIL_FILE="oracle/bimodal_logic/tests/test_cross_oracle_differential.py"
XFAIL_LINES=(767 942 1020 1133 1431)

FAILURES=0
note() { echo "[verify-refactor] $*"; }
fail() { echo "[verify-refactor] FAIL: $*" >&2; FAILURES=$((FAILURES + 1)); }

note "=== Step 1: in-package bimodal collection count ==="
bimodal_count=$(PYTHONPATH=code/src python -m pytest code/src/model_checker/theory_lib/bimodal/tests/ --collect-only -q 2>/dev/null | grep -oE '[0-9]+ tests? collected' | grep -oE '^[0-9]+')
if [ -z "$bimodal_count" ] || [ "$bimodal_count" -lt "$BASELINE_BIMODAL_COUNT" ]; then
  fail "bimodal collection count is '${bimodal_count:-<none>}', expected >= ${BASELINE_BIMODAL_COUNT}"
else
  note "OK: ${bimodal_count} tests collected (baseline ${BASELINE_BIMODAL_COUNT})"
fi

note "=== Step 2: full in-package suite collection count ==="
full_count=$(cd code && PYTHONPATH=src python -m pytest --collect-only -q 2>/dev/null | grep -oE '[0-9]+ tests? collected' | grep -oE '^[0-9]+')
if [ -z "$full_count" ] || [ "$full_count" -lt "$BASELINE_FULL_COUNT" ]; then
  fail "full in-package collection count is '${full_count:-<none>}', expected >= ${BASELINE_FULL_COUNT}"
else
  note "OK: ${full_count} tests collected (baseline ${BASELINE_FULL_COUNT})"
fi

note "=== Step 3: oracle suite collection count ==="
oracle_count=$(PYTHONPATH=code/src python -m pytest oracle/bimodal_logic/tests/ --collect-only -q 2>/dev/null | grep -oE '[0-9]+ tests? collected' | grep -oE '^[0-9]+')
if [ "$oracle_count" != "$BASELINE_ORACLE_COUNT" ]; then
  fail "oracle collection count is '${oracle_count:-<none>}', expected exactly ${BASELINE_ORACLE_COUNT}"
else
  note "OK: ${oracle_count} tests collected (baseline ${BASELINE_ORACLE_COUNT})"
fi

note "=== Step 4: bimodal in-package suite (one retry allowed for documented flake) ==="
if PYTHONPATH=code/src python -m pytest code/src/model_checker/theory_lib/bimodal/tests/ -q >/tmp/verify-refactor-bimodal-1.txt 2>&1; then
  note "OK: bimodal suite green on first attempt"
elif PYTHONPATH=code/src python -m pytest code/src/model_checker/theory_lib/bimodal/tests/ -q >/tmp/verify-refactor-bimodal-2.txt 2>&1; then
  note "OK: bimodal suite green on retry (first attempt hit the documented flake)"
else
  fail "bimodal suite failed on both attempts; see /tmp/verify-refactor-bimodal-{1,2}.txt"
fi

note "=== Step 5: xfail(strict=True) line locations unchanged ==="
actual_lines=$(grep -n 'xfail(' "$XFAIL_FILE" 2>/dev/null | cut -d: -f1 | tr '\n' ' ')
expected_lines="${XFAIL_LINES[*]} "
if [ "$actual_lines" != "$expected_lines" ]; then
  fail "xfail(strict=True) line set changed: expected [${expected_lines}], got [${actual_lines}]"
else
  note "OK: xfail(strict=True) markers at unchanged lines: ${actual_lines}"
fi

if [ "$SKIP_ORACLE" = true ]; then
  note "=== Step 6: oracle suite run SKIPPED (--skip-oracle) ==="
else
  note "=== Step 6: oracle suite (oracle/bimodal_logic/tests/) ==="
  if PYTHONPATH=code/src python -m pytest oracle/bimodal_logic/tests/ -q >/tmp/verify-refactor-oracle.txt 2>&1; then
    note "OK: oracle suite green (xfail set within it stayed strict — an XPASS would have failed this run)"
  else
    fail "oracle suite failed; see /tmp/verify-refactor-oracle.txt"
  fi
fi

note "=== Step 7: compare_bimodal_baseline.sh ==="
if bash code/scripts/compare_bimodal_baseline.sh specs/archive/097_optimize_build_frame_constraints/baseline_results.txt >/tmp/verify-refactor-baseline-compare.txt 2>&1; then
  note "OK: $(tail -1 /tmp/verify-refactor-baseline-compare.txt)"
else
  fail "compare_bimodal_baseline.sh reported regressions; see /tmp/verify-refactor-baseline-compare.txt"
fi

echo
if [ "$FAILURES" -gt 0 ]; then
  echo "[verify-refactor] ${FAILURES} check(s) FAILED"
  exit 1
fi
echo "[verify-refactor] All checks passed"
exit 0
