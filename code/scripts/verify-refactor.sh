#!/usr/bin/env bash
# verify-refactor.sh
#
# Reusable regression gate for the core/theory_lib refactor. Asserts, in order:
#   1. In-package bimodal collection count is at or above its pinned floor (never fewer tests).
#   2. Full in-package collection count is at or above its pinned floor.
#   3. Oracle collection matches its pinned total exactly, AND each of its three marker
#      populations (gating-parallel, xdist_serial, slow) matches its own pinned sub-count
#      exactly. The sub-counts catch a test silently migrating between the gating and
#      exhaustive populations, which the total alone cannot see.
#   4. The bimodal in-package suite passes in full (one retry allowed — the suite has a
#      documented single-test Z3-timing flake unrelated to code changes; see
#      specs/126_refactor_repo_core_infrastructure_theory_lib/baselines/bimodal-run.txt).
#   5. The cross-oracle accommodation guard is intact, matched by content rather than by
#      file:line: the external-defect record exists; the five ordered guard assertions in
#      test_cross_oracle_differential.py are each present exactly once and in their required
#      order; the four floor/budget constants still hold their pinned values; and every
#      xfail( marker in test_oracle_interface.py is still strict=True. This is the check that
#      makes the accommodation impossible to weaken quietly.
#   6. The GATING oracle suite passes, run through oracle/run-oracle-suite.sh so the gate
#      executes exactly what the runner defines — its marker deselects, its two-pass
#      xdist_serial split, its calibrated per-pass timeouts, and its exit-code classification.
#      A strict-xfail XPASS inside it is itself a pytest failure, so step 6 going green also
#      means the xfail set stayed strict.
#   7. code/scripts/compare_bimodal_baseline.sh reports zero regressions.
#
# Note that step 6 deliberately does NOT run the exhaustive complexity-5 sweep: those tests
# carry the `slow` marker and the runner deselects them. The exhaustive path is a separate,
# 60-90 minute workflow documented in code/docs/core/TESTING_GUIDE.md section 8.8; step 3's
# BASELINE_ORACLE_SLOW_COUNT is what keeps this gate honest about their continued existence.
#
# Exits non-zero on any deviation (fail-fast). Intended to be run at every phase/wave boundary
# of the refactor plan, not just at the start and end.
#
# Usage: bash code/scripts/verify-refactor.sh [--skip-oracle]
#   --skip-oracle   Skip the (slow, ~20-35 minute) gating oracle suite run. All of step 5's
#                    static guard checks still run. Use for fast iteration; never skip at a
#                    wave boundary.

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

# Oracle collection pins. These are EXACT-equality pins, not floors: exact equality is the
# property that makes a *disappearing* test visible, and a >= floor would pass while a test
# silently vanished. If you add, remove, or re-mark an oracle test, re-pin ALL FOUR values
# below together — the three sub-counts must always sum to the total. Re-derive them with:
#   pytest oracle --collect-only -q
#   pytest oracle --collect-only -q -m "not xdist_serial and not slow"
#   pytest oracle --collect-only -q -m "xdist_serial and not slow"
#   pytest oracle --collect-only -q -m slow
BASELINE_ORACLE_COUNT=606
BASELINE_ORACLE_PARALLEL_COUNT=594
BASELINE_ORACLE_SERIAL_COUNT=10
BASELINE_ORACLE_SLOW_COUNT=2

# Step 5 targets. Matched by content, never by line number — line-number pinning is exactly
# what went stale here before.
GUARD_FILE="oracle/bimodal_logic/tests/test_cross_oracle_differential.py"
XFAIL_SRC_FILE="oracle/bimodal_logic/tests/test_oracle_interface.py"
DEFECTS_DOC="oracle/bimodal_logic/KNOWN_EXTERNAL_DEFECTS.md"
BASELINE_XFAIL_COUNT=4

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

note "=== Step 3: oracle collection counts (total + per-marker sub-counts) ==="

# Extracts the SELECTED test count from a `--collect-only -q` summary line. pytest prints
# "606 tests collected in 0.29s" with no -m, but "594/606 tests collected (12 deselected) in
# 0.24s" once a marker expression deselects anything. In the second form the selected count is
# the numerator, so a naive '[0-9]+ tests? collected' match would read back the TOTAL for every
# sub-count and the sub-count pins would silently check nothing.
_oracle_collect_count() {
  local marker="$1" out
  if [ -n "$marker" ]; then
    out=$(PYTHONPATH=code/src python -m pytest oracle --collect-only -q -m "$marker" 2>/dev/null)
  else
    out=$(PYTHONPATH=code/src python -m pytest oracle --collect-only -q 2>/dev/null)
  fi
  printf '%s\n' "$out" \
    | grep -oE '[0-9]+(/[0-9]+)? tests? collected' \
    | head -1 \
    | grep -oE '^[0-9]+'
}

_pin_oracle_count() {
  local label="$1" actual="$2" expected="$3"
  if [ "$actual" != "$expected" ]; then
    fail "oracle ${label} collection count is '${actual:-<none>}', expected exactly ${expected} (if intentional, re-pin all four BASELINE_ORACLE_* values together)"
  else
    note "OK: oracle ${label} = ${actual} (pinned ${expected})"
  fi
}

oracle_count=$(_oracle_collect_count "")
oracle_parallel_count=$(_oracle_collect_count "not xdist_serial and not slow")
oracle_serial_count=$(_oracle_collect_count "xdist_serial and not slow")
oracle_slow_count=$(_oracle_collect_count "slow")

_pin_oracle_count "total"           "$oracle_count"          "$BASELINE_ORACLE_COUNT"
_pin_oracle_count "gating-parallel" "$oracle_parallel_count" "$BASELINE_ORACLE_PARALLEL_COUNT"
_pin_oracle_count "xdist_serial"    "$oracle_serial_count"   "$BASELINE_ORACLE_SERIAL_COUNT"
_pin_oracle_count "slow"            "$oracle_slow_count"     "$BASELINE_ORACLE_SLOW_COUNT"

# Internal consistency: the three populations must partition the suite. A mismatch here means
# a marker-configuration defect (an overlapping or unreachable marker expression), which is a
# different fault from any single count drifting.
if [ -n "$oracle_parallel_count" ] && [ -n "$oracle_serial_count" ] && [ -n "$oracle_slow_count" ] && [ -n "$oracle_count" ]; then
  oracle_subtotal=$((oracle_parallel_count + oracle_serial_count + oracle_slow_count))
  if [ "$oracle_subtotal" -ne "$oracle_count" ]; then
    fail "oracle marker sub-counts do not partition the suite: ${oracle_parallel_count} + ${oracle_serial_count} + ${oracle_slow_count} = ${oracle_subtotal}, but ${oracle_count} tests collected in total"
  else
    note "OK: sub-counts partition the suite (${oracle_parallel_count} + ${oracle_serial_count} + ${oracle_slow_count} = ${oracle_count})"
  fi
else
  fail "oracle collection produced an empty count; cannot verify the marker partition"
fi

note "=== Step 4: bimodal in-package suite (one retry allowed for documented flake) ==="
if PYTHONPATH=code/src python -m pytest code/src/model_checker/theory_lib/bimodal/tests/ -q >/tmp/verify-refactor-bimodal-1.txt 2>&1; then
  note "OK: bimodal suite green on first attempt"
elif PYTHONPATH=code/src python -m pytest code/src/model_checker/theory_lib/bimodal/tests/ -q >/tmp/verify-refactor-bimodal-2.txt 2>&1; then
  note "OK: bimodal suite green on retry (first attempt hit the documented flake)"
else
  fail "bimodal suite failed on both attempts; see /tmp/verify-refactor-bimodal-{1,2}.txt"
fi

note "=== Step 5: cross-oracle accommodation guard intact ==="

# --- 5a: the external-defect record the accommodation cites still exists ------------------
if [ ! -s "$DEFECTS_DOC" ]; then
  fail "Step 5a: ${DEFECTS_DOC} is missing or empty — the external-defect record that the accommodation depends on is gone"
else
  note "OK (5a): ${DEFECTS_DOC} present and non-empty"
fi

# --- 5b: the five guard assertions, each exactly once, in their required order -------------
# Order is asserted, not merely presence. The ordering is what makes each failure
# self-diagnosing: the conclusive-formula floor runs FIRST so that a starved solve budget is
# ruled out before any of the semantic guards below it can be blamed. Transposing them would
# leave every assertion present while destroying that property, so a presence-only check would
# wave the regression through.
GUARD_ASSERTIONS=(
  "assert conclusive >= MIN_CONCLUSIVE_TEMPORAL_BH_FORMULAS"
  "assert not mc_soundness_bug"
  "assert not unclassified"
  "assert external_bh_defect"
  "assert not bad_signature"
)
guard_prev_line=0
guard_prev_expr=""
guard_ok=true
for guard_expr in "${GUARD_ASSERTIONS[@]}"; do
  guard_hits=$(grep -cF "$guard_expr" "$GUARD_FILE" 2>/dev/null || true)
  guard_hits=${guard_hits:-0}
  if [ "$guard_hits" -ne 1 ]; then
    fail "Step 5b: guard assertion '${guard_expr}' appears ${guard_hits} time(s) in ${GUARD_FILE}, expected exactly 1"
    guard_ok=false
    continue
  fi
  guard_line=$(grep -nF "$guard_expr" "$GUARD_FILE" | head -1 | cut -d: -f1)
  if [ "$guard_line" -le "$guard_prev_line" ]; then
    fail "Step 5b: guard assertion '${guard_expr}' (line ${guard_line}) is out of order — it must follow '${guard_prev_expr}' (line ${guard_prev_line}); the ordering is what makes each failure self-diagnosing"
    guard_ok=false
  fi
  guard_prev_line=$guard_line
  guard_prev_expr=$guard_expr
done
if [ "$guard_ok" = true ]; then
  note "OK (5b): all five guard assertions present exactly once, in the required order"
fi

# --- 5c: the floor/budget constants still hold their pinned values -------------------------
# Pinned so a floor cannot be quietly lowered (or a timeout quietly widened) to turn a red
# guard green. Raising a floor is also a change and will trip this check — that is intended:
# re-pin here deliberately, with the new value recorded, rather than drifting.
GUARD_CONSTANTS=(
  "SELF_SCAN_SOLVE_TIMEOUT_MS=10000"
  "MIN_CONCLUSIVE_SCAN_FORMULAS=90"
  "MIN_CONCLUSIVE_GATING_FORMULAS=100"
  "MIN_CONCLUSIVE_TEMPORAL_BH_FORMULAS=45"
)
const_ok=true
for guard_const in "${GUARD_CONSTANTS[@]}"; do
  const_name="${guard_const%%=*}"
  const_value="${guard_const##*=}"
  if ! grep -qE "^${const_name}[[:space:]]*=[[:space:]]*${const_value}([^0-9]|\$)" "$GUARD_FILE" 2>/dev/null; then
    actual_const=$(grep -oE "^${const_name}[[:space:]]*=[[:space:]]*[0-9]+" "$GUARD_FILE" 2>/dev/null | head -1 | grep -oE '[0-9]+$')
    fail "Step 5c: ${const_name} in ${GUARD_FILE} is '${actual_const:-<not found>}', expected exactly ${const_value} — a floor or budget was changed"
    const_ok=false
  fi
done
if [ "$const_ok" = true ]; then
  note "OK (5c): all four floor/budget constants hold their pinned values"
fi

# --- 5d: every xfail( marker is still strict=True, and the count has not drifted ------------
# A non-strict xfail silently absorbs an XPASS, which is precisely how an accommodation stops
# being a guard. Both the count and the strictness are pinned.
xfail_total=$(grep -cE 'xfail\(' "$XFAIL_SRC_FILE" 2>/dev/null || true)
xfail_total=${xfail_total:-0}
xfail_strict=$(grep -cE 'xfail\([^)]*strict=True' "$XFAIL_SRC_FILE" 2>/dev/null || true)
xfail_strict=${xfail_strict:-0}
if [ "$xfail_total" -ne "$BASELINE_XFAIL_COUNT" ]; then
  fail "Step 5d: ${XFAIL_SRC_FILE} carries ${xfail_total} xfail( marker(s), expected exactly ${BASELINE_XFAIL_COUNT} (re-pin BASELINE_XFAIL_COUNT if intentional)"
elif [ "$xfail_strict" -ne "$xfail_total" ]; then
  fail "Step 5d: only ${xfail_strict} of ${xfail_total} xfail( markers in ${XFAIL_SRC_FILE} are strict=True — a non-strict xfail silently absorbs an XPASS"
else
  note "OK (5d): all ${xfail_total} xfail( markers in ${XFAIL_SRC_FILE} are strict=True"
fi

if [ "$SKIP_ORACLE" = true ]; then
  note "=== Step 6: gating oracle suite run SKIPPED (--skip-oracle) ==="
else
  note "=== Step 6: gating oracle suite (oracle/run-oracle-suite.sh) ==="
  # Delegated to the runner rather than spelled out here, so the gate cannot drift from what
  # the runner defines: the marker deselects, the two-pass xdist_serial split, the calibrated
  # per-pass timeouts, and the exit-124/137 timeout classification all live there. Invoking
  # pytest directly is what previously dragged the 60-90 minute exhaustive sweep into every
  # gating run, because oracle/ has no reachable ini file to filter the `slow` marker.
  #
  # Any non-zero runner exit is a FAILURE, never a skip and never a downgrade — including its
  # "pytest-xdist is not importable" preflight refusal, which means the gating suite did not
  # run at all and so cannot be reported as having passed.
  bash oracle/run-oracle-suite.sh >/tmp/verify-refactor-oracle.txt 2>&1
  oracle_status=$?
  if [ "$oracle_status" -eq 0 ]; then
    note "OK: gating oracle suite green across both passes (a strict-xfail XPASS would have failed this run)"
  else
    fail "gating oracle suite failed (runner exit ${oracle_status}); see /tmp/verify-refactor-oracle.txt"
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
