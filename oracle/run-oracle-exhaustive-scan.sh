#!/usr/bin/env bash
# Explicitly-invoked exhaustive oracle self-consistency sweep.
#
# Runs the full complexity<=5 (274-formula x 2-solve)
# TestFullScanReport::test_complexity_5_scan_self_consistent scan via
# pytest, NOT via a reimplementation (Decision D2 in
# specs/138_make_oracle_suite_fast_and_observable/plans/
# 01_oracle-suite-fast-observable.md): the shared scan core
# (_generate_differential_report() in
# oracle/bimodal_logic/tests/test_cross_oracle_differential.py) already
# streams progress, and emits a JSONL side-channel, a JSON report, and a
# SCAN_COMPLETE completion marker when given an output directory via the
# ORACLE_SCAN_OUT_DIR environment variable, so driving pytest directly
# reuses that machinery instead of duplicating the enumerate-solve-compare
# loop a second time.
#
# This is NEVER part of the gating path -- oracle/run-oracle-suite.sh
# deselects `slow` on both passes; see that script's own header and
# code/docs/core/TESTING_GUIDE.md section 8.8 ("Oracle Suite: Gating vs.
# Exhaustive Split"). It costs roughly 60-90 minutes of wall clock at the
# deployed 10000ms solve budget (SELF_SCAN_SOLVE_TIMEOUT_MS in
# test_cross_oracle_differential.py) and is invoked explicitly -- e.g. to
# re-derive the known-conclusive baseline manifest after a change to the
# formula enumerator or the solve budget.
#
# Run serially (no `-n`), not under pytest-xdist: xdist buffers each
# worker's stdout until the worker finishes, so streamed per-formula
# progress lines would not appear in real time under `-n`, and Z3 solve
# times would be inflated by CPU contention with sibling workers -- the
# same contention risk oracle/run-oracle-suite.sh's `xdist_serial` pass
# already guards against (see code/docs/core/TESTING_GUIDE.md section 8.6).
#
# This script assumes it is already running inside the project's Nix
# devShell (it does not invoke `nix develop` itself): run it as
#   nix develop --command bash oracle/run-oracle-exhaustive-scan.sh
#
# Completion is established from the SCAN_COMPLETE marker under the run's
# output directory -- never from whether the pytest process exited zero. A
# `timeout`-fired kill can leave report.json half-written or entirely
# absent; only the marker's existence (written strictly after report.json
# is closed) is a sanctioned completion signal. A vanished PID is not a
# verdict.
set -uo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
repo_root="$(cd "$script_dir/.." >/dev/null 2>&1 && pwd)"

export PYTHONPATH="${PYTHONPATH:-$repo_root/code/src}"

# Budget in seconds. This is a provisional, generous ceiling (2 hours),
# not a calibrated-from-measurement value the way run-oracle-suite.sh's
# pass budgets are (see that script's Phase 6 calibration comment): the
# exhaustive scan is allowed to be slow -- this ceiling exists only to
# prevent an unattended run hanging forever, not to bound normal runtime.
timeout_budget="${ORACLE_EXHAUSTIVE_TIMEOUT:-7200}"

# Per-run timestamped output directory so concurrent or repeated runs
# cannot collide, matching oracle/scan_runner.py's default --out-dir
# convention.
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
out_dir="$repo_root/oracle/scan-results/$stamp"
mkdir -p "$out_dir"
export ORACLE_SCAN_OUT_DIR="$out_dir"

echo "== oracle exhaustive scan =="
echo "timeout budget:    ${timeout_budget}s (override via ORACLE_EXHAUSTIVE_TIMEOUT)"
echo "output directory:  $out_dir"
echo

# --kill-after=60s: if SIGTERM (sent when the budget expires) does not
# stop pytest within 60s, SIGKILL follows -- matching the same
# --kill-after usage and orphan-cleanup rationale as
# oracle/run-oracle-suite.sh.
timeout --kill-after=60s "$timeout_budget" \
  pytest "$repo_root/oracle" -m slow -s "$@"
pytest_status=$?

marker_path="$out_dir/SCAN_COMPLETE"

echo
echo "== oracle exhaustive scan summary =="
if [ "$pytest_status" -eq 124 ] || [ "$pytest_status" -eq 137 ]; then
  echo "pytest: TIMED OUT (exit $pytest_status, budget ${timeout_budget}s)"
elif [ "$pytest_status" -eq 0 ]; then
  echo "pytest: PASSED"
else
  echo "pytest: FAILED (exit $pytest_status)"
fi

if [ -f "$marker_path" ]; then
  echo "completion marker: present ($marker_path)"
  cat "$marker_path"
else
  echo "completion marker: ABSENT -- scan did not reach completion."
  echo "  (process exit status alone is never a completion verdict; see the"
  echo "   marker contract in test_cross_oracle_differential.py's module docstring.)"
fi

if [ "$pytest_status" -ne 0 ] || [ ! -f "$marker_path" ]; then
  exit 1
fi
exit 0
