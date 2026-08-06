#!/usr/bin/env bash
# Two-pass runner for the oracle/ test suite -- the GATING variant.
#
# Both passes deselect `slow` by default: `slow` marks the exhaustive
# complexity<=5 self-consistency scan and its temporal-only BH-comparison
# sibling, which together used to make every invocation of this script run
# a ~76-minute, 274-formula x 2-solve sweep with no way to observe progress
# or detect a hang short of PID liveness. That exhaustive sweep is now a
# separate, explicitly-invoked entry point: `oracle/run-oracle-exhaustive-scan.sh`
# (see code/docs/core/TESTING_GUIDE.md section 8.8, "Oracle Suite: Gating vs.
# Exhaustive Split", for the full split rationale). `oracle/` has no
# reachable ini file for pytest to read a default `-m` expression from (see
# oracle/conftest.py's own docstring on why marks are registered there
# instead), so the deselect must be spelled out explicitly on every
# invocation -- there is no ambient default to fall back on.
#
# The suite is still split into two pytest invocations rather than run as
# one `-n 6` session: a handful of tests have a Z3 solve budget with under
# ~2x headroom over their typical solo wall-clock time, and six-way CPU
# contention under pytest-xdist can inflate solve times enough to trip that
# budget. The oracle pipeline reports a blown budget as "no countermodel"
# rather than as an error, so a contention-induced timeout silently inverts
# a test's verdict instead of failing loudly (see
# code/docs/core/TESTING_GUIDE.md section 8.6). These tests are marked
# `xdist_serial` (see oracle/conftest.py) and run in a second, non-parallel
# pass with zero sibling pytest workers competing for cores. The gating
# conclusive-population scan (TestGatingConclusiveScan, see
# code/docs/core/TESTING_GUIDE.md section 8.8) is marked `xdist_serial` for
# the same contention reason and so runs in this second pass.
#
# Both passes are wrapped in `timeout --kill-after=60s BUDGET`: a hang in
# either pass must fail loudly (`TIMED OUT`, exit 124/137) rather than
# block indefinitely or be silently mistaken for success. `--kill-after=60s`
# means if SIGTERM (sent when the budget expires) does not stop pytest
# within 60s, SIGKILL follows -- this reaps orphaned xdist workers that
# would otherwise survive a bare SIGTERM to the parent (see
# code/docs/core/TESTING_GUIDE.md section 8.8 for the verification of this
# cleanup behaviour). Budgets default to values set from real measurement
# (see the "measured basis" note below) and are overridable via
# ORACLE_PASS1_TIMEOUT / ORACLE_PASS2_TIMEOUT.
#
# This script assumes it is already running inside the project's Nix devShell
# (it does not invoke `nix develop` itself): run it as
#   nix develop --command bash oracle/run-oracle-suite.sh
#
# Not `set -e`: pass 1 failing must not prevent pass 2 from running -- both
# passes' exit codes are captured and reported at the end.
set -uo pipefail

if ! python -c 'import xdist' >/dev/null 2>&1; then
  echo "error: pytest-xdist is not importable in the current environment." >&2
  echo "Re-run inside the project devShell: nix develop --command bash oracle/run-oracle-suite.sh" >&2
  exit 1
fi

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
repo_root="$(cd "$script_dir/.." >/dev/null 2>&1 && pwd)"

export PYTHONPATH="${PYTHONPATH:-$repo_root/code/src}"

# Measured basis (Phase 6 of specs/138_make_oracle_suite_fast_and_observable/
# plans/01_oracle-suite-fast-observable.md): each default is ~2x the real
# measured per-pass wall clock of the gating suite on an otherwise-idle
# machine, so a deliberate budget can be told apart from a guess.
#   pass 1 (parallel, -n 6, not xdist_serial and not slow): 649.09s measured
#     -> 1300s default.
#   pass 2 (serial, xdist_serial and not slow): 318.57s measured for the 7
#     pre-Phase-5 tests, plus 127.96s independently measured for the Phase 5
#     gating-conclusive-population test added to this pass, ~446s combined
#     -> 900s default.
# Both measurements were taken on an idle machine with no competing pytest
# processes and no other heavy CPU consumers; re-running under a heavily
# loaded shared machine (e.g. a concurrent unrelated `lean --worker` proof
# search consuming multiple cores) can push individual near-budget Z3 solves
# past SELF_SCAN_SOLVE_TIMEOUT_MS even in this serial pass, which is
# environmental contention distinct from the pytest-xdist sibling-worker
# contention this two-pass split exists to eliminate. Never widen these
# timeouts, or MIN_CONCLUSIVE_GATING_FORMULAS/MIN_CONCLUSIVE_SCAN_FORMULAS,
# to paper over a contended run -- re-run when the machine is idle instead.
pass1_timeout="${ORACLE_PASS1_TIMEOUT:-1300}"
pass2_timeout="${ORACLE_PASS2_TIMEOUT:-900}"

# Pass 1: everything except the contention-sensitive tests and the slow
# exhaustive scan, in parallel. Hard-coded -n 6, not -n auto: this
# repository already pins a sibling suite
# (code/src/model_checker/theory_lib/bimodal/tests, see flake.nix's
# checks.default) to -n 6 for the same documented CPU-contention-flake
# reason; -n auto would mean one worker per core on a many-core machine and
# risks recreating the exact problem this split exists to avoid.
timeout --kill-after=60s "$pass1_timeout" \
  pytest "$repo_root/oracle" -n 6 -m "not xdist_serial and not slow" "$@"
pass1_status=$?

# Pass 2: the contention-sensitive tests (still excluding `slow`), with no
# other pytest workers running at all -- no -n flag.
timeout --kill-after=60s "$pass2_timeout" \
  pytest "$repo_root/oracle" -m "xdist_serial and not slow" "$@"
pass2_status=$?

_classify() {
  # Prints a human label for a captured pytest/timeout exit status.
  local status="$1"
  if [ "$status" -eq 124 ] || [ "$status" -eq 137 ]; then
    echo "TIMED OUT (exit $status)"
  elif [ "$status" -eq 0 ]; then
    echo "PASSED"
  else
    echo "FAILED (exit $status)"
  fi
}

echo
echo "== oracle suite summary (gating: slow deselected on both passes) =="
echo "pass 1 (parallel, -n 6, not xdist_serial and not slow, budget ${pass1_timeout}s): $(_classify "$pass1_status")"
echo "pass 2 (serial, xdist_serial and not slow, budget ${pass2_timeout}s):             $(_classify "$pass2_status")"
echo
echo "Exhaustive complexity<=5 self-consistency scan (the 'slow'-marked tests"
echo "deselected above) is not part of this gating run. Run it explicitly via:"
echo "  nix develop --command bash oracle/run-oracle-exhaustive-scan.sh"

if [ "$pass1_status" -ne 0 ] || [ "$pass2_status" -ne 0 ]; then
  exit 1
fi
exit 0
