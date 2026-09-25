#!/usr/bin/env bash
# Two-pass runner for the oracle/ test suite -- the GATING variant.
#
# Both passes now pass pytest's own `-rs` (print skip reasons) and, via
# oracle/conftest.py's pytest_runtest_logreport/pytest_terminal_summary
# hooks, print a `== ORACLE TIMEOUT-SKIP INVENTORY ==` section classifying
# every timeout-conditional skip as [KNOWN] / [NEW] / [RESOLVED] -- see
# code/docs/core/TESTING_GUIDE.md section 8.8's "Timeout-skip inventory"
# subsection for the full contract. This is reporting-only: it adds no
# marker, never touches exit status, and never turns a skip into a failure
# -- it only makes visible what a gating run already decided but, before
# this, never printed.
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
# the same contention reason -- it WOULD run in this second pass, except its
# one test method is now additionally marked `unstable` (see
# code/docs/core/TESTING_GUIDE.md section 8.9) and both passes below
# deselect `unstable`, so it is deselected from this script's gating runs
# entirely and observed instead by `.github/workflows/unstable-watch.yml`.
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
#
# Recalibration of the pass 2 default only (see
# specs/143_decide_oracle_serial_pass_timeout_capacity/reports/
# 01_serial-pass-capacity.md for the full capacity analysis). The measured
# basis above is left intact as the historical record of how 900s was set;
# this block records why it no longer fits. Note that unlike those figures,
# the measurements below were NOT taken on an idle machine.
#
# Pass 2 now carries 14 tests, not the 10 the 900s default was set for --
# four genuinely slow solves (test_mixed_and_box_next, ~44-45s, plus three
# BM_CM_4 parametrizations, ~15-24s each) were deliberately routed here via
# @pytest.mark.xdist_serial to escape real -n 6 CPU-contention failures in
# pass 1; scheduling was the correct fix and nothing was weakened to obtain
# it. Three independent measurements of the resulting 14-test population --
# 869.58s, 802.98s, and 836.37s wall clock, taken under three different
# ambient-load profiles on a continuously-active shared development machine
# (a genuinely idle machine was not obtainable) -- converge on 800-870s,
# consistently 89-97% of the superseded 900s budget. The load-sensitivity
# across those three runs is modest (an ~8% spread across the widest load
# swing observed, load average 4-11 across the runs), so this is a genuine
# capacity increase from more/heavier work, not primarily a load artifact --
# an honest capacity adjustment, not a fudge to force a green run. Following
# the same ~2x-of-measured convention as pass 1 above, applied to the
# highest observed figure for margin: 869.58s -> 1800s default (30 min),
# consistent with 8.6's "set budgets generously, not tightly" guidance.
#
# Two subsequent full-gate runs measured this pass at 958.58s (load average
# 5.4-7.5) and 847.38s (load average 1.57), both comfortably inside 1800s,
# confirming the budget. Both of those runs nonetheless failed pass 2 on
# per-formula solve timeouts unrelated to this pass-level budget -- see the
# triage record in that same task directory. Widening this budget further
# would not address those, and must not be attempted for that purpose.
#
# Headroom check after the 2026-08-11 per-formula recalibration (and_box_next
# 60000 -> 240000ms; BM_CM_4 max_time 30 -> 120s x3 tests; gating re-check
# 10000 -> 20000ms x ~4 marginal formulas; and_all_future_neg and the ternary
# serialization test relocated into this pass): the SIMULTANEOUS worst case --
# every widened budget drawn to its measured maximum in the same run, which
# requires 6+ independent worst draws to coincide -- sums to ~1450-1690s
# against the 800-1030s measured band, still under 1800s. Typical runs remain
# ~850-1150s. The one scenario exceeding 1800s (a divergent ~1-in-7 next_A
# draw consuming its full 480s leg bound) is one in which that leg's own test
# has ALREADY hard-failed, so the pass budget is not the binding constraint
# there and widening it would rescue nothing. 1800s therefore remains
# calibrated, not implicated, and is deliberately unchanged.
pass1_timeout="${ORACLE_PASS1_TIMEOUT:-1300}"
pass2_timeout="${ORACLE_PASS2_TIMEOUT:-1800}"

# Opt-in per-pass JUnit output. Unset (the default), this changes nothing:
# no flag is added and behaviour is byte-for-byte what it was before this
# hook existed. Set ORACLE_JUNIT_DIR to a directory to additionally capture
# each pass's results as JUnit XML, one file per pass so pass 2 cannot
# clobber pass 1's report. Each file is written directly by pytest's own
# --junitxml, so it reflects that pass's real exit status even under a
# `timeout --kill-after` SIGKILL of a hung run.
pass1_extra_args=()
pass2_extra_args=()
if [ -n "${ORACLE_JUNIT_DIR:-}" ]; then
  pass1_extra_args+=("--junitxml=$ORACLE_JUNIT_DIR/junit-oracle-pass1.xml")
  pass2_extra_args+=("--junitxml=$ORACLE_JUNIT_DIR/junit-oracle-pass2.xml")
fi

# Opt-in per-pass timeout-skip-inventory JSON artifact, mirroring the
# ORACLE_JUNIT_DIR idiom immediately above. Unset (the default), this
# changes nothing: oracle/conftest.py's pytest_terminal_summary hook only
# writes a JSON file when ORACLE_SKIP_REPORT is set in its own environment.
# One file per pass, via a per-pass ORACLE_SKIP_REPORT value, so pass 2
# cannot clobber pass 1's report.
if [ -n "${ORACLE_SKIP_REPORT_DIR:-}" ]; then
  pass1_skip_report="$ORACLE_SKIP_REPORT_DIR/skip-report-pass1.json"
  pass2_skip_report="$ORACLE_SKIP_REPORT_DIR/skip-report-pass2.json"
else
  pass1_skip_report=""
  pass2_skip_report=""
fi

# Pass 1: everything except the contention-sensitive tests and the slow
# exhaustive scan, in parallel. Hard-coded -n 6, not -n auto: this
# repository already pins a sibling suite
# (code/src/model_checker/theory_lib/bimodal/tests, see flake.nix's
# checks.default) to -n 6 for the same documented CPU-contention-flake
# reason; -n auto would mean one worker per core on a many-core machine and
# risks recreating the exact problem this split exists to avoid.
#
# "and not unstable" on BOTH passes below (TESTING_GUIDE.md section 8.9):
# this is the first oracle-tree `unstable` marking
# (TestGatingConclusiveScan::test_known_conclusive_population_self_consistent,
# xdist_serial, so it lands in pass 2 today), and this script was not
# updated when the `unstable` category was introduced -- without this
# filter, a marked test would run (and can fail) in this gating driver,
# defeating the entire point of the marker. Present on BOTH passes
# defensively, matching `.github/workflows/tests.yml` and `flake.nix`'s
# established both-passes convention, so a future `unstable` marking on a
# non-`xdist_serial` test (landing in pass 1 instead) does not silently
# reopen this same gap. Do not remove this filter as "redundant" without
# re-reading this comment and TESTING_GUIDE.md section 8.9 first.
ORACLE_SKIP_REPORT="$pass1_skip_report" timeout --kill-after=60s "$pass1_timeout" \
  pytest "$repo_root/oracle" -n 6 -m "not xdist_serial and not slow and not unstable" -rs \
    "${pass1_extra_args[@]}" "$@"
pass1_status=$?

# Pass 2: the contention-sensitive tests (still excluding `slow` and
# `unstable` -- see the comment above pass 1), with no other pytest workers
# running at all -- no -n flag.
ORACLE_SKIP_REPORT="$pass2_skip_report" timeout --kill-after=60s "$pass2_timeout" \
  pytest "$repo_root/oracle" -m "xdist_serial and not slow and not unstable" -rs \
    "${pass2_extra_args[@]}" "$@"
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
echo "== oracle suite summary (gating: slow and unstable deselected on both passes) =="
echo "pass 1 (parallel, -n 6, not xdist_serial and not slow and not unstable, budget ${pass1_timeout}s): $(_classify "$pass1_status")"
echo "pass 2 (serial, xdist_serial and not slow and not unstable, budget ${pass2_timeout}s):             $(_classify "$pass2_status")"
echo
echo "Each pass above printed its own '== ORACLE TIMEOUT-SKIP INVENTORY ==' section"
echo "(from oracle/conftest.py, see code/docs/core/TESTING_GUIDE.md section 8.8)."
echo "[NEW] and [RESOLVED] lines there are the actionable ones -- [KNOWN] lines are"
echo "already-adjudicated. A skip is always a budget/performance outcome, never"
echo "cleared by widening a solve budget."
echo
echo "Exhaustive complexity<=5 self-consistency scan (the 'slow'-marked tests"
echo "deselected above) is not part of this gating run. Run it explicitly via:"
echo "  nix develop --command bash oracle/run-oracle-exhaustive-scan.sh"

if [ "$pass1_status" -ne 0 ] || [ "$pass2_status" -ne 0 ]; then
  exit 1
fi
exit 0
