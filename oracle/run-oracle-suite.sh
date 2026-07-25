#!/usr/bin/env bash
# Two-pass runner for the oracle/ test suite.
#
# The suite is split into two pytest invocations rather than run as one `-n 6`
# session: a handful of tests have a Z3 solve budget with under ~2x headroom
# over their typical solo wall-clock time, and six-way CPU contention under
# pytest-xdist can inflate solve times enough to trip that budget. The oracle
# pipeline reports a blown budget as "no countermodel" rather than as an
# error, so a contention-induced timeout silently inverts a test's verdict
# instead of failing loudly (see code/docs/core/TESTING_GUIDE.md section 8.6).
# These tests are marked `xdist_serial` (see oracle/conftest.py) and run in a
# second, non-parallel pass with zero sibling pytest workers competing for
# cores.
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

# Pass 1: everything except the contention-sensitive tests, in parallel.
# Hard-coded -n 6, not -n auto: this repository already pins a sibling suite
# (code/src/model_checker/theory_lib/bimodal/tests, see flake.nix's
# checks.default) to -n 6 for the same documented CPU-contention-flake
# reason; -n auto would mean one worker per core on a many-core machine and
# risks recreating the exact problem this split exists to avoid.
pytest "$repo_root/oracle" -n 6 -m "not xdist_serial" "$@"
pass1_status=$?

# Pass 2: the contention-sensitive tests, with no other pytest workers
# running at all -- no -n flag.
pytest "$repo_root/oracle" -m "xdist_serial" "$@"
pass2_status=$?

echo
echo "== oracle suite summary =="
if [ "$pass1_status" -eq 0 ]; then
  echo "pass 1 (parallel, -n 6, not xdist_serial): PASSED"
else
  echo "pass 1 (parallel, -n 6, not xdist_serial): FAILED (exit $pass1_status)"
fi
if [ "$pass2_status" -eq 0 ]; then
  echo "pass 2 (serial, xdist_serial):             PASSED"
else
  echo "pass 2 (serial, xdist_serial):             FAILED (exit $pass2_status)"
fi

if [ "$pass1_status" -ne 0 ] || [ "$pass2_status" -ne 0 ]; then
  exit 1
fi
exit 0
