#!/usr/bin/env bash
# Repeat-sample validation harness for the concurrent model-building segfault fix.
#
# A segfault kills the interpreter, so in-process pytest repetition cannot detect it --
# each sample must be its own subprocess, checked by exit code. This script runs one or
# more pytest node IDs N times as separate `python -m pytest` invocations and tabulates
# exit codes, per specs/135_fix_concurrent_model_building_segfault/plans/
# 01_single-threaded-construction-guard.md Phase 4.
#
# Usage:
#   repeat_sample.sh <count> <node-id> [<node-id> ...]
#
# Example (from repo root):
#   bash specs/135_fix_concurrent_model_building_segfault/scripts/repeat_sample.sh 20 \
#     "code/tests/integration/test_performance.py::TestConcurrentPerformance::test_sequential_vs_concurrent"
#
#   bash specs/135_fix_concurrent_model_building_segfault/scripts/repeat_sample.sh 20 \
#     "code/tests/integration/test_performance.py::TestConcurrentPerformance::test_sequential_vs_concurrent" \
#     "code/tests/integration/test_timeout_resources.py::TestResourceLimits::test_concurrent_model_building"
#
# Runs are strictly serial (one subprocess at a time, waited on before starting the
# next) -- this harness never parallelizes samples, by design: parallel sampling would
# reintroduce exactly the kind of external CPU contention that this task's fix is meant
# to make irrelevant to correctness, and would also contend with any other test/CI
# activity in the same environment.
#
# Exit code categories:
#   0                    -> pass
#   139 (128+SIGSEGV=11) -> segfault
#   134 (128+SIGABRT=6)  -> abort
#   other non-zero       -> test failure or other error
#
# On any non-zero exit code, this script does NOT stop early: it completes all N runs
# so the full pattern is visible, but it prints a hard-failure banner per Phase 4's
# "any exit code 139/134/non-zero is a hard failure" rule, and the overall script exit
# code is non-zero if any sample was non-zero.

set -u

if [ "$#" -lt 2 ]; then
    echo "Usage: $0 <count> <node-id> [<node-id> ...]" >&2
    exit 64
fi

count="$1"
shift
node_ids=("$@")

if ! [[ "$count" =~ ^[0-9]+$ ]] || [ "$count" -lt 1 ]; then
    echo "Error: <count> must be a positive integer, got: $count" >&2
    exit 64
fi

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$repo_root" || { echo "Error: could not cd to repo root ($repo_root)" >&2; exit 1; }

echo "Repeat-sample run: $count invocations of:"
printf '  %s\n' "${node_ids[@]}"
echo "Repo root: $repo_root"
echo "Command template: PYTHONFAULTHANDLER=1 PYTHONPATH=code/src python -m pytest <node-ids> -q"
echo

declare -a exit_codes=()
any_nonzero=0

for i in $(seq 1 "$count"); do
    log_file="$(mktemp)"
    PYTHONFAULTHANDLER=1 PYTHONPATH=code/src python -m pytest "${node_ids[@]}" -q \
        > "$log_file" 2>&1
    code=$?
    exit_codes+=("$code")

    case "$code" in
        0)
            status="pass"
            ;;
        139)
            status="SEGFAULT (SIGSEGV)"
            any_nonzero=1
            ;;
        134)
            status="ABORT (SIGABRT)"
            any_nonzero=1
            ;;
        *)
            status="FAIL (exit $code)"
            any_nonzero=1
            ;;
    esac

    printf 'Run %2d/%d: exit=%d (%s)\n' "$i" "$count" "$code" "$status"

    if [ "$code" -ne 0 ]; then
        echo "  --- hard failure: captured output follows ---"
        sed 's/^/  | /' "$log_file"
        echo "  --- end captured output ---"
    fi

    rm -f "$log_file"
done

echo
pass_count=0
for code in "${exit_codes[@]}"; do
    if [ "$code" -eq 0 ]; then
        pass_count=$((pass_count + 1))
    fi
done

echo "Summary: $pass_count/$count passed (exit code 0)."
if [ "$any_nonzero" -ne 0 ]; then
    echo "HARD FAILURE: at least one run did not exit 0. Guard coverage is likely incomplete." >&2
    echo "Exit codes: ${exit_codes[*]}" >&2
    exit 1
fi

echo "All $count runs passed."
exit 0
