#!/usr/bin/env bash
# Staleness check for the exhaustive oracle self-consistency scan.
#
# The exhaustive scan (oracle/run-oracle-exhaustive-scan.sh) is deliberately
# never part of the gating path -- ~60 minutes of wall clock is incompatible
# with per-commit gating, see code/docs/core/TESTING_GUIDE.md section 8.8's
# "Oracle Suite: Gating vs. Exhaustive Split". The tradeoff that split makes
# is that self-consistency drift (disagreements > 0 across the full
# complexity<=5 population) is only detectable by actually running the scan,
# so a scheduled-but-silently-broken scan (a dead cron entry, a CI job that
# stopped triggering, an operator who forgot) is the same failure mode this
# task exists to fix for the two named timeout-skip sites, just at the
# schedule level instead of the per-test level. This script is the mitigation
# the research required: absence of a fresh SCAN_COMPLETE marker must itself
# be alertable, not silently invisible.
#
# Marker existence -- never PID or process liveness -- is the only completion
# signal this script trusts, matching the contract documented in
# TESTING_GUIDE.md section 8.8 ("The JSON-artifact and completion-marker
# contract"): SCAN_COMPLETE is written via write-to-temp-then-os.replace only
# after report.json is closed, so its presence is atomic and never
# observably half-written.
#
# Usage:
#   nix develop --command bash oracle/check-scan-freshness.sh
#
# Exit status:
#   0  the newest oracle/scan-results/*/SCAN_COMPLETE marker is younger than
#      the cadence window
#   1  no marker exists at all, or the newest one is older than the cadence
#      window (default 7 days, overridable via ORACLE_SCAN_MAX_AGE_DAYS)
#
# This script only reads scan-results/ and reports; it never triggers a scan
# itself, and it never widens any solve budget or lowers any conclusiveness
# floor -- it is a reporting tool, not a remediation.
set -uo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
repo_root="$(cd "$script_dir/.." >/dev/null 2>&1 && pwd)"
scan_results_dir="$repo_root/oracle/scan-results"

max_age_days="${ORACLE_SCAN_MAX_AGE_DAYS:-7}"

echo "== oracle exhaustive-scan freshness check =="
echo "scan-results directory: $scan_results_dir"
echo "cadence window:         ${max_age_days} day(s) (override via ORACLE_SCAN_MAX_AGE_DAYS)"
echo

if [ ! -d "$scan_results_dir" ]; then
  echo "no marker: $scan_results_dir does not exist -- the exhaustive scan has"
  echo "  apparently never been run for this checkout. Run it via:"
  echo "    nix develop --command bash oracle/run-oracle-exhaustive-scan.sh"
  exit 1
fi

# Find every SCAN_COMPLETE marker and pick the newest by its parent
# directory's timestamp stamp (YYYYMMDDTHHMMSSZ, matching
# run-oracle-exhaustive-scan.sh's `date -u +%Y%m%dT%H%M%SZ` naming
# convention) -- lexicographic sort on that stamp is chronological sort,
# never PID or filesystem mtime, which a copy/restore could disturb.
newest_marker=""
newest_stamp=""
for marker in "$scan_results_dir"/*/SCAN_COMPLETE; do
  [ -f "$marker" ] || continue
  run_dir="$(basename "$(dirname "$marker")")"
  if [ -z "$newest_stamp" ] || [[ "$run_dir" > "$newest_stamp" ]]; then
    newest_stamp="$run_dir"
    newest_marker="$marker"
  fi
done

if [ -z "$newest_marker" ]; then
  echo "no marker: no SCAN_COMPLETE file found under $scan_results_dir/*/"
  echo "  A run directory without a completion marker is not evidence of a"
  echo "  completed scan -- process exit status alone is never a completion"
  echo "  verdict (see TESTING_GUIDE.md section 8.8). Run the scan via:"
  echo "    nix develop --command bash oracle/run-oracle-exhaustive-scan.sh"
  exit 1
fi

echo "newest run:  $newest_stamp"
echo "marker path: $newest_marker"
echo

# Parse the stamp (YYYYMMDDTHHMMSSZ) into a POSIX timestamp and compute age.
if [[ ! "$newest_stamp" =~ ^([0-9]{4})([0-9]{2})([0-9]{2})T([0-9]{2})([0-9]{2})([0-9]{2})Z$ ]]; then
  echo "error: run directory name '$newest_stamp' does not match the expected"
  echo "  YYYYMMDDTHHMMSSZ stamp convention -- cannot compute age. Treating as"
  echo "  stale rather than guessing."
  exit 1
fi
iso_stamp="${BASH_REMATCH[1]}-${BASH_REMATCH[2]}-${BASH_REMATCH[3]}T${BASH_REMATCH[4]}:${BASH_REMATCH[5]}:${BASH_REMATCH[6]}Z"
marker_epoch="$(date -u -d "$iso_stamp" +%s 2>/dev/null)"
now_epoch="$(date -u +%s)"

if [ -z "$marker_epoch" ]; then
  echo "error: could not parse '$iso_stamp' as a date -- treating as stale."
  exit 1
fi

age_seconds=$((now_epoch - marker_epoch))
age_days_whole=$((age_seconds / 86400))
# One decimal place without relying on bc/awk floating point availability.
age_days_tenths=$(( (age_seconds * 10 / 86400) % 10 ))
echo "age: ${age_days_whole}.${age_days_tenths} day(s)"

# Report the run's own recorded metrics, straight from SCAN_COMPLETE's JSON
# body (written by the same shared scan core report.json is written from --
# see TESTING_GUIDE.md section 8.8 -- so the two never disagree).
python3 - "$newest_marker" <<'PYEOF'
import json
import sys

path = sys.argv[1]
with open(path) as fh:
    data = json.load(fh)

print(f"disagreements:      {data.get('disagreements', '<missing>')}")
print(f"conclusive:         {data.get('conclusive', '<missing>')} / {data.get('total_formulas', '<missing>')}")
print(f"timeout_count:      {data.get('timeout_count', '<missing>')}")
print(f"wall_clock_seconds: {data.get('wall_clock_seconds', '<missing>')}")

if data.get("disagreements", None) != 0:
    print()
    print("WARNING: the newest recorded run has disagreements != 0. This script")
    print("  only checks freshness, not correctness -- a stale-but-clean run and")
    print("  a fresh-but-disagreeing run are both worth separate attention. See")
    print("  code/docs/core/TESTING_GUIDE.md section 8.8's hard constraint: never")
    print("  weaken an assertion or lower a floor in response to this.")
PYEOF
echo

max_age_seconds=$((max_age_days * 86400))
if [ "$age_seconds" -gt "$max_age_seconds" ]; then
  echo "STALE: newest run is ${age_days_whole}.${age_days_tenths} day(s) old, exceeding the"
  echo "  ${max_age_days}-day cadence window. Run a fresh scan via:"
  echo "    nix develop --command bash oracle/run-oracle-exhaustive-scan.sh"
  exit 1
fi

echo "FRESH: newest run is within the ${max_age_days}-day cadence window."
exit 0
