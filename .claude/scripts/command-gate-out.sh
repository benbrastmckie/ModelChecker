#!/usr/bin/env bash
# command-gate-out.sh — CHECKPOINT 2: Defensive status correction after skill delegation
#
# Usage: bash .claude/scripts/command-gate-out.sh "$task_number" "$operation" "$session_id"
#
# This script can be called as a subprocess (not sourced) since it only produces
# side effects (state.json updates, artifact validation) and does not export variables.
#
# Arguments:
#   $1  task_number — The numeric task ID
#   $2  operation   — "research" | "plan" | "implement"
#   $3  session_id  — The session ID (sess_{timestamp}_{hex}) from gate-in
#
# Scope: NARROW — only the shared defensive correction pattern (~25 lines).
# Implement-specific steps (completion_summary, plan file verification) stay inline
# in implement.md. Plan-specific steps (plan file status check) stay inline in plan.md.
#
# Exit Codes:
#   0 — Success (correction applied or no correction needed)
#   1 — Fatal error (state.json missing)
#
# Downstream dependencies:
#   Task 594 (skill-base.sh) may call this script.

set -e

task_number="$1"
operation="$2"
session_id="$3"
state_file="specs/state.json"

if [ ! -f "$state_file" ]; then
  echo "ERROR: $state_file not found" >&2
  exit 1
fi

# Get project name and task directory
project_name=$(jq -r --argjson num "$task_number" \
  '.active_projects[] | select(.project_number == $num) | .project_name' \
  "$state_file")
padded_num=$(printf "%03d" "$task_number")
task_dir="specs/${padded_num}_${project_name}"

# Read skill return metadata (non-blocking if missing)
meta_file="${task_dir}/.return-meta.json"
if [ ! -f "$meta_file" ]; then
  echo "WARNING: .return-meta.json not found at $meta_file — skill may have failed silently" >&2
  # Non-blocking: continue anyway (defensive correction impossible without metadata)
  exit 0
fi

skill_status=$(jq -r '.status' "$meta_file")

# Defensive status correction: map skill status to task status
# Only applies when skill reports completion but state.json is stale
case "$operation" in
  research)  expected_status="researched" ;;
  plan)      expected_status="planned" ;;
  implement) expected_status="completed" ;;
  *)         expected_status="" ;;
esac

if [ -n "$expected_status" ] && [ "$skill_status" = "implemented" ] || \
   [ "$skill_status" = "researched" ] || [ "$skill_status" = "planned" ]; then

  # Get current status from state.json using safe jq pattern (no != operator per Issue #1132)
  current_status=$(jq -r --argjson num "$task_number" \
    '.active_projects[] | select(.project_number == $num) | .status' \
    "$state_file")

  if [ "$current_status" != "$expected_status" ] && [ "$skill_status" != "partial" ] && [ "$skill_status" != "failed" ]; then
    echo "[gate-out] Defensive correction: status is '$current_status', skill reports '$skill_status'. Applying correction to '$expected_status'."
    bash .claude/scripts/update-task-status.sh postflight "$task_number" "$operation" "$session_id" 2>/dev/null || \
      echo "WARNING: update-task-status.sh failed — manual correction may be needed" >&2
  fi
fi

# Non-blocking artifact validation (link repair)
if [ -d "$task_dir" ]; then
  bash .claude/scripts/validate-artifact.sh "$task_dir" --fix 2>/dev/null || true
fi
