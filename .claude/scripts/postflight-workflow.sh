#!/bin/bash
# postflight-workflow.sh — Unified postflight for research, plan, and implement operations
#
# Usage: bash .claude/scripts/postflight-workflow.sh TASK_NUMBER ARTIFACT_PATH [ARTIFACT_SUMMARY] OPERATION_TYPE
#
# This script parameterizes the 3 near-identical postflight scripts into a single
# implementation. The OPERATION_TYPE argument controls which status, artifact type,
# and timestamp field are used.
#
# Arguments:
#   TASK_NUMBER      Task number to update
#   ARTIFACT_PATH    Path to artifact (relative to project root)
#   ARTIFACT_SUMMARY Optional summary of artifact (or OPERATION_TYPE if 3 args)
#   OPERATION_TYPE   One of: "research", "plan", "implement"
#
# Operation Mappings:
#   research  -> status: "researched",  artifact type: "research",  timestamp field: "researched"
#   plan      -> status: "planned",     artifact type: "plan",      timestamp field: "planned"
#   implement -> status: "completed",   artifact type: "summary",   timestamp field: "completed"
#
# Uses two-step jq pattern to avoid Issue #1132 (Claude Code Bash tool escaping bug).
# See: .claude/context/patterns/jq-escaping-workarounds.md
#
# Downstream dependencies:
#   Task 594 (skill-base.sh) may call this script.
#   postflight-research.sh, postflight-plan.sh, postflight-implement.sh are now thin wrappers.

set -e

# Guard: ensure specs/tmp/ exists (prevents failures on fresh checkouts)
mkdir -p specs/tmp

# Parse arguments — handle both 3-arg (TASK_NUMBER ARTIFACT_PATH OPERATION_TYPE)
# and 4-arg (TASK_NUMBER ARTIFACT_PATH ARTIFACT_SUMMARY OPERATION_TYPE) forms
if [ $# -lt 3 ]; then
    echo "Usage: $0 TASK_NUMBER ARTIFACT_PATH [ARTIFACT_SUMMARY] OPERATION_TYPE"
    echo ""
    echo "Arguments:"
    echo "  TASK_NUMBER      Task number to update"
    echo "  ARTIFACT_PATH    Path to artifact (relative to project root)"
    echo "  ARTIFACT_SUMMARY Optional summary (omit to use OPERATION_TYPE as 3rd arg)"
    echo "  OPERATION_TYPE   research | plan | implement"
    exit 1
fi

task_number="$1"
artifact_path="$2"
state_file="specs/state.json"

# Determine if 3-arg or 4-arg form
if [ $# -eq 3 ]; then
    # 3-arg form: TASK_NUMBER ARTIFACT_PATH OPERATION_TYPE
    artifact_summary=""
    operation_type="$3"
else
    # 4-arg form: TASK_NUMBER ARTIFACT_PATH ARTIFACT_SUMMARY OPERATION_TYPE
    artifact_summary="$3"
    operation_type="$4"
fi

# Map operation type to status, artifact type, timestamp field, and default summary
case "$operation_type" in
    research)
        status_value="researched"
        artifact_type="research"
        timestamp_field="researched"
        default_summary="Research report"
        ;;
    plan)
        status_value="planned"
        artifact_type="plan"
        timestamp_field="planned"
        default_summary="Implementation plan"
        ;;
    implement)
        status_value="completed"
        artifact_type="summary"
        timestamp_field="completed"
        default_summary="Implementation summary"
        ;;
    *)
        echo "Error: Unknown operation type '$operation_type'. Expected: research, plan, implement" >&2
        exit 1
        ;;
esac

# Use default summary if not provided
if [ -z "$artifact_summary" ]; then
    artifact_summary="$default_summary"
fi

# Validate state file exists
if [ ! -f "$state_file" ]; then
    echo "Error: $state_file not found" >&2
    exit 1
fi

# Validate task exists
task_exists=$(jq -r --argjson num "$task_number" \
  '.active_projects[] | select(.project_number == $num) | .project_number' \
  "$state_file")

if [ -z "$task_exists" ]; then
    echo "Error: Task $task_number not found in state.json" >&2
    exit 1
fi

echo "Updating task $task_number with $operation_type artifact..."

# Step 1: Update status and timestamps
# Note: timestamp_field is a dynamic key — use jq --arg to inject safely
jq --arg ts "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
   --arg status "$status_value" \
   --arg ts_field "$timestamp_field" \
  '(.active_projects[] | select(.project_number == '$task_number')) |= . + {
    status: $status,
    last_updated: $ts
  } + {($ts_field): $ts}' "$state_file" > specs/tmp/state.json && mv specs/tmp/state.json "$state_file"

echo "  Status updated to '$status_value'"

# Step 2: Filter out existing artifacts of this type (two-step pattern for Issue #1132)
# Safe pattern: select(.type == "X" | not) instead of select(.type != "X")
jq --arg atype "$artifact_type" \
  '(.active_projects[] | select(.project_number == '$task_number')).artifacts =
    [(.active_projects[] | select(.project_number == '$task_number')).artifacts // [] | .[] | select(.type == $atype | not)]' \
  "$state_file" > specs/tmp/state.json && mv specs/tmp/state.json "$state_file"

# Step 3: Add new artifact
jq --arg path "$artifact_path" \
   --arg summary "$artifact_summary" \
   --arg atype "$artifact_type" \
  '(.active_projects[] | select(.project_number == '$task_number')).artifacts += [{"path": $path, "type": $atype, "summary": $summary}]' \
  "$state_file" > specs/tmp/state.json && mv specs/tmp/state.json "$state_file"

echo "  Artifact linked: $artifact_path"
echo "Done."
