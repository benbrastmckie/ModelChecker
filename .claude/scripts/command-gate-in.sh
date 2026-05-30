#!/usr/bin/env bash
# command-gate-in.sh — CHECKPOINT 1: Session generation, task lookup, and terminal status guard
#
# Usage: source .claude/scripts/command-gate-in.sh "$task_number" "$operation"
#
# IMPORTANT: This script MUST be sourced (not called as a subprocess) because
# it exports variables into the calling shell. Source it within a single Bash
# tool invocation so the exported variables are visible to subsequent commands
# in that same invocation.
#
# Arguments:
#   $1  task_number — The numeric task ID to look up
#   $2  operation   — "research" | "plan" | "implement" | "revise"
#
# Exported Variables:
#   SESSION_ID    — sess_{timestamp}_{random}
#   TASK_TYPE     — Task type from state.json (e.g., "general", "meta", "neovim")
#   TASK_STATUS   — Current task status from state.json
#   PROJECT_NAME  — Project slug from state.json
#   DESCRIPTION   — Task description from state.json
#   PADDED_NUM    — Zero-padded task number (e.g., "007" for task 7)
#
# Exit Codes:
#   0   — Success; all exports set
#   1   — Task not found or terminal status
#
# Downstream dependencies:
#   Task 594 (skill-base.sh) will source this script.

gate_in() {
  local task_number="$1"
  local operation="$2"

  # Generate session ID
  SESSION_ID="sess_$(date +%s)_$(od -An -N3 -tx1 /dev/urandom | tr -d ' \n')"

  # Pad task number
  PADDED_NUM=$(printf "%03d" "$task_number")

  # Look up task in state.json
  local task_data
  task_data=$(jq -c --argjson num "$task_number" \
    '.active_projects[] | select(.project_number == $num)' \
    specs/state.json)

  if [ -z "$task_data" ]; then
    echo "ERROR: Task $task_number not found in state.json" >&2
    return 1
  fi

  TASK_TYPE=$(echo "$task_data" | jq -r '.task_type // "general"')
  TASK_STATUS=$(echo "$task_data" | jq -r '.status')
  PROJECT_NAME=$(echo "$task_data" | jq -r '.project_name')
  DESCRIPTION=$(echo "$task_data" | jq -r '.description // ""')

  # Guard: terminal status check
  case "$TASK_STATUS" in
    completed|abandoned|expanded)
      echo "ABORT: Task $task_number is in terminal status: $TASK_STATUS" >&2
      echo "  Use --force to override (implement only), or check task status with /task --sync" >&2
      return 1
      ;;
  esac

  # Display operation header
  local op_label
  op_label=$(echo "$operation" | tr '[:lower:]' '[:upper:]')
  echo "[$op_label] Task $task_number: $PROJECT_NAME"

  export SESSION_ID TASK_TYPE TASK_STATUS PROJECT_NAME DESCRIPTION PADDED_NUM
}

gate_in "$1" "$2"
