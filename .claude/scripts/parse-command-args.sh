#!/usr/bin/env bash
# parse-command-args.sh — Superset argument parser for Claude Code commands
#
# Usage: source .claude/scripts/parse-command-args.sh "$ARGUMENTS"
#
# IMPORTANT: This script MUST be sourced (not called as a subprocess) because
# it exports variables into the calling shell. Source it within a single Bash
# tool invocation so the exported variables are visible to subsequent commands
# in that same invocation.
#
# Exported Variables:
#   TASK_NUMBERS   — space-separated list of task numbers (ranges expanded)
#   REMAINING_ARGS — remaining args string after task numbers removed
#   TEAM_MODE      — "true" or "false"
#   TEAM_SIZE      — integer 2-4 (default 2)
#   EFFORT_FLAG    — "fast", "hard", or ""
#   MODEL_FLAG     — "haiku", "sonnet", "opus", or ""
#   CLEAN_FLAG     — "true" or "false"
#   FORCE_FLAG     — "true" or "false"
#   EXPLOIT_FLAG   — "true" or "false" (--exploit mode hint for team research)
#   EXPLORE_FLAG   — "true" or "false" (--explore mode hint for team research)
#   FOCUS_PROMPT   — remaining text after all recognized flags stripped
#
# Downstream dependencies:
#   Task 594 (skill-base.sh) will source this script.
#   Task 595 (multi-task dispatch extraction) relies on TASK_NUMBERS and REMAINING_ARGS.

parse_command_args() {
  local args="$1"

  # Step 1: Extract task spec (leading digits, commas, ranges, spaces — stop at letters or --)
  # Uses bash regex to capture leading task spec before any text/flags
  local task_spec=""
  if [[ "$args" =~ ^([0-9][0-9,\ \-]*)(\ +.*)?$ ]]; then
    task_spec="${BASH_REMATCH[1]}"
  fi
  # Trim trailing whitespace and commas
  task_spec=$(echo "$task_spec" | sed 's/[, ]*$//')

  # Step 2: Expand ranges "22-24" -> "22 23 24"
  TASK_NUMBERS=""
  for token in $(echo "$task_spec" | tr ',' ' '); do
    token=$(echo "$token" | xargs)  # trim whitespace
    if [ -z "$token" ]; then
      continue
    fi
    if echo "$token" | grep -qE '^[0-9]+-[0-9]+$'; then
      start=$(echo "$token" | cut -d'-' -f1)
      end=$(echo "$token" | cut -d'-' -f2)
      for n in $(seq "$start" "$end"); do
        TASK_NUMBERS="$TASK_NUMBERS $n"
      done
    else
      TASK_NUMBERS="$TASK_NUMBERS $token"
    fi
  done
  TASK_NUMBERS=$(echo "$TASK_NUMBERS" | xargs)  # trim whitespace

  # Step 3: Strip task spec to get remaining args
  local remaining
  remaining="${args#$task_spec}"
  remaining=$(echo "$remaining" | sed 's/^[[:space:]]*//')
  REMAINING_ARGS="$remaining"

  # Step 4: Scan for flags (superset — all commands, all flags)
  TEAM_MODE="false"
  TEAM_SIZE=2
  EFFORT_FLAG=""
  MODEL_FLAG=""
  CLEAN_FLAG="false"
  FORCE_FLAG="false"
  EXPLOIT_FLAG="false"
  EXPLORE_FLAG="false"

  if [[ "$remaining" =~ --team ]]; then
    TEAM_MODE="true"
  fi
  if [[ "$remaining" =~ --team-size[[:space:]]*=?[[:space:]]*([0-9]+) ]]; then
    TEAM_SIZE="${BASH_REMATCH[1]}"
  elif [[ "$remaining" =~ --team-size[[:space:]]+([0-9]+) ]]; then
    TEAM_SIZE="${BASH_REMATCH[1]}"
  fi
  if [[ "$remaining" =~ --fast ]]; then
    EFFORT_FLAG="fast"
  fi
  if [[ "$remaining" =~ --hard ]]; then
    EFFORT_FLAG="hard"
  fi
  if [[ "$remaining" =~ --haiku ]]; then
    MODEL_FLAG="haiku"
  fi
  if [[ "$remaining" =~ --sonnet ]]; then
    MODEL_FLAG="sonnet"
  fi
  if [[ "$remaining" =~ --opus ]]; then
    MODEL_FLAG="opus"
  fi
  if [[ "$remaining" =~ --clean ]]; then
    CLEAN_FLAG="true"
  fi
  if [[ "$remaining" =~ --force ]]; then
    FORCE_FLAG="true"
  fi
  if [[ "$remaining" =~ --exploit ]]; then
    EXPLOIT_FLAG="true"
  fi
  if [[ "$remaining" =~ --explore ]]; then
    EXPLORE_FLAG="true"
  fi

  # Step 5: Strip all recognized flags to produce FOCUS_PROMPT
  FOCUS_PROMPT=$(echo "$remaining" \
    | sed 's/--team-size[[:space:]]*=*[[:space:]]*[0-9]*//g' \
    | sed 's/--team//g' \
    | sed 's/--fast//g' \
    | sed 's/--hard//g' \
    | sed 's/--haiku//g' \
    | sed 's/--sonnet//g' \
    | sed 's/--opus//g' \
    | sed 's/--clean//g' \
    | sed 's/--force//g' \
    | sed 's/--exploit//g' \
    | sed 's/--explore//g' \
    | xargs)

  # Step 6: Validate — at least one task number is required
  if [ -z "$TASK_NUMBERS" ]; then
    echo "ERROR: No task numbers found in arguments: $args" >&2
    return 1
  fi

  export TASK_NUMBERS REMAINING_ARGS TEAM_MODE TEAM_SIZE EFFORT_FLAG MODEL_FLAG CLEAN_FLAG FORCE_FLAG EXPLOIT_FLAG EXPLORE_FLAG FOCUS_PROMPT
}

parse_command_args "$1"
