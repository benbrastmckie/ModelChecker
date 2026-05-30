#!/bin/bash
# WezTerm task number hook for Claude Code
# Sets TASK_NUMBER user variable via OSC 1337 when Claude commands include task numbers
#
# Integration: Called from UserPromptSubmit hook in .claude/settings.json
# Requirements: wezterm with user variable support, jq for JSON parsing
#
# 3-tier logic:
#   Tier 1 (SET): Workflow command with task number(s)
#     1a: /research|plan|implement|revise|spawn + task spec (multi-task: N, N-N, N)
#     1b: /task --recover|expand|abandon|review + task spec
#     1c: /errors --fix N
#   Tier 2 (CLEAR): Any slash command without task number
#   Tier 3 (PRESERVE): Free text / follow-up (no change to TASK_NUMBER)
#
# Multi-task specs are displayed compactly: "7, 22-24, 59" -> "7,22-24,59"
#
# Note: Claude Code hooks run with redirected stdio (stdout is a socket),
# so we must write the escape sequence directly to the pane's TTY.

set -euo pipefail

# Helper: return success JSON for hook
exit_success() {
    echo '{}'
    exit 0
}

# Only run in WezTerm
if [[ -z "${WEZTERM_PANE:-}" ]]; then
    exit_success
fi

# Read hook input from stdin (Claude Code provides JSON)
HOOK_INPUT=$(cat)

# Parse user prompt from JSON input
PROMPT=$(echo "$HOOK_INPUT" | jq -r '.prompt // ""' 2>/dev/null || echo "")

# 3-tier task number logic
TASK_DISPLAY=""
SHOULD_SET=0
SHOULD_CLEAR=0

# Tier 1a: research, plan, implement, revise, spawn + task spec (supports multi-task syntax)
if [[ "$PROMPT" =~ ^[[:space:]]*/?(research|plan|implement|revise|spawn)[[:space:]]+([0-9][0-9,' '-]*) ]]; then
    TASK_SPEC="${BASH_REMATCH[2]}"
    TASK_SPEC="${TASK_SPEC%%--*}"       # strip from first "--" (removes flags like --team)
    while [[ "$TASK_SPEC" =~ [[:space:],]$ ]]; do
        TASK_SPEC="${TASK_SPEC%[[:space:],]}"   # strip trailing space/comma
    done
    TASK_DISPLAY="${TASK_SPEC// /}"     # compact: remove internal spaces
    SHOULD_SET=1

# Tier 1b: /task --recover/expand/abandon/review + task spec
elif [[ "$PROMPT" =~ ^[[:space:]]*/?(task)[[:space:]]+(--(recover|expand|abandon|review))[[:space:]]+([0-9][0-9,' '-]*) ]]; then
    TASK_SPEC="${BASH_REMATCH[4]}"
    TASK_SPEC="${TASK_SPEC%%--*}"
    while [[ "$TASK_SPEC" =~ [[:space:],]$ ]]; do
        TASK_SPEC="${TASK_SPEC%[[:space:],]}"
    done
    TASK_DISPLAY="${TASK_SPEC// /}"
    SHOULD_SET=1

# Tier 1c: /errors --fix N
elif [[ "$PROMPT" =~ ^[[:space:]]*/?(errors)[[:space:]]+--fix[[:space:]]+([0-9]+) ]]; then
    TASK_DISPLAY="${BASH_REMATCH[2]}"
    SHOULD_SET=1

# Tier 2: Any other slash command (new session context, no task number) -> clear
elif [[ "$PROMPT" =~ ^[[:space:]]*/[a-zA-Z] ]]; then
    SHOULD_CLEAR=1

# Tier 3: Free text / follow-up -> preserve TASK_NUMBER (implicit no-op)
fi

# Get the TTY for the current pane from WezTerm CLI
# Claude Code hooks have redirected stdio, so we cannot use /dev/tty
PANE_TTY=$(wezterm cli list --format=json 2>/dev/null | \
    jq -r ".[] | select(.pane_id == $WEZTERM_PANE) | .tty_name" 2>/dev/null || echo "")

# Check if we found a writable TTY
if [[ -z "$PANE_TTY" ]] || [[ ! -w "$PANE_TTY" ]]; then
    exit_success
fi

if [[ "$SHOULD_SET" -eq 1 ]]; then
    # Set TASK_NUMBER user variable via OSC 1337
    # Format: OSC 1337 ; SetUserVar=name=base64_value ST
    TASK_VALUE=$(echo -n "$TASK_DISPLAY" | base64 | tr -d '\n')
    printf '\033]1337;SetUserVar=TASK_NUMBER=%s\007' "$TASK_VALUE" > "$PANE_TTY"
elif [[ "$SHOULD_CLEAR" -eq 1 ]]; then
    # Clear TASK_NUMBER on non-task slash commands
    printf '\033]1337;SetUserVar=TASK_NUMBER=\007' > "$PANE_TTY"
fi
# Tier 3: no-op (TASK_NUMBER preserved from previous prompt)

exit_success
