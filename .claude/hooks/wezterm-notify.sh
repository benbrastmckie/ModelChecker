#!/bin/bash
# WezTerm tab notification hook for Claude Code completion
# Sets CLAUDE_STATUS user variable via OSC 1337 when Claude stops
#
# Integration: Called from Stop hook in .claude/settings.json
#              Also called by update-task-status.sh with lifecycle state parameter
# Requirements: wezterm with user variable support, jq for JSON parsing
#
# Usage:
#   bash wezterm-notify.sh              # Sets CLAUDE_STATUS=needs_input (Stop hook)
#   bash wezterm-notify.sh researched   # Sets CLAUDE_STATUS=researched (lifecycle)
#   bash wezterm-notify.sh completed    # Sets CLAUDE_STATUS=completed (lifecycle)
#
# Configuration:
#   WEZTERM_NOTIFY_ENABLED - Set to "0" to disable (default: 1)
#
# The CLAUDE_STATUS variable is read by wezterm.lua format-tab-title handler
# to show colored background on inactive tabs based on lifecycle state.
# Only lifecycle states are used (no artifact-type vocabulary):
#   needs_input  -> gray (Stop hook default)
#   researching  -> dim green (in progress)
#   researched   -> bright green (done)
#   planning     -> dim blue (in progress)
#   planned      -> bright blue (done)
#   implementing -> dim gold (in progress)
#   completed    -> bright gold (done)
#   blocked      -> red
#   unknown      -> default styling (safe degradation)
#
# Note: Claude Code hooks run with redirected stdio (stdout is a socket),
# so we must write the escape sequence directly to the pane's TTY.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Load shared WezTerm utilities (TTY discovery and OSC writes)
# shellcheck source=wezterm-utils.sh
source "$SCRIPT_DIR/wezterm-utils.sh"

# Configuration with defaults
WEZTERM_NOTIFY_ENABLED="${WEZTERM_NOTIFY_ENABLED:-1}"

# Parse optional lifecycle state parameter
# When called with an argument, use it as the CLAUDE_STATUS value
# When called without arguments (Stop hook), default to "needs_input"
STATUS="${1:-needs_input}"

# Helper: return success JSON for Stop hook
exit_success() {
    echo '{}'
    exit 0
}

# Check if notification is disabled
if [[ "$WEZTERM_NOTIFY_ENABLED" != "1" ]]; then
    exit_success
fi

# Only run in WezTerm
if [[ -z "${WEZTERM_PANE:-}" ]]; then
    exit_success
fi

# Get the TTY for the current pane (via shared utility)
PANE_TTY=$(get_pane_tty) || exit_success

# Set CLAUDE_STATUS user variable via OSC 1337 (via shared utility)
set_user_var "CLAUDE_STATUS" "$STATUS" "$PANE_TTY"

exit_success
