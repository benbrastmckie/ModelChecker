#!/bin/bash
# TTS notification hook for Claude Code events
# Announces WezTerm tab number via Piper TTS for lifecycle transitions
# and interactive prompts requiring user input.
#
# Integration:
#   Notification hook (permission_prompt, elicitation_dialog): called with no args
#   Lifecycle transitions: called by update-task-status.sh postflight with --lifecycle STATUS
#
# Requirements: piper-tts, aplay or paplay (alsa-utils), wezterm
#
# Supported Modes:
#   Interactive (no args) - speaks "Tab N" for permission_prompt/elicitation_dialog
#   Lifecycle (--lifecycle STATUS) - speaks "Tab N STATUS" (e.g., "Tab 3 researched")
#
# Lifecycle status vocabulary (no artifact-type vocabulary):
#   researching, researched, planning, planned, implementing, completed, blocked
#
# Configuration:
#   PIPER_MODEL - Path to piper voice model (default: ~/.local/share/piper/en_US-lessac-medium.onnx)
#   TTS_ENABLED - Set to "0" to disable (default: 1)

set -uo pipefail

# Configuration with defaults
PIPER_MODEL="${PIPER_MODEL:-$HOME/.local/share/piper/en_US-lessac-medium.onnx}"
TTS_ENABLED="${TTS_ENABLED:-1}"

# Log file
LOG_FILE="specs/tmp/claude-tts-notify.log"

# --- Parse arguments ---
LIFECYCLE_STATUS=""
if [[ "${1:-}" == "--lifecycle" ]] && [[ -n "${2:-}" ]]; then
    LIFECYCLE_STATUS="$2"
fi

# Helper: log message
log() {
    echo "[$(date -Iseconds)] $1" >> "$LOG_FILE" 2>/dev/null || true
}

# Helper: return success JSON for hook
exit_success() {
    echo '{}'
    exit 0
}

# Helper: get WezTerm tab prefix ("Tab N" or fallback "Tab")
get_tab_prefix() {
    local tab_prefix="Tab"
    if [[ -n "${WEZTERM_PANE:-}" ]] && command -v wezterm &>/dev/null; then
        local all_panes current_tab_id unique_tab_ids tab_index position tab_num
        all_panes=$(wezterm cli list --format=json 2>/dev/null)
        current_tab_id=$(echo "$all_panes" | jq -r ".[] | select(.pane_id == $WEZTERM_PANE) | .tab_id" 2>/dev/null || echo "")
        if [[ -n "$current_tab_id" ]] && ! [[ "$current_tab_id" == "null" ]]; then
            unique_tab_ids=$(echo "$all_panes" | jq -r '[.[].tab_id] | unique | .[]')
            tab_index=0
            position=0
            while IFS= read -r tab_id; do
                if [[ "$tab_id" == "$current_tab_id" ]]; then
                    position=$tab_index
                    break
                fi
                ((tab_index++))
            done <<< "$unique_tab_ids"
            tab_num=$((position + 1))
            tab_prefix="Tab $tab_num"
        fi
    fi
    echo "$tab_prefix"
}

# Helper: speak a message via piper
speak() {
    local message="$1"
    if command -v paplay &>/dev/null; then
        local temp_wav="specs/tmp/claude-tts-$$.wav"
        mkdir -p specs/tmp
        (timeout 10s bash -c "echo '${message}' | piper --model '${PIPER_MODEL}' --output_file '${temp_wav}' 2>/dev/null && paplay '${temp_wav}' 2>/dev/null; rm -f '${temp_wav}'" &) || true
    elif command -v aplay &>/dev/null; then
        (timeout 10s bash -c "echo '${message}' | piper --model '${PIPER_MODEL}' --output_file - 2>/dev/null | aplay -q 2>/dev/null" &) || true
    else
        log "No audio player found (aplay or paplay) - skipping TTS"
        return 1
    fi
    return 0
}

# Check if TTS is disabled
if [[ "$TTS_ENABLED" != "1" ]]; then
    exit_success
fi

# Check if piper is available
if ! command -v piper &>/dev/null; then
    log "piper command not found - skipping TTS notification"
    exit_success
fi

# Check if model exists
if [[ ! -f "$PIPER_MODEL" ]]; then
    log "Piper model not found at $PIPER_MODEL - skipping TTS notification"
    exit_success
fi

# ============================================================
# LIFECYCLE MODE: --lifecycle STATUS
# Speak "Tab N STATUS" for researched/planned/completed events
# ============================================================
if [[ -n "$LIFECYCLE_STATUS" ]]; then
    TAB_PREFIX=$(get_tab_prefix)
    MESSAGE="$TAB_PREFIX $LIFECYCLE_STATUS"
    speak "$MESSAGE"
    log "Lifecycle notification sent: $MESSAGE (status=$LIFECYCLE_STATUS)"
    exit_success
fi

# ============================================================
# INTERACTIVE MODE: no args (Notification hook)
# Speak "Tab N" for permission_prompt and elicitation_dialog
# ============================================================
TAB_PREFIX=$(get_tab_prefix)
MESSAGE="$TAB_PREFIX"
speak "$MESSAGE"
log "Interactive notification sent: $MESSAGE"
exit_success
