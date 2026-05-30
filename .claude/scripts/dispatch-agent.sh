#!/usr/bin/env bash
# dispatch-agent.sh — Dispatch function for skill-orchestrate state machine
#
# SOURCING SEMANTICS:
#   This file must be sourced within the SAME Bash tool invocation as function calls.
#   Exported variables do NOT persist across separate Bash invocations in Claude Code.
#   Pattern: source this file, then call functions, all within one bash block.
#
#   Example usage in a SKILL.md bash block:
#     source .claude/scripts/dispatch-agent.sh
#     dispatch_agent "general-research-agent" "$prompt" "$context_json" "false"
#
# FUNCTION SIGNATURES:
#   dispatch_agent       -> prints dispatch instructions to stdout (JSON)
#   invoke_named_agent   -> generates named subagent dispatch JSON
#   invoke_agent_fork    -> generates fork dispatch JSON (blocker research only)
#
# DISPATCH SEMANTICS:
#   This script does NOT perform actual Agent tool invocations — those require
#   direct Claude tool calls. Instead, these functions produce JSON dispatch
#   instructions that the SKILL.md reads to construct Agent tool invocations.
#
#   Two dispatch paths:
#   1. Named subagent (is_blocker_escalation=false):
#      - Fresh context window per invocation
#      - agent_type maps to subagent_type in Agent tool call
#      - Used for: research, plan, implement, revise
#
#   2. Fork dispatch (is_blocker_escalation=true):
#      - Cache-warm: inherits parent cache prefix for fast reading
#      - Omits subagent_type (fork inherits parent agent type)
#      - Used for: blocker research ONLY (highest-value use of fork)
#      - Graceful degradation: falls back to named general-research-agent
#        if FORK_SUBAGENT env var is not set
#
# ARCHITECTURE REFERENCE:
#   .claude/docs/architecture/dispatch-agent-spec.md

# ─────────────────────────────────────────────────────────────────────────────
# invoke_named_agent — Generate named subagent dispatch JSON
# Usage: invoke_named_agent "$agent_type" "$prompt" "$context_json"
# Output: JSON dispatch instructions printed to stdout
invoke_named_agent() {
  local agent_type="$1"
  local prompt="$2"
  local context_json="$3"

  jq -n \
    --arg agent_type "$agent_type" \
    --arg prompt "$prompt" \
    --argjson context "$context_json" \
    '{
      "dispatch_mode": "named_subagent",
      "subagent_type": $agent_type,
      "prompt": $prompt,
      "context": $context,
      "cache_warm": false
    }'
}

# ─────────────────────────────────────────────────────────────────────────────
# invoke_agent_fork — Generate fork dispatch JSON (blocker research only)
# Usage: invoke_agent_fork "$prompt" "$context_json"
# Output: JSON dispatch instructions printed to stdout
# Graceful degradation: if FORK_SUBAGENT not set, falls back to named research agent
invoke_agent_fork() {
  local prompt="$1"
  local context_json="$2"

  if [ "${FORK_SUBAGENT:-}" = "1" ]; then
    jq -n \
      --arg prompt "$prompt" \
      --argjson context "$context_json" \
      '{
        "dispatch_mode": "fork",
        "subagent_type": null,
        "prompt": $prompt,
        "context": $context,
        "cache_warm": true,
        "note": "Fork inherits parent cache prefix for fast blocker research"
      }'
  else
    # Graceful degradation: no fork available, use named research agent with warning
    echo "[dispatch-agent] WARNING: FORK_SUBAGENT not set, falling back to named research agent" >&2
    jq -n \
      --arg prompt "$prompt" \
      --argjson context "$context_json" \
      '{
        "dispatch_mode": "named_subagent",
        "subagent_type": "general-research-agent",
        "prompt": $prompt,
        "context": $context,
        "cache_warm": false,
        "note": "Degraded from fork to named subagent (FORK_SUBAGENT not set)"
      }'
  fi
}

# ─────────────────────────────────────────────────────────────────────────────
# dispatch_agent — Main dispatch function: routes to fork or named subagent
# Usage: dispatch_agent "$agent_type" "$prompt" "$context_json" "$is_blocker_escalation"
#
# Parameters:
#   $1 = agent_type            : Agent name (e.g., "general-research-agent", "planner-agent")
#                                Ignored when is_blocker_escalation=true (fork path)
#   $2 = prompt                : Task instructions for the dispatched agent
#   $3 = context_json          : JSON context object passed to the agent
#   $4 = is_blocker_escalation : "true" | "false" — selects fork vs named path
#
# Output: JSON dispatch instructions printed to stdout (for SKILL.md to consume)
dispatch_agent() {
  local agent_type="$1"
  local prompt="$2"
  local context_json="$3"
  local is_blocker_escalation="${4:-false}"

  # Validate context_json is valid JSON
  if ! echo "$context_json" | jq empty 2>/dev/null; then
    echo "[dispatch-agent] ERROR: context_json is not valid JSON" >&2
    return 1
  fi

  if [ "$is_blocker_escalation" = "true" ]; then
    invoke_agent_fork "$prompt" "$context_json"
  else
    invoke_named_agent "$agent_type" "$prompt" "$context_json"
  fi
}
