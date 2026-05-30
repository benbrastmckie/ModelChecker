# dispatch_agent() Function Specification

**Status**: Current architecture — designed by Task 592, implemented by Task 596.

**File location**: `.claude/scripts/dispatch-agent.sh`
**Sourced by**: `.claude/skills/skill-orchestrate/SKILL.md`

**See Also**: `architecture-spec.md` (Component 4), `orchestrate-state-machine.md`,
`handoff-schema.md`

---

## Overview

`dispatch_agent()` is the single function that encapsulates the fork-vs-named-subagent decision.
It lives exclusively in `dispatch-agent.sh`, sourced by `skill-orchestrate`. Regular commands
do NOT use this function — they invoke skills directly via the Skill tool.

The function's existence future-proofs the system: when Anthropic provides a "named fork" API,
only `dispatch-agent.sh` changes. All call sites remain unchanged.

---

## Full Function Specification

```bash
#!/usr/bin/env bash
# dispatch-agent.sh — encapsulates fork-vs-named-subagent decision
# Source this file to make dispatch_agent() available.

dispatch_agent() {
  # Usage:
  #   dispatch_agent "$agent_type" "$prompt" "$context_json" "$is_blocker_escalation"
  #
  # Parameters:
  #   $1 = agent_type             - Named agent string (e.g. "general-research-agent")
  #                                 Pass "" (empty string) for fork path
  #   $2 = prompt                 - Full prompt string to pass to Agent tool
  #   $3 = context_json           - Delegation context JSON string
  #   $4 = is_blocker_escalation  - "true" | "false"
  #
  # Returns:
  #   exit 0 on agent success
  #   exit 1 on agent failure
  #   Writes: specs/{NNN}_{SLUG}/.orchestrator-handoff.json (via the agent)
  #
  # Side effects:
  #   Updates .orchestrator-loop-guard cycle_count
  #   Sets LAST_DISPATCH_STATUS from the handoff's status field

  local agent_type="$1"
  local prompt="$2"
  local context_json="$3"
  local is_blocker_escalation="$4"

  if [ "$is_blocker_escalation" = "true" ]; then
    # FORK PATH: omit subagent_type
    # → FORK_SUBAGENT=1 env var applies (if set by caller)
    # → Parent cache prefix inherited (~90% token reduction)
    # → No specialized agent context loaded (blocker research is general)
    invoke_agent_fork "$prompt" "$context_json"
  else
    # NAMED SUBAGENT PATH: use agent_type as subagent_type
    # → Fresh context window for the agent
    # → Full structured context injection
    # → Specialized agent prompt and patterns loaded
    invoke_named_agent "$agent_type" "$prompt" "$context_json"
  fi
}

invoke_agent_fork() {
  local prompt="$1"
  local context_json="$2"
  # Calls Agent tool WITHOUT subagent_type field
  # Implementation: Claude Code Agent tool call
  # This is a conceptual representation; actual invocation is via Agent tool in SKILL.md
  echo "[dispatch] fork dispatch (blocker escalation)"
}

invoke_named_agent() {
  local agent_type="$1"
  local prompt="$2"
  local context_json="$3"
  # Calls Agent tool WITH subagent_type="$agent_type"
  echo "[dispatch] named subagent: $agent_type"
}
```

---

## Decision Logic: Semantic Flag vs. TTL Heuristic

### Why `is_blocker_escalation` (not cache TTL)

The task 591 seed research suggested a `context_is_warm()` function based on 5-minute cache TTL:
```bash
context_is_warm() {
  local last_dispatch_time="$1"
  local elapsed=$(( $(date +%s) - last_dispatch_time ))
  [ $elapsed -lt 300 ]  # 5-minute TTL
}
```

This was **rejected** for `dispatch_agent()` for the following reason:

The orchestrator always knows *why* it is dispatching:
- **Blocker escalation**: Always happens within a single `/orchestrate` invocation (same session,
  same conversational turn). Cache is guaranteed warm. No named agent context needed (the blocker
  research is general-purpose).
- **State transition** (not_started → research, researched → plan, planned → implement): Always
  crosses conversation boundaries (the orchestrator dispatches, the agent completes, the next
  cycle starts). Cache is guaranteed cold (or nearly expired). Named agent context is needed.

The `is_blocker_escalation` flag captures this semantic distinction directly. Cache TTL measurement
is fragile and may give wrong answers if the system is slow or the conversation takes longer than
expected.

### Decision Matrix

| Dispatch Context | `is_blocker_escalation` | Path | Why |
|-----------------|------------------------|------|-----|
| State machine: not_started → research | `false` | Named subagent | Cold; needs agent context |
| State machine: researched → plan | `false` | Named subagent | Cold; needs agent context |
| State machine: planned → implement | `false` | Named subagent | Cold; needs agent context |
| Blocker escalation: research fork | `true` | Fork | Warm; general research, no specialized context |
| Blocker escalation: revise | `false` | Named subagent | Reviser needs specialized prompt |
| Blocker escalation: re-implement | `false` | Named subagent | Named implementer context needed |

**Note**: Only the initial blocker research step uses a fork. Reviser and re-implement dispatch
use named subagents even during blocker escalation (they need specialized agent prompts).

---

## Integration with skill-orchestrate

In `skill-orchestrate/SKILL.md`, after sourcing `dispatch-agent.sh`:

```bash
source .claude/scripts/dispatch-agent.sh

# State machine loop (MAX_CYCLES=5)
while [ "$cycle_count" -lt "$MAX_CYCLES" ]; do
  task_status=$(jq -r ".active_projects[] | select(.project_number == $task_n) | .status" specs/state.json)

  case "$task_status" in
    not_started)
      dispatch_agent "general-research-agent" "$research_prompt" "$context_json" "false"
      ;;
    researched)
      dispatch_agent "planner-agent" "$plan_prompt" "$context_json" "false"
      ;;
    planned|implementing|partial)
      # Check handoff for blockers/continuation
      handoff_file="specs/${padded_num}_${project_name}/.orchestrator-handoff.json"
      if has_blockers "$handoff_file"; then
        # Step 2: fork research (is_blocker_escalation=true)
        dispatch_agent "" "$blocker_research_prompt" "$context_json" "true"
        # Step 4: dispatch revise (named)
        dispatch_agent "reviser-agent" "$revise_prompt" "$context_with_findings" "false"
        # Step 5: re-implement (named)
        dispatch_agent "general-implementation-agent" "$implement_prompt" "$context_json" "false"
      elif has_continuation "$handoff_file"; then
        continuation=$(get_continuation "$handoff_file")
        dispatch_agent "general-implementation-agent" "$implement_prompt" "$context_with_continuation" "false"
      else
        dispatch_agent "general-implementation-agent" "$implement_prompt" "$context_json" "false"
      fi
      ;;
    completed|abandoned|expanded)
      echo "Task $task_n: $task_status. Exiting."
      break
      ;;
  esac

  cycle_count=$((cycle_count + 1))
  update_loop_guard "$cycle_count" "$task_status"
done
```

---

## Future-Proofing: Named Fork API

When Anthropic provides a "named fork" API that combines cache prefix sharing with named agent
specialization, only `dispatch-agent.sh` changes:

```bash
dispatch_agent() {
  local agent_type="$1"
  local prompt="$2"
  local context_json="$3"
  local is_blocker_escalation="$4"

  # Future: named fork combines both benefits
  if [ "$named_fork_available" = "true" ] && [ "$is_blocker_escalation" = "true" ]; then
    # Gets cache sharing AND specialized prompt
    invoke_named_fork "$agent_type" "$prompt" "$context_json"
  elif [ "$is_blocker_escalation" = "true" ]; then
    # Current behavior: anonymous fork (cache sharing, no agent specialization)
    invoke_agent_fork "$prompt" "$context_json"
  else
    # Current behavior: named subagent (no cache sharing, full agent specialization)
    invoke_named_agent "$agent_type" "$prompt" "$context_json"
  fi
}
```

All call sites remain unchanged. The dispatch_agent() interface is stable.

---

## Error Handling

If `invoke_agent_fork` fails (e.g., FORK_SUBAGENT env var not set), fall back to named subagent:

```bash
invoke_agent_fork() {
  local prompt="$1"
  local context_json="$2"

  if [ "$FORK_SUBAGENT" = "1" ]; then
    # Use fork (cache-warm)
    # ... Agent tool call without subagent_type ...
  else
    # Graceful degradation: fall back to named research agent
    echo "[dispatch] FORK_SUBAGENT not set; falling back to named research agent"
    invoke_named_agent "general-research-agent" "$prompt" "$context_json"
  fi
}
```

This ensures blocker escalation still works even when the fork environment variable is absent.
The token savings are foregone, but the functional outcome is the same.
