---
name: skill-orchestrate
description: Autonomous state machine that drives a task through its full lifecycle (research -> plan -> implement -> complete) without user confirmation between phases. Invoke for /orchestrate command.
allowed-tools: Agent, Bash, Read, Edit
---

# Orchestrate Skill

Fire-and-forget autonomous loop implementing the 10-state task lifecycle state machine.
Drives research, planning, implementation, and blocker escalation without user interaction.

## Context References

Architecture documentation (load as needed):
- `.claude/docs/architecture/orchestrate-state-machine.md` - Complete state table and transition diagram
- `.claude/docs/architecture/handoff-schema.md` - Orchestrator handoff JSON schema
- `.claude/docs/architecture/dispatch-agent-spec.md` - Fork vs. named subagent dispatch spec

Infrastructure (source as needed):
- `.claude/scripts/skill-base.sh` - Shared skill lifecycle functions
- `.claude/scripts/dispatch-agent.sh` - Fork vs. named subagent dispatch functions

---

## Execution Flow

### Stage 1: Input Validation

```bash
source .claude/scripts/skill-base.sh
task_number=$(echo "$delegation_context" | jq -r '.task_context.task_number')
session_id=$(echo "$delegation_context" | jq -r '.session_id')
focus_prompt=$(echo "$delegation_context" | jq -r '.focus_prompt // ""')

# Read task state without blocking on terminal states (orchestrate handles them gracefully)
PADDED_NUM=$(printf "%03d" "$task_number")
TASK_DATA=$(jq -r --argjson num "$task_number" \
  '.active_projects[] | select(.project_number == $num)' \
  specs/state.json)
if [ -z "$TASK_DATA" ]; then
  echo "ERROR: Task $task_number not found in state.json" >&2
  exit 1
fi
PROJECT_NAME=$(echo "$TASK_DATA" | jq -r '.project_name')
TASK_TYPE=$(echo "$TASK_DATA" | jq -r '.task_type // "general"')
DESCRIPTION=$(echo "$TASK_DATA" | jq -r '.description // ""')
TASK_DIR="specs/${PADDED_NUM}_${PROJECT_NAME}"
```

### Stage 1b: Resolve Task-Type Routing

Map task_type to the correct research and implementation agents using extension manifests.

```bash
# Resolve agents by task_type — consult extension manifests for non-core types
case "$TASK_TYPE" in
  lean4|lean)
    RESEARCH_AGENT="lean-research-agent"
    IMPLEMENT_AGENT="lean-implementation-agent"
    ;;
  neovim)
    RESEARCH_AGENT="neovim-research-agent"
    IMPLEMENT_AGENT="neovim-implementation-agent"
    ;;
  nix)
    RESEARCH_AGENT="nix-research-agent"
    IMPLEMENT_AGENT="nix-implementation-agent"
    ;;
  *)
    RESEARCH_AGENT="general-research-agent"
    IMPLEMENT_AGENT="general-implementation-agent"
    ;;
esac
echo "[orchestrate] Task type: $TASK_TYPE → research=$RESEARCH_AGENT, implement=$IMPLEMENT_AGENT"
```

**Extension resolution**: If a task_type is not in the case table above, check for an extension manifest:
```bash
manifest=".claude/extensions/${TASK_TYPE}/manifest.json"
if [ -f "$manifest" ]; then
  ext_research=$(jq -r ".routing.research[\"$TASK_TYPE\"] // empty" "$manifest")
  ext_implement=$(jq -r ".routing.implement[\"$TASK_TYPE\"] // empty" "$manifest")
  # Map skill names to agent names (skill-X-Y -> X-Y-agent)
  if [ -n "$ext_research" ]; then
    RESEARCH_AGENT=$(echo "$ext_research" | sed 's/^skill-//' | sed 's/$/-agent/')
  fi
  if [ -n "$ext_implement" ]; then
    IMPLEMENT_AGENT=$(echo "$ext_implement" | sed 's/^skill-//' | sed 's/$/-agent/')
  fi
fi
```

### Stage 2: Preflight — Loop Guard

Create or read the loop guard file. This tracks cycle count across conversational turns.

```bash
MAX_CYCLES=5
loop_guard_file="${TASK_DIR}/.orchestrator-loop-guard"
handoff_file="${TASK_DIR}/.orchestrator-handoff.json"

mkdir -p "$TASK_DIR"

if [ -f "$loop_guard_file" ] && jq empty "$loop_guard_file" 2>/dev/null; then
  # Resume: read existing guard
  cycle_count=$(jq -r '.cycle_count // 0' "$loop_guard_file")
  echo "[orchestrate] Resuming — cycle $cycle_count of $MAX_CYCLES"
else
  # Fresh start: create guard
  cycle_count=0
  jq -n \
    --arg session_id "$session_id" \
    --argjson max_cycles "$MAX_CYCLES" \
    --arg started "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    '{
      "session_id": $session_id,
      "cycle_count": 0,
      "max_cycles": $max_cycles,
      "current_state": "reading",
      "started": $started,
      "last_updated": $started
    }' > "$loop_guard_file"
  echo "[orchestrate] Starting fresh — MAX_CYCLES=$MAX_CYCLES"
fi

# Blocker escalation counter (reset each /orchestrate invocation)
blocker_escalation_count=0
MAX_BLOCKER_ESCALATIONS=2

# Drift detection constants (reset each /orchestrate invocation)
drift_inspection_count=0
MAX_DRIFT_INSPECTIONS=1
DRIFT_COMPLETION_THRESHOLD=0.70
DRIFT_REVISION_THRESHOLD=0.30
```

### Stage 3: State Machine Loop

The loop runs until a terminal condition is reached or MAX_CYCLES is hit.

```
while [ "$cycle_count" -lt "$MAX_CYCLES" ]; do
```

At the top of each iteration:

**3a. Read current task status**

```bash
current_status=$(jq -r --argjson num "$task_number" \
  '.active_projects[] | select(.project_number == $num) | .status' \
  specs/state.json)
echo "[orchestrate] Cycle $((cycle_count + 1))/$MAX_CYCLES — status: $current_status"
```

**3b. Update loop guard with current state**

```bash
jq --arg state "$current_status" \
   --arg updated "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
   --argjson count "$cycle_count" \
  '.current_state = $state | .last_updated = $updated | .cycle_count = $count' \
  "$loop_guard_file" > "${loop_guard_file}.tmp" && mv "${loop_guard_file}.tmp" "$loop_guard_file"
```

**3c. Dispatch by state** (see State Handlers in Stage 4)

---

### Stage 4: State Handlers

#### State: `not_started` or `not started`

Dispatch research via named subagent (resolved by task type in Stage 1b).

```
dispatch_instructions = dispatch_agent "$RESEARCH_AGENT" \
  "Research task $task_number: $DESCRIPTION${focus_prompt:+. User focus: $focus_prompt}" \
  '{"task_number": N, "task_type": "T", "session_id": "S", "orchestrator_mode": false}' \
  "false"
```

Invoke the Agent tool per dispatch_instructions (subagent_type: $RESEARCH_AGENT).

After Agent tool returns: read handoff (Stage 5). Increment cycle_count.

#### State: `researching`

In-flight state (another session is actively researching). Exit with warning.

```
echo "[orchestrate] WARNING: Task $task_number is currently being researched in another session."
echo "Wait for the research to complete, then run /orchestrate $task_number again."
EXIT (partial)
```

#### State: `researched`

Dispatch planning via named subagent.

```
research_artifacts=$(jq -c '[.active_projects[] | select(.project_number == N) | .artifacts // [] | .[] | select(.type == "report")] | .[0].path // ""' specs/state.json)

dispatch_instructions = dispatch_agent "planner-agent" \
  "Create implementation plan for task $task_number${focus_prompt:+. User focus: $focus_prompt}" \
  '{"task_number": N, "task_type": "T", "session_id": "S", "research_artifacts": [...], "orchestrator_mode": false}' \
  "false"
```

Invoke the Agent tool per dispatch_instructions (subagent_type: planner-agent).

After Agent tool returns: read handoff. Increment cycle_count.

#### State: `planning`

In-flight state. Exit with warning (same pattern as `researching`).

#### State: `planned` or `implementing`

Dispatch implement via named subagent with `orchestrator_mode: true` (resolved by task type in Stage 1b).

```bash
plan_path=$(ls -1 "${TASK_DIR}/plans/"*.md 2>/dev/null | sort -V | tail -1)
```

```
dispatch_instructions = dispatch_agent "$IMPLEMENT_AGENT" \
  "Implement task $task_number following the plan${focus_prompt:+. User focus: $focus_prompt}" \
  '{"task_number": N, "task_type": "T", "session_id": "S", "orchestrator_mode": true,
    "plan_path": "$plan_path"}' \
  "false"
```

Invoke the Agent tool per dispatch_instructions (subagent_type: $IMPLEMENT_AGENT).

After Agent tool returns: read handoff. Increment cycle_count.

#### State: `partial`

Read `.orchestrator-handoff.json` to determine sub-state:

```bash
handoff=$(cat "$handoff_file" 2>/dev/null || echo '{}')
blockers=$(echo "$handoff" | jq -c '.blockers // []')
continuation=$(echo "$handoff" | jq -c '.continuation_context // null')
blocker_count=$(echo "$blockers" | jq 'length')
```

**Sub-state: continuation available** (continuation != null AND has handoff_path):

Dispatch implement with continuation context (resolved by task type in Stage 1b).

```
dispatch_instructions = dispatch_agent "$IMPLEMENT_AGENT" \
  "Resume implementation for task $task_number from continuation handoff${focus_prompt:+. User focus: $focus_prompt}" \
  '{"task_number": N, ..., "orchestrator_mode": true,
    "plan_path": "$plan_path",
    "continuation_context": {continuation_context_object}}' \
  "false"
```

**Sub-state: blockers present** (blocker_count > 0):

Invoke blocker escalation (Stage 6). Increment cycle_count after escalation.

**Sub-state: no handoff, no blockers** (cycle limit or stuck):

```
echo "[orchestrate] Task $task_number in partial state with no continuation and no blockers."
echo "Cycle $cycle_count/$MAX_CYCLES consumed. Run /orchestrate $task_number to retry or /implement $task_number for manual resume."
EXIT (partial, cycle_count)
```

#### State: `blocked`

Read blockers from state.json (not handoff — task was blocked outside orchestrator context):

```bash
blocker_desc=$(jq -r --argjson num "$task_number" \
  '.active_projects[] | select(.project_number == $num) | .blockers // "Unspecified blocker"' \
  specs/state.json)
```

Invoke blocker escalation (Stage 6) with blocker_desc.

#### State: `completed`

```
echo "[orchestrate] Task $task_number completed successfully."
# Clean up loop guard
rm -f "$loop_guard_file"
EXIT (success)
```

#### States: `abandoned`, `expanded`

```
echo "[orchestrate] Task $task_number is in terminal state [$current_status]. No action taken."
EXIT (no-op)
```

#### Unknown state

```
echo "[orchestrate] WARNING: Unrecognized state '$current_status' for task $task_number."
EXIT (partial)
```

---

### Stage 5: Handoff Reading (after each dispatch)

After every Agent tool invocation, read the orchestrator handoff to learn the outcome.
Never read the full research report, plan, or implementation summary — only the handoff.

```bash
if [ ! -f "$handoff_file" ]; then
  echo "[orchestrate] ERROR: Skill did not write orchestrator handoff."
  echo "This may mean orchestrator_mode was not propagated correctly."
  # Increment cycle and continue — state.json may still have been updated
else
  handoff=$(cat "$handoff_file")
  dispatch_status=$(echo "$handoff" | jq -r '.status')
  dispatch_summary=$(echo "$handoff" | jq -r '.summary // ""')
  blockers=$(echo "$handoff" | jq -c '.blockers // []')
  continuation=$(echo "$handoff" | jq -c '.continuation_context // null')
  next_hint=$(echo "$handoff" | jq -r '.next_action_hint // "none"')
  phases_completed=$(echo "$handoff" | jq -r '.phases_completed // 0')
  phases_total=$(echo "$handoff" | jq -r '.phases_total // 0')
  echo "[orchestrate] Dispatch result: $dispatch_status — $dispatch_summary"
  [ "$phases_total" -gt 0 ] && echo "[orchestrate] Phase progress: $phases_completed/$phases_total"

  # Drift detection: arithmetic gate (cheap check before expensive inspection fork)
  if [ "$phases_total" -gt 0 ] && [ "$dispatch_status" = "partial" ]; then
    # Use awk for floating-point comparison (bash only does integer math)
    completion_ratio=$(awk "BEGIN { printf \"%.4f\", $phases_completed / $phases_total }")
    is_below_threshold=$(awk "BEGIN { print ($completion_ratio < $DRIFT_COMPLETION_THRESHOLD) ? \"yes\" : \"no\" }")
    if [ "$is_below_threshold" = "yes" ]; then
      echo "[orchestrate] Low phase completion ($phases_completed/$phases_total). Inspecting plan for drift..."
      invoke_drift_inspection "$task_number" "$plan_path" "$session_id"
    fi
  fi
fi

# Increment cycle_count
cycle_count=$((cycle_count + 1))
```

---

### Stage 5a: Drift Inspection Function

Called from Stage 5 when phase completion is below DRIFT_COMPLETION_THRESHOLD and dispatch_status is "partial".
Capped at MAX_DRIFT_INSPECTIONS=1 per /orchestrate invocation.

```bash
invoke_drift_inspection() {
  local task_number="$1"
  local plan_path="$2"
  local session_id="$3"

  if [ "$drift_inspection_count" -ge "$MAX_DRIFT_INSPECTIONS" ]; then
    echo "[orchestrate] WARNING: Drift inspection cap ($MAX_DRIFT_INSPECTIONS) reached. Skipping inspection."
    return 0
  fi

  drift_inspection_count=$((drift_inspection_count + 1))
  echo "[orchestrate] Drift inspection attempt $drift_inspection_count/$MAX_DRIFT_INSPECTIONS"

  source .claude/scripts/dispatch-agent.sh

  drift_inspect_context=$(jq -n \
    --argjson num "$task_number" \
    --arg session_id "$session_id" \
    --arg plan_path "$plan_path" \
    '{"task_number": $num, "session_id": $session_id, "plan_path": $plan_path, "orchestrator_mode": false}')

  drift_inspect_prompt="Read the plan file at '$plan_path'. Count: (1) total checklist items matching '- \\[ \\]' or '- \\[x\\]', (2) completed items matching '- \\[x\\]', (3) deviation annotations matching '*(deviation:'. Calculate drift_pct as: deviation_count / max(total_items, 1). Write compact JSON to '${TASK_DIR}/.drift-inspection.json' with fields: drift_pct (float), deviation_count (int), total_items (int), completed_items (int), summary (string, one sentence). Return a brief summary of findings."

  dispatch_agent "" "$drift_inspect_prompt" "$drift_inspect_context" "true"
  # SKILL.md reads this output and invokes the Agent tool as a fork (omitting subagent_type)
  # After Agent tool returns: read .drift-inspection.json

  # Read drift inspection result
  drift_inspection_file="${TASK_DIR}/.drift-inspection.json"
  if [ -f "$drift_inspection_file" ]; then
    drift_pct=$(jq -r '.drift_pct // 0' "$drift_inspection_file")
    drift_summary=$(jq -r '.summary // "No summary"' "$drift_inspection_file")
    echo "[orchestrate] Drift inspection result: drift_pct=$drift_pct — $drift_summary"
  else
    echo "[orchestrate] WARNING: Drift inspection did not write .drift-inspection.json. Defaulting drift_pct=0."
    drift_pct=0
    drift_summary="Inspection output missing"
  fi

  # Conditional reviser-agent invocation when drift exceeds threshold
  is_above_threshold=$(awk "BEGIN { print ($drift_pct > $DRIFT_REVISION_THRESHOLD) ? \"yes\" : \"no\" }")
  if [ "$is_above_threshold" = "yes" ]; then
    echo "[orchestrate] Drift detected ($drift_pct > $DRIFT_REVISION_THRESHOLD). Triggering plan revision..."
    revised_plan_path=$(ls -1 "${TASK_DIR}/plans/"*.md 2>/dev/null | sort -V | tail -1)
    revise_context=$(jq -n \
      --argjson num "$task_number" \
      --arg session_id "$session_id" \
      --arg plan_path "${revised_plan_path:-}" \
      --arg revision_reason "drift" \
      --arg drift_pct "$drift_pct" \
      '{"task_number": $num, "session_id": $session_id,
        "plan_path": $plan_path,
        "revision_reason": $revision_reason,
        "drift_pct": $drift_pct,
        "orchestrator_mode": false}')
    dispatch_agent "reviser-agent" \
      "Revise the implementation plan for task $task_number to address plan drift (drift_pct=$drift_pct). Summary: $drift_summary" \
      "$revise_context" "false"
    # SKILL.md invokes the Agent tool (subagent_type: reviser-agent)
    # After Agent tool returns: read handoff to confirm revision
  else
    echo "[orchestrate] Drift check passed ($drift_pct <= $DRIFT_REVISION_THRESHOLD). Continuing."
  fi
}
```

---

### Stage 6: Blocker Escalation (5-Step Sequence)

Called when: `partial` state with non-empty blockers, or `blocked` state.
Capped at MAX_BLOCKER_ESCALATIONS=2 per /orchestrate invocation.

```bash
blocker_escalation() {
  local blocker_desc="$1"
  local task_number="$2"
  local session_id="$3"

  if [ "$blocker_escalation_count" -ge "$MAX_BLOCKER_ESCALATIONS" ]; then
    echo "[orchestrate] ERROR: Blocker escalation cap ($MAX_BLOCKER_ESCALATIONS) reached."
    echo "Manual intervention required. Blocker: $blocker_desc"
    echo "Suggested actions:"
    echo "  1. Run /research $task_number to research the blocker manually"
    echo "  2. Run /revise $task_number to update the plan"
    echo "  3. Run /implement $task_number to re-attempt implementation"
    return 1
  fi

  blocker_escalation_count=$((blocker_escalation_count + 1))
  echo "[orchestrate] Blocker escalation attempt $blocker_escalation_count/$MAX_BLOCKER_ESCALATIONS"
  echo "  Blocker: $blocker_desc"

  # Step 1: DETECT (already done by caller; blocker_desc passed in)

  # Step 2: RESEARCH FORK (cache-warm, is_blocker_escalation=true)
  source .claude/scripts/dispatch-agent.sh
  blocker_research_prompt="Research this specific blocker for task $task_number: $blocker_desc. Find the root cause and a concrete solution path."
  fork_context=$(jq -n \
    --argjson num "$task_number" \
    --arg session_id "$session_id" \
    --arg blocker "$blocker_desc" \
    '{"task_number": $num, "session_id": $session_id, "blocker": $blocker, "orchestrator_mode": false}')
  dispatch_agent "" "$blocker_research_prompt" "$fork_context" "true"
  # SKILL.md reads this output and invokes the Agent tool as a fork (omitting subagent_type)
  # After Agent tool returns: read handoff for research findings

  # Step 3: READ FINDINGS (from handoff)
  findings_summary=$(jq -r '.summary // "No findings"' "$handoff_file" 2>/dev/null)
  findings_artifact=$(jq -r '.artifacts[0].path // ""' "$handoff_file" 2>/dev/null)
  echo "[orchestrate] Research findings: $findings_summary"

  # Step 4: REVISE PLAN (named reviser-agent)
  plan_path=$(ls -1 "${TASK_DIR}/plans/"*.md 2>/dev/null | sort -V | tail -1)
  revise_context=$(jq -n \
    --argjson num "$task_number" \
    --arg session_id "$session_id" \
    --arg findings "$findings_summary" \
    --arg plan_path "${plan_path:-}" \
    '{"task_number": $num, "session_id": $session_id,
      "research_findings": $findings,
      "plan_path": $plan_path,
      "orchestrator_mode": false}')
  dispatch_agent "reviser-agent" \
    "Revise the implementation plan for task $task_number to address this blocker: $blocker_desc. Research findings: $findings_summary" \
    "$revise_context" "false"
  # SKILL.md invokes the Agent tool (subagent_type: reviser-agent)
  # After Agent tool returns: read handoff to confirm revision

  # Step 5: RE-DISPATCH IMPLEMENT (orchestrator_mode=true)
  revised_plan_path=$(ls -1 "${TASK_DIR}/plans/"*.md 2>/dev/null | sort -V | tail -1)
  implement_context=$(jq -n \
    --argjson num "$task_number" \
    --arg session_id "$session_id" \
    --arg plan_path "${revised_plan_path:-}" \
    '{"task_number": $num, "session_id": $session_id,
      "orchestrator_mode": true,
      "plan_path": $plan_path}')
  dispatch_agent "$IMPLEMENT_AGENT" \
    "Implement task $task_number following the revised plan${focus_prompt:+. User focus: $focus_prompt}" \
    "$implement_context" "false"
  # SKILL.md invokes the Agent tool (subagent_type: $IMPLEMENT_AGENT)
  # After Agent tool returns: read handoff

  return 0
}
```

---

### Stage 7: Loop Guard Update (end of each cycle)

After each cycle (whether dispatch succeeded or failed):

```bash
jq --arg state "$current_status" \
   --arg updated "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
   --argjson count "$cycle_count" \
  '.current_state = $state | .last_updated = $updated | .cycle_count = $count' \
  "$loop_guard_file" > "${loop_guard_file}.tmp" && mv "${loop_guard_file}.tmp" "$loop_guard_file"
```

If MAX_CYCLES reached (cycle_count >= MAX_CYCLES):

```
echo "[orchestrate] MAX_CYCLES ($MAX_CYCLES) reached for task $task_number."
echo "Current state: $current_status. Run /orchestrate $task_number to continue."
EXIT (partial)
```

---

### Stage 8: Postflight

On clean exit (task completed or terminal state):

```bash
# Remove loop guard on success
rm -f "$loop_guard_file"
# Clean up drift inspection artifact if present
rm -f "${TASK_DIR}/.drift-inspection.json"
echo "[orchestrate] Task $task_number: orchestration complete."
echo "Final status: $current_status | Cycles used: $cycle_count/$MAX_CYCLES"
```

On partial exit (MAX_CYCLES, in-flight warning, escalation cap):

```bash
# Preserve loop guard for next /orchestrate invocation
echo "[orchestrate] Task $task_number: orchestration paused."
echo "Status: $current_status | Cycles: $cycle_count/$MAX_CYCLES | Run /orchestrate $task_number to continue."
```

Write metadata file:

```bash
mkdir -p "${TASK_DIR}/summaries"
jq -n \
  --arg status "implemented" \
  --argjson cycles "$cycle_count" \
  --arg final_state "$current_status" \
  '{
    "status": $status,
    "metadata": {
      "cycles_used": $cycles,
      "final_state": $final_state
    }
  }' > "${TASK_DIR}/.return-meta.json"
```

---

## MUST NOT (Context Flatness Constraint)

This skill MUST NOT:

1. **Read research reports** (`reports/*.md`) during the state machine loop
2. **Read plan files** (`plans/*.md`) during the state machine loop
3. **Read implementation summaries** (`summaries/*.md`) during the state machine loop
4. **Read continuation handoff files** (`handoffs/*.md`) — pass the path, not the content

The ONLY file read after each dispatch is `.orchestrator-handoff.json` (≤400 tokens).
This ensures context grows by only ~450 tokens per cycle regardless of artifact complexity.

## Skill-to-Agent Mapping

| Operation | Agent Type | Mode |
|-----------|-----------|------|
| Research dispatch | `$RESEARCH_AGENT` (resolved by task type) | Named subagent |
| Plan dispatch | `planner-agent` | Named subagent |
| Implement dispatch | `$IMPLEMENT_AGENT` (resolved by task type) | Named subagent, orchestrator_mode=true |
| Blocker research | (no type — fork inherits parent) | Fork (cache-warm) |
| Plan revision (blocker) | `reviser-agent` | Named subagent |
| Drift inspection | (no type — fork inherits parent) | Fork (cache-warm); reads plan file, writes .drift-inspection.json |
| Plan revision (drift) | `reviser-agent` | Named subagent; triggered when drift_pct > DRIFT_REVISION_THRESHOLD |

Default agents: `general-research-agent`, `general-implementation-agent`. Extension agents resolved in Stage 1b.
