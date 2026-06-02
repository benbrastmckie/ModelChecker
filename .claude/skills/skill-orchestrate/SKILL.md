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

### Stage 0: Multi-Task Mode Detection

Parse `multi_task_mode` from the delegation context. If true, branch to multi-task stages (MT-1 through MT-5) in the **Multi-Task Mode** section below. If false or absent, fall through to existing Stage 1 (single-task mode unchanged).

```bash
source .claude/scripts/skill-base.sh
multi_task_mode=$(echo "$delegation_context" | jq -r '.multi_task_mode // false')
session_id=$(echo "$delegation_context" | jq -r '.session_id')
focus_prompt=$(echo "$delegation_context" | jq -r '.focus_prompt // ""')

if [ "$multi_task_mode" = "true" ]; then
  echo "[orchestrate] Multi-task mode detected — branching to MT-1"
  # Continue to Stage MT-1 (see Multi-Task Mode section)
  # All single-task stages (1-8) are SKIPPED in multi-task mode
  goto_multi_task=true
else
  goto_multi_task=false
fi

# If goto_multi_task=true, skip Stages 1-8 and proceed to Stage MT-1
```

---

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

  # Postflight status update: trigger state.json + TODO.md Task Order regeneration
  case "$dispatch_status" in
    researched)
      skill_postflight_update "$task_number" "research" "$session_id" "$dispatch_status"
      ;;
    planned)
      skill_postflight_update "$task_number" "plan" "$session_id" "$dispatch_status"
      ;;
    implemented)
      skill_postflight_update "$task_number" "implement" "$session_id" "$dispatch_status"
      ;;
    *)
      echo "[orchestrate] Dispatch status '$dispatch_status' — no postflight update needed"
      ;;
  esac

  # Artifact linking: extract artifact path/type from handoff and link in TODO.md + state.json
  handoff_artifact_path=$(echo "$handoff" | jq -r '.artifacts[0].path // ""')
  handoff_artifact_type=$(echo "$handoff" | jq -r '.artifacts[0].type // ""')
  handoff_artifact_summary=$(echo "$handoff" | jq -r '.artifacts[0].summary // ""')
  if [ -n "$handoff_artifact_path" ] && [ "$handoff_artifact_path" != "null" ]; then
    case "$handoff_artifact_type" in
      report)
        field_name='**Research**'
        next_field='**Plan**'
        ;;
      plan)
        field_name='**Plan**'
        next_field='**Description**'
        ;;
      summary)
        field_name='**Summary**'
        next_field='**Description**'
        ;;
      *)
        field_name='**Summary**'
        next_field='**Description**'
        ;;
    esac
    skill_link_artifacts "$task_number" "$handoff_artifact_path" "$handoff_artifact_type" \
      "$handoff_artifact_summary" "$field_name" "$next_field"
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

## Multi-Task Mode

Entered when `multi_task_mode=true` in the delegation context (detected in Stage 0).
All single-task stages (1-8) are skipped. The skill receives a pre-computed wave schedule
from `orchestrate.md` and manages all tasks in a single orchestrator instance.

### Stage MT-1: Parse Multi-Task Context

Extract all task numbers, dependency graph, pre-computed waves, and session context from the delegation context.

```bash
# Extract multi-task fields from delegation context
task_numbers_json=$(echo "$delegation_context" | jq -c '.task_numbers // []')
dependency_graph_json=$(echo "$delegation_context" | jq -c '.dependency_graph // {}')
waves_json=$(echo "$delegation_context" | jq -c '.waves // []')

# Convert JSON arrays to bash arrays for iteration
task_count=$(echo "$task_numbers_json" | jq 'length')
wave_count=$(echo "$waves_json" | jq 'length')

echo "[orchestrate-mt] Multi-task mode: $task_count tasks, $wave_count waves"
echo "[orchestrate-mt] Task numbers: $(echo "$task_numbers_json" | jq -r '.[]' | tr '\n' ' ')"
echo "[orchestrate-mt] Waves: $waves_json"
```

### Stage MT-2: Build Per-Task Routing Table and Initialize Multi-State

For each task, resolve agents by task_type (same case statement as Stage 1b) and initialize the multi-state tracking file.

```bash
# Build per-task metadata by reading state.json for each task
declare -A task_types
declare -A task_dirs
declare -A research_agents
declare -A implement_agents

for task_num in $(echo "$task_numbers_json" | jq -r '.[]'); do
  padded=$(printf "%03d" "$task_num")
  task_data=$(jq -r --argjson num "$task_num" \
    '.active_projects[] | select(.project_number == $num)' \
    specs/state.json)
  
  ttype=$(echo "$task_data" | jq -r '.task_type // "general"')
  pname=$(echo "$task_data" | jq -r '.project_name')
  task_dir="specs/${padded}_${pname}"
  
  # Resolve agents by task_type (mirrors Stage 1b case statement)
  case "$ttype" in
    lean4|lean)
      r_agent="lean-research-agent"
      i_agent="lean-implementation-agent"
      ;;
    neovim)
      r_agent="neovim-research-agent"
      i_agent="neovim-implementation-agent"
      ;;
    nix)
      r_agent="nix-research-agent"
      i_agent="nix-implementation-agent"
      ;;
    *)
      r_agent="general-research-agent"
      i_agent="general-implementation-agent"
      ;;
  esac
  
  # Check for extension manifest override
  manifest=".claude/extensions/${ttype}/manifest.json"
  if [ -f "$manifest" ]; then
    ext_research=$(jq -r ".routing.research[\"$ttype\"] // empty" "$manifest")
    ext_implement=$(jq -r ".routing.implement[\"$ttype\"] // empty" "$manifest")
    if [ -n "$ext_research" ]; then
      r_agent=$(echo "$ext_research" | sed 's/^skill-//' | sed 's/$/-agent/')
    fi
    if [ -n "$ext_implement" ]; then
      i_agent=$(echo "$ext_implement" | sed 's/^skill-//' | sed 's/$/-agent/')
    fi
  fi
  
  task_types[$task_num]="$ttype"
  task_dirs[$task_num]="$task_dir"
  research_agents[$task_num]="$r_agent"
  implement_agents[$task_num]="$i_agent"
  
  echo "[orchestrate-mt] Task $task_num: type=$ttype dir=$task_dir research=$r_agent implement=$i_agent"
done

# Read current status for each task
declare -A current_statuses
for task_num in $(echo "$task_numbers_json" | jq -r '.[]'); do
  status=$(jq -r --argjson num "$task_num" \
    '.active_projects[] | select(.project_number == $num) | .status' \
    specs/state.json)
  current_statuses[$task_num]="$status"
done

# Set MAX_CYCLES: 5 * task_count, capped at 25
MAX_CYCLES_MT=$(( task_count * 5 ))
if [ "$MAX_CYCLES_MT" -gt 25 ]; then
  MAX_CYCLES_MT=25
fi

# Build task_types_json, task_dirs_json, etc. for multi-state file
task_types_json=$(python3 -c "
import json, sys
nums = json.loads(sys.argv[1])
types = {str(n): '${task_types[$n]:-general}' for n in nums}
print(json.dumps(types))
" "$task_numbers_json")

# Initialize multi-state tracking file (atomic write)
mt_state_file="specs/.orchestrator-multi-state.json"
jq -n \
  --arg session_id "$session_id" \
  --argjson task_numbers "$task_numbers_json" \
  --argjson waves "$waves_json" \
  --argjson max_cycles "$MAX_CYCLES_MT" \
  '{
    "session_id": $session_id,
    "task_numbers": $task_numbers,
    "task_types": {},
    "task_dirs": {},
    "current_statuses": {},
    "research_agents": {},
    "implement_agents": {},
    "cycle_count": 0,
    "max_cycles": $max_cycles,
    "failed_tasks": [],
    "completed_tasks": [],
    "waves": $waves
  }' > "${mt_state_file}.tmp" && mv "${mt_state_file}.tmp" "$mt_state_file"

# Populate per-task routing maps into multi-state file
for task_num in $(echo "$task_numbers_json" | jq -r '.[]'); do
  ttype="${task_types[$task_num]:-general}"
  tdir="${task_dirs[$task_num]}"
  ragent="${research_agents[$task_num]:-general-research-agent}"
  iagent="${implement_agents[$task_num]:-general-implementation-agent}"
  cstatus="${current_statuses[$task_num]:-not_started}"
  
  jq --argjson num "$task_num" \
     --arg ttype "$ttype" \
     --arg tdir "$tdir" \
     --arg ragent "$ragent" \
     --arg iagent "$iagent" \
     --arg cstatus "$cstatus" \
    '.task_types[$num | tostring] = $ttype |
     .task_dirs[$num | tostring] = $tdir |
     .research_agents[$num | tostring] = $ragent |
     .implement_agents[$num | tostring] = $iagent |
     .current_statuses[$num | tostring] = $cstatus' \
    "$mt_state_file" > "${mt_state_file}.tmp" && mv "${mt_state_file}.tmp" "$mt_state_file"
done

echo "[orchestrate-mt] Multi-state initialized: $mt_state_file (MAX_CYCLES=$MAX_CYCLES_MT)"
```

### Stage MT-3: Wave Execution Loop

Outer loop iterates through waves sequentially. Within each wave, tasks are dispatched in parallel (up to 4 concurrent). After each batch, per-task postflight (status sync + artifact linking) fires for every dispatched task.

```
# Outer loop: iterate through waves sequentially
for wave_idx in $(seq 0 $((wave_count - 1))); do
  wave_tasks=$(echo "$waves_json" | jq -r ".[$wave_idx][]")
  
  # Filter: remove completed/failed/terminal tasks and tasks with failed predecessors
  active_tasks=()
  for task_num in $wave_tasks; do
    # Re-read status from state.json for freshness
    current_status=$(jq -r --argjson num "$task_num" \
      '.active_projects[] | select(.project_number == $num) | .status' \
      specs/state.json)
    current_statuses[$task_num]="$current_status"
    
    # Check if task's predecessors failed
    predecessor_failed=false
    predecessors_json=$(echo "$dependency_graph_json" | jq -c ".\"$task_num\" // []")
    for pred in $(echo "$predecessors_json" | jq -r '.[]'); do
      if jq -e --argjson p "$pred" '.failed_tasks | map(select(. == $p)) | length > 0' \
          "$mt_state_file" > /dev/null 2>&1; then
        predecessor_failed=true
        echo "[orchestrate-mt] Skipping task $task_num: predecessor $pred failed"
        break
      fi
    done
    
    if [ "$predecessor_failed" = "true" ]; then
      continue
    fi
    
    case "$current_status" in
      completed|abandoned|expanded)
        echo "[orchestrate-mt] Task $task_num already in terminal state [$current_status], skipping"
        jq --argjson num "$task_num" \
          '.completed_tasks = (.completed_tasks + [$num] | unique)' \
          "$mt_state_file" > "${mt_state_file}.tmp" && mv "${mt_state_file}.tmp" "$mt_state_file"
        continue
        ;;
    esac
    
    active_tasks+=("$task_num")
  done
  
  echo "[orchestrate-mt] Wave $wave_idx: ${#active_tasks[@]} active tasks: ${active_tasks[*]}"
  
  # Phase-aware grouping: dispatch each task to its appropriate agent
  # (parallel dispatch in batches of max 4 concurrent)
  # Stage MT-4 handles the dispatch context construction and parallel invocation
  # After all tasks in wave complete: read handoffs, call postflight, update multi-state
done
```

### Stage MT-4: Phase-Aware Dispatch and Per-Task Postflight

For each active task in the current wave, determine which agent phase to dispatch based on current status, construct the dispatch context, invoke the Agent tool (up to 4 in parallel), then read each task's handoff and call both postflight functions.

```
# Phase-aware dispatch for each active task in wave
# Group by needed phase for batching
research_tasks=()
plan_tasks=()
implement_tasks=()

for task_num in "${active_tasks[@]}"; do
  status="${current_statuses[$task_num]}"
  case "$status" in
    not_started|"not started")
      research_tasks+=("$task_num")
      ;;
    researched)
      plan_tasks+=("$task_num")
      ;;
    planned|implementing)
      implement_tasks+=("$task_num")
      ;;
    partial)
      # Check continuation context in handoff
      task_dir="${task_dirs[$task_num]}"
      handoff="${task_dir}/.orchestrator-handoff.json"
      if [ -f "$handoff" ]; then
        continuation=$(jq -c '.continuation_context // null' "$handoff")
        blocker_count=$(jq 'length' <<< "$(jq -c '.blockers // []' "$handoff")")
        if [ "$continuation" != "null" ]; then
          implement_tasks+=("$task_num")
        elif [ "$blocker_count" -gt 0 ]; then
          echo "[orchestrate-mt] WARNING: Task $task_num has blockers — marking as failed for this run"
          jq --argjson num "$task_num" \
            '.failed_tasks = (.failed_tasks + [$num] | unique) |
             .current_statuses[$num | tostring] = "blocked"' \
            "$mt_state_file" > "${mt_state_file}.tmp" && mv "${mt_state_file}.tmp" "$mt_state_file"
        fi
      else
        implement_tasks+=("$task_num")
      fi
      ;;
    blocked|researching|planning)
      echo "[orchestrate-mt] Task $task_num in in-flight or blocked state [$status] — skipping this cycle"
      ;;
    *)
      echo "[orchestrate-mt] WARNING: Unknown status '$status' for task $task_num — skipping"
      ;;
  esac
done

# Dispatch research tasks (concurrent, max 4)
for task_num in "${research_tasks[@]}"; do
  task_dir="${task_dirs[$task_num]}"
  task_type="${task_types[$task_num]:-general}"
  r_agent="${research_agents[$task_num]:-general-research-agent}"
  
  description=$(jq -r --argjson num "$task_num" \
    '.active_projects[] | select(.project_number == $num) | .description // ""' \
    specs/state.json)
  
  dispatch_context=$(jq -n \
    --argjson num "$task_num" \
    --arg task_type "$task_type" \
    --arg session_id "${session_id}_${task_num}" \
    '{"task_number": $num, "task_type": $task_type, "session_id": $session_id, "orchestrator_mode": false}')
  
  # Invoke Agent tool: subagent_type=$r_agent
  # Dispatch: dispatch_agent "$r_agent" "Research task $task_num: $description" "$dispatch_context" "false"
  echo "[orchestrate-mt] Dispatching research for task $task_num -> $r_agent"
done

# Dispatch plan tasks (concurrent, max 4)
for task_num in "${plan_tasks[@]}"; do
  task_dir="${task_dirs[$task_num]}"
  task_type="${task_types[$task_num]:-general}"
  
  research_artifacts=$(jq -c --argjson num "$task_num" \
    '[.active_projects[] | select(.project_number == $num) | .artifacts // [] | .[] | select(.type == "report")] | .[0].path // ""' \
    specs/state.json)
  
  dispatch_context=$(jq -n \
    --argjson num "$task_num" \
    --arg task_type "$task_type" \
    --arg session_id "${session_id}_${task_num}" \
    --argjson research_artifacts "[$research_artifacts]" \
    '{"task_number": $num, "task_type": $task_type, "session_id": $session_id,
      "research_artifacts": $research_artifacts, "orchestrator_mode": false}')
  
  # Invoke Agent tool: subagent_type=planner-agent
  echo "[orchestrate-mt] Dispatching planning for task $task_num -> planner-agent"
done

# Dispatch implement tasks (concurrent, max 4)
for task_num in "${implement_tasks[@]}"; do
  task_dir="${task_dirs[$task_num]}"
  task_type="${task_types[$task_num]:-general}"
  i_agent="${implement_agents[$task_num]:-general-implementation-agent}"
  plan_path=$(ls -1 "${task_dir}/plans/"*.md 2>/dev/null | sort -V | tail -1)
  
  # Check for continuation context
  handoff_file="${task_dir}/.orchestrator-handoff.json"
  if [ -f "$handoff_file" ]; then
    continuation=$(jq -c '.continuation_context // null' "$handoff_file")
  else
    continuation="null"
  fi
  
  dispatch_context=$(jq -n \
    --argjson num "$task_num" \
    --arg task_type "$task_type" \
    --arg session_id "${session_id}_${task_num}" \
    --arg plan_path "${plan_path:-}" \
    --argjson continuation "$continuation" \
    '{"task_number": $num, "task_type": $task_type, "session_id": $session_id,
      "orchestrator_mode": true, "plan_path": $plan_path, "continuation_context": $continuation}')
  
  # Invoke Agent tool: subagent_type=$i_agent
  echo "[orchestrate-mt] Dispatching implement for task $task_num -> $i_agent"
done

# After all parallel dispatches complete: read handoffs and call per-task postflight
for task_num in "${research_tasks[@]}" "${plan_tasks[@]}" "${implement_tasks[@]}"; do
  task_dir="${task_dirs[$task_num]}"
  handoff_file="${task_dir}/.orchestrator-handoff.json"
  
  if [ ! -f "$handoff_file" ]; then
    echo "[orchestrate-mt] WARNING: Task $task_num did not write handoff — marking failed"
    jq --argjson num "$task_num" \
      '.failed_tasks = (.failed_tasks + [$num] | unique)' \
      "$mt_state_file" > "${mt_state_file}.tmp" && mv "${mt_state_file}.tmp" "$mt_state_file"
    continue
  fi
  
  handoff=$(cat "$handoff_file")
  dispatch_status=$(echo "$handoff" | jq -r '.status')
  dispatch_summary=$(echo "$handoff" | jq -r '.summary // ""')
  echo "[orchestrate-mt] Task $task_num dispatch result: $dispatch_status — $dispatch_summary"
  
  # Determine operation from dispatch status
  case "$dispatch_status" in
    researched)
      operation="research"
      skill_postflight_update "$task_num" "research" "${session_id}_${task_num}" "$dispatch_status"
      ;;
    planned)
      operation="plan"
      skill_postflight_update "$task_num" "plan" "${session_id}_${task_num}" "$dispatch_status"
      ;;
    implemented)
      operation="implement"
      skill_postflight_update "$task_num" "implement" "${session_id}_${task_num}" "$dispatch_status"
      ;;
    *)
      operation="unknown"
      echo "[orchestrate-mt] Task $task_num status '$dispatch_status' — no postflight update"
      ;;
  esac
  
  # Artifact linking (same logic as single-task Stage 5)
  handoff_artifact_path=$(echo "$handoff" | jq -r '.artifacts[0].path // ""')
  handoff_artifact_type=$(echo "$handoff" | jq -r '.artifacts[0].type // ""')
  handoff_artifact_summary=$(echo "$handoff" | jq -r '.artifacts[0].summary // ""')
  if [ -n "$handoff_artifact_path" ] && [ "$handoff_artifact_path" != "null" ]; then
    case "$handoff_artifact_type" in
      report)
        field_name='**Research**'
        next_field='**Plan**'
        ;;
      plan)
        field_name='**Plan**'
        next_field='**Description**'
        ;;
      summary)
        field_name='**Summary**'
        next_field='**Description**'
        ;;
      *)
        field_name='**Summary**'
        next_field='**Description**'
        ;;
    esac
    skill_link_artifacts "$task_num" "$handoff_artifact_path" "$handoff_artifact_type" \
      "$handoff_artifact_summary" "$field_name" "$next_field"
  fi
  
  # Update multi-state current_statuses and move to completed/failed as appropriate
  # Re-read fresh status from state.json (postflight may have updated it)
  fresh_status=$(jq -r --argjson num "$task_num" \
    '.active_projects[] | select(.project_number == $num) | .status' \
    specs/state.json)
  
  if [ "$fresh_status" = "completed" ]; then
    jq --argjson num "$task_num" \
      '.completed_tasks = (.completed_tasks + [$num] | unique) |
       .current_statuses[$num | tostring] = "completed"' \
      "$mt_state_file" > "${mt_state_file}.tmp" && mv "${mt_state_file}.tmp" "$mt_state_file"
  elif [ "$dispatch_status" = "failed" ] || [ "$dispatch_status" = "blocked" ]; then
    jq --argjson num "$task_num" \
      '.failed_tasks = (.failed_tasks + [$num] | unique) |
       .current_statuses[$num | tostring] = $num' \
      "$mt_state_file" > "${mt_state_file}.tmp" && mv "${mt_state_file}.tmp" "$mt_state_file"
  else
    jq --argjson num "$task_num" \
       --arg status "$fresh_status" \
      '.current_statuses[$num | tostring] = $status' \
      "$mt_state_file" > "${mt_state_file}.tmp" && mv "${mt_state_file}.tmp" "$mt_state_file"
  fi
done

# Increment cycle_count and update multi-state
cycle_count=$(jq -r '.cycle_count' "$mt_state_file")
cycle_count=$((cycle_count + 1))
jq --argjson count "$cycle_count" \
  '.cycle_count = $count' \
  "$mt_state_file" > "${mt_state_file}.tmp" && mv "${mt_state_file}.tmp" "$mt_state_file"

# Cycle guard: exit if MAX_CYCLES_MT reached
if [ "$cycle_count" -ge "$MAX_CYCLES_MT" ]; then
  echo "[orchestrate-mt] MAX_CYCLES ($MAX_CYCLES_MT) reached. Writing partial results."
  completed_tasks=$(jq -c '.completed_tasks' "$mt_state_file")
  failed_tasks=$(jq -c '.failed_tasks' "$mt_state_file")
  echo "[orchestrate-mt] Completed: $completed_tasks | Failed: $failed_tasks"
  # Proceed to Stage MT-5 with partial status
fi
```

### Stage MT-5: Multi-Task Postflight

On completion of the wave loop (all tasks completed, all waves processed, or MAX_CYCLES reached):

```bash
# Read final multi-state
completed_tasks=$(jq -c '.completed_tasks // []' "$mt_state_file")
failed_tasks=$(jq -c '.failed_tasks // []' "$mt_state_file")
cycles_used=$(jq -r '.cycle_count // 0' "$mt_state_file")
completed_count=$(jq '.completed_tasks | length' "$mt_state_file")
failed_count=$(jq '.failed_tasks | length' "$mt_state_file")
total_count=$(jq '.task_numbers | length' "$mt_state_file")

if [ "$failed_count" -eq 0 ]; then
  echo "[orchestrate-mt] All $total_count tasks completed. Cycles used: $cycles_used/$MAX_CYCLES_MT"
  # On clean exit: remove multi-state file
  rm -f "$mt_state_file"
  exit_status="implemented"
else
  echo "[orchestrate-mt] Partial: $completed_count/$total_count completed, $failed_count failed."
  echo "[orchestrate-mt] Multi-state preserved at: $mt_state_file (for diagnostics)"
  exit_status="partial"
fi

# Write .return-meta.json with aggregated results
jq -n \
  --arg status "$exit_status" \
  --argjson tasks_completed "$completed_tasks" \
  --argjson tasks_failed "$failed_tasks" \
  --argjson cycles_used "$cycles_used" \
  '{
    "status": $status,
    "metadata": {
      "tasks_completed": $tasks_completed,
      "tasks_failed": $tasks_failed,
      "cycles_used": $cycles_used,
      "multi_task_mode": true
    }
  }' > "specs/.return-meta-multi.json"
echo "[orchestrate-mt] Return metadata written: specs/.return-meta-multi.json"
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
