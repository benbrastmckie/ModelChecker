---
description: Execute a task autonomously through its full lifecycle (research -> plan -> implement -> complete) without user confirmation between phases
allowed-tools: Skill, Agent, Bash(jq:*), Bash(git:*), Read
argument-hint: TASK_NUMBERS [PROMPT]
model: opus
---

# /orchestrate Command

Drive a task through its complete lifecycle autonomously without pausing for user confirmation.
Implements fire-and-forget state machine: research -> plan -> implement -> complete.

## Arguments

- `$1` - Task number(s) (required). Supports single task, comma-separated lists, and ranges.
  - Single: `42`
  - Comma-separated: `42, 43, 45`
  - Range: `42-45`
  - Mixed: `42, 44-46, 50`
- `$2+` - Optional prompt/focus text (e.g., `focus on the LSP config`). Applies to all tasks in multi-task mode.

## Constraints

- Multi-task mode uses dependency-aware wave dispatch. `--team` flag not supported.
- No confirmation gates between lifecycle phases
- Terminates automatically on success, MAX_CYCLES exceeded, or unrecoverable blocker
- In multi-task mode, failure in one task does not block other tasks in the same wave, but DOES block dependent tasks in later waves

## Anti-Bypass Constraint

**PROHIBITION**: All lifecycle phases (research, plan, implement) MUST be executed by delegating
to `skill-orchestrate` via the Skill tool. Never run research/plan/implement directly from this
command.

## Execution

### STAGE 0: PARSE AND DISPATCH

```bash
source .claude/scripts/parse-command-args.sh "$ARGUMENTS"
# Exports: TASK_NUMBERS (space-separated), FOCUS_PROMPT, REMAINING_ARGS
focus_prompt="${FOCUS_PROMPT:-}"
```

If `len(TASK_NUMBERS) == 1`: extract `task_number=$(echo "$TASK_NUMBERS" | awk '{print $1}')` and fall through to CHECKPOINT 1: GATE IN.

If `len(TASK_NUMBERS) > 1`: continue to MULTI-TASK DISPATCH below.

---

### MULTI-TASK DISPATCH

#### Step 1: Batch Validation

```bash
validated_tasks=(); skipped_tasks=()
for task_num in "${TASK_NUMBERS[@]}"; do
  task_data=$(jq -r --argjson num "$task_num" \
    '.active_projects[] | select(.project_number == $num)' specs/state.json)
  if [ -z "$task_data" ]; then
    skipped_tasks+=("$task_num: not found")
    continue
  fi
  status=$(echo "$task_data" | jq -r '.status')
  case "$status" in
    completed|abandoned|expanded)
      skipped_tasks+=("$task_num: terminal status [$status]")
      continue
      ;;
  esac
  validated_tasks+=("$task_num")
done
```

Report skipped tasks as warnings. If no validated tasks remain, ABORT with error.

#### Step 2: Dependency Graph Construction

For each task in `validated_tasks`, read its `dependencies` field from state.json. Restrict to **intra-batch dependencies only** (ignore dependencies on tasks not in `validated_tasks`):

```bash
# Build adjacency map: task -> list of validated predecessors it depends on
declare -A predecessors   # predecessors[$task] = space-separated list of intra-batch deps
declare -A in_degree      # in_degree[$task] = count of intra-batch predecessors

for task_num in "${validated_tasks[@]}"; do
  deps=$(jq -r --argjson num "$task_num" \
    '.active_projects[] | select(.project_number == $num) | .dependencies // [] | .[]' \
    specs/state.json)
  intra_deps=()
  for dep in $deps; do
    # Only include deps that are also in validated_tasks
    if [[ " ${validated_tasks[*]} " == *" $dep "* ]]; then
      intra_deps+=("$dep")
    fi
  done
  predecessors[$task_num]="${intra_deps[*]}"
  in_degree[$task_num]=${#intra_deps[@]}
done
```

#### Step 3: Topological Wave Assignment (Kahn's Algorithm)

```bash
# Initialize: collect tasks with no intra-batch predecessors into Wave 0
declare -A wave_assignment
waves=()
remaining=("${validated_tasks[@]}")

wave_num=0
while [ ${#remaining[@]} -gt 0 ]; do
  ready=()
  next_remaining=()

  for task in "${remaining[@]}"; do
    if [ "${in_degree[$task]}" -eq 0 ]; then
      ready+=("$task")
      wave_assignment[$task]=$wave_num
    else
      next_remaining+=("$task")
    fi
  done

  # Circular dependency detection: if no tasks are ready but remaining is non-empty
  if [ ${#ready[@]} -eq 0 ]; then
    echo "[ERROR] Circular dependency detected among tasks: ${remaining[*]}"
    echo "Aborting multi-task orchestration."
    return 1
  fi

  waves+=("${ready[*]}")
  remaining=("${next_remaining[@]}")

  # Decrement in-degree for tasks whose predecessor just completed this wave
  for completed in "${ready[@]}"; do
    for task in "${remaining[@]}"; do
      if [[ " ${predecessors[$task]} " == *" $completed "* ]]; then
        in_degree[$task]=$(( ${in_degree[$task]} - 1 ))
      fi
    done
  done

  wave_num=$(( wave_num + 1 ))
done
```

Wave assignment summary: tasks in Wave 0 have no intra-batch predecessors and run first. Tasks in Wave 1 depend only on Wave 0 tasks, and so on. All tasks within a wave are independent and can run in parallel.

#### Step 4: Wave Execution

Generate the batch session ID:

```bash
batch_session_id="sess_$(date +%s)_$(od -An -N3 -tx1 /dev/urandom | tr -d ' ')"
```

**MAX_TASKS Guard**: Before entering multi-task dispatch, check task count:

```bash
task_count=${#validated_tasks[@]}
MAX_TASKS=8
if [ "$task_count" -gt "$MAX_TASKS" ]; then
  echo "[orchestrate] WARNING: $task_count tasks exceeds MAX_TASKS=$MAX_TASKS."
  echo "Batching is not yet supported. Running with first $MAX_TASKS tasks only."
  validated_tasks=("${validated_tasks[@]:0:$MAX_TASKS}")
  # Recalculate waves for the trimmed task list
fi
```

**Single-Dispatch Multi-Task Mode**: Build the dependency graph JSON and waves JSON for passing to the skill, then invoke a single `skill-orchestrate` instance that manages all tasks internally:

```bash
# Build dependency_graph JSON: {"task_num": [dep1, dep2], ...}
dep_graph_json=$(jq -n '{}')
for task_num in "${validated_tasks[@]}"; do
  deps_array=$(jq -n --argjson deps "$(printf '%s\n' "${predecessors[$task_num]}" | jq -R . | jq -s .)" '$deps')
  dep_graph_json=$(echo "$dep_graph_json" | jq --arg key "$task_num" --argjson deps "$deps_array" \
    '. + {($key): $deps}')
done

# Build waves JSON: [[task_a, task_b], [task_c], ...]
waves_json=$(jq -n '[]')
for wave_tasks in "${waves[@]}"; do
  wave_array=$(printf '%s\n' $wave_tasks | jq -R 'tonumber' | jq -s '.')
  waves_json=$(echo "$waves_json" | jq --argjson wave "$wave_array" '. + [$wave]')
done

# Build task_numbers JSON array
task_numbers_json=$(printf '%s\n' "${validated_tasks[@]}" | jq -R 'tonumber' | jq -s '.')
```

Invoke a single `skill-orchestrate` instance with all task context:

```
Tool: Skill
Parameters:
  skill: "skill-orchestrate"
  args: "multi_task_mode=true task_numbers={task_numbers_json} waves={waves_json} dependency_graph={dep_graph_json} session_id={batch_session_id} focus_prompt={focus_prompt}"
```

The delegation context passed to the skill must include:
```json
{
  "session_id": "{batch_session_id}",
  "multi_task_mode": true,
  "task_numbers": [42, 43, 44],
  "waves": [[42], [43, 44]],
  "dependency_graph": {"42": [], "43": [42], "44": [42]},
  "focus_prompt": "{focus_prompt}"
}
```

The skill manages wave-by-wave dispatch, per-task postflight (status sync + artifact linking), and writes results to `specs/.orchestrator-multi-state.json`.

#### Step 5: Batch Git Commit and Consolidated Output

After the single `skill-orchestrate` invocation completes, read results from `specs/.orchestrator-multi-state.json` and produce a batch git commit (non-blocking) and consolidated output.

```bash
mt_state_file="specs/.orchestrator-multi-state.json"
if [ -f "$mt_state_file" ]; then
  completed_tasks=$(jq -r '.completed_tasks[]' "$mt_state_file" 2>/dev/null | tr '\n' ' ')
  failed_tasks_json=$(jq -c '.failed_tasks // []' "$mt_state_file")
  cycles_used=$(jq -r '.cycle_count // 0' "$mt_state_file")
  max_cycles=$(jq -r '.max_cycles // 25' "$mt_state_file")
  succeeded_count=$(jq '.completed_tasks | length' "$mt_state_file")
  failed_count=$(jq '.failed_tasks | length' "$mt_state_file")
else
  echo "[orchestrate] WARNING: Multi-state file missing — skill may have been interrupted"
  completed_tasks=""
  failed_tasks_json="[]"
  cycles_used=0
  succeeded_count=0
  failed_count=${#validated_tasks[@]}
fi
skipped_count=${#skipped_tasks[@]}
```

**Batch Git Commit**:

Full success (all tasks completed):
```bash
git add -A && git commit -m "orchestrate tasks {range_summary}: complete orchestration

Tasks: {comma-separated succeeded list}
Session: {batch_session_id}"
```

Partial success:
```bash
git add -A && git commit -m "orchestrate tasks {range_summary}: complete orchestration ({succeeded}/{total} succeeded)

Tasks completed: {comma-separated succeeded list}
Tasks failed: {failed_count} (see multi-state log)
Tasks skipped: {skipped_count}
Session: {batch_session_id}"
```

**Consolidated Output**:

```markdown
## Batch Orchestrate Results

Session: {batch_session_id}
Tasks requested: {count}
Succeeded: {succeeded_count}
Failed: {failed_count}
Skipped: {skipped_count}
Cycles used: {cycles_used}/{max_cycles}

### Succeeded

| Task | Title | Final Status |
|------|-------|--------------|
| #42 | task_title | [COMPLETED] |

### Failed

| Task | Error |
|------|-------|
| #43 | Partial: blockers present (no continuation) |

### Skipped

| Task | Reason |
|------|--------|
| #44 | predecessor #43 failed |
| #99 | terminal status [ABANDONED] |

### Next Steps
- Re-run failed tasks: /orchestrate {failed_task_numbers}
```

**After consolidated output, STOP. Do not continue to CHECKPOINT 1.**

---

### CHECKPOINT 1: GATE IN

```bash
source .claude/scripts/command-gate-in.sh "$task_number" "orchestrate"
# Exports: SESSION_ID, TASK_TYPE, TASK_STATUS, PROJECT_NAME, DESCRIPTION, PADDED_NUM
# Displays: [ORCHESTRATE] Task {N}: {project_name}
```

**Permissive gate**: Unlike `/implement`, this command does NOT require a plan file.
The state machine handles all lifecycle phases starting from wherever the task currently is.

**Only blocks on terminal states**: `completed`, `abandoned`, `expanded`.
All non-terminal states (not_started, researched, planned, implementing, partial, blocked) are
valid entry points for the orchestrator.

**On GATE IN success**: Task validated. **IMMEDIATELY CONTINUE** to STAGE 2.

### STAGE 2: DELEGATE

**EXECUTE NOW**: After CHECKPOINT 1 completes, immediately invoke the Skill tool.

Invoke `skill-orchestrate` via the Skill tool:

```
skill: "skill-orchestrate"
args: "task_number={N} session_id={SESSION_ID} orchestrator_mode=true"
```

The delegation context passed to the skill must include:
```json
{
  "session_id": "{SESSION_ID}",
  "delegation_depth": 1,
  "delegation_path": ["orchestrator", "orchestrate", "skill-orchestrate"],
  "task_context": {
    "task_number": N,
    "task_name": "{PROJECT_NAME}",
    "description": "{DESCRIPTION}",
    "task_type": "{TASK_TYPE}"
  },
  "orchestrator_mode": true,
  "focus_prompt": "{FOCUS_PROMPT}"
}
```

**On DELEGATE success**: Orchestration complete. **IMMEDIATELY CONTINUE** to CHECKPOINT 2.

### CHECKPOINT 2: GATE OUT

```bash
bash .claude/scripts/command-gate-out.sh "$task_number" "orchestrate" "$SESSION_ID"
# Reads .return-meta.json; applies defensive status correction if needed
```

**Populate Completion Summary (if implemented)**:

```bash
completion_summary="$result_summary"
jq --arg summary "$completion_summary" \
  '(.active_projects[] | select(.project_number == '"$task_number"')).completion_summary = $summary' \
  specs/state.json > specs/tmp/state.json && mv specs/tmp/state.json specs/state.json
```

**On GATE OUT success**: IMMEDIATELY CONTINUE to CHECKPOINT 3.

### CHECKPOINT 3: COMMIT

**On completion:**
```bash
git add -A && git commit -m "task {N}: complete orchestration

Session: {SESSION_ID}"
```

**On partial:**
```bash
git add -A && git commit -m "task {N}: orchestration paused (cycles {M}/{MAX})

Session: {SESSION_ID}"
```

Commit failure is non-blocking (log and continue).

## Output

**Completion**: `Orchestration complete for Task #{N}` | Final status: `[COMPLETED]` | Cycles: M/5

**Partial**: `Orchestration paused for Task #{N}` | Status: `[{STATUS}]` | Cycles: M/5 | `Next: /orchestrate {N}`

**Blocked**: `Task #{N} requires manual intervention` | Blocker description | Suggested actions

## Error Handling

- **GATE IN Failure**: Task not found or in terminal state — return error with guidance
- **DELEGATE Failure**: Keep current status, log error; loop guard preserved for resume
- **GATE OUT Failure**: Missing artifacts — log warning, continue with available
- **MAX_CYCLES Reached**: Report status, provide `/orchestrate {N}` resume instruction
