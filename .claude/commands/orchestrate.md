---
description: Execute a task autonomously through its full lifecycle (research -> plan -> implement -> complete) without user confirmation between phases
allowed-tools: Skill, Agent, Bash(jq:*), Bash(git:*), Read
argument-hint: TASK_NUMBER [PROMPT]
model: opus
---

# /orchestrate Command

Drive a task through its complete lifecycle autonomously without pausing for user confirmation.
Implements fire-and-forget state machine: research -> plan -> implement -> complete.

## Arguments

- `$1` - Single task number (e.g., `42`)
- `$2+` - Optional prompt/focus text (e.g., `focus on the LSP config`)

## Constraints

- Single task only: no multi-task, no `--team` flag in v1
- No confirmation gates between lifecycle phases
- Terminates automatically on success, MAX_CYCLES exceeded, or unrecoverable blocker

## Anti-Bypass Constraint

**PROHIBITION**: All lifecycle phases (research, plan, implement) MUST be executed by delegating
to `skill-orchestrate` via the Skill tool. Never run research/plan/implement directly from this
command.

## Execution

### STAGE 0: PARSE ARGS

```bash
source .claude/scripts/parse-command-args.sh "$ARGUMENTS"
task_number=$(echo "$TASK_NUMBERS" | awk '{print $1}')
focus_prompt="${FOCUS_PROMPT:-}"
```

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
