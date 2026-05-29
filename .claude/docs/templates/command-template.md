---
description: <one-line description of what this command does>
allowed-tools: Skill, Agent, Bash(jq:*), Bash(git:*), Read, Edit
argument-hint: "<required-arg>" [--flag]
model: sonnet
---

# /<command-name> Command

<Brief description of what this command does and when to use it.>

**Use this command when you need to**: <specific use case>

## Arguments

- `$1` - Task number(s) (required). Supports single task, comma-separated lists, and ranges.
- Remaining args - Optional focus/prompt (applies to all tasks in multi-task mode)

## Options

| Flag | Description | Default |
|------|-------------|---------|
| `--team` | Enable multi-agent parallel execution | false |
| `--fast` | Low-effort mode | false |
| `--hard` | High-effort mode | false |

## Execution

### STAGE 0: PARSE TASK NUMBERS

```bash
source .claude/scripts/parse-command-args.sh "$ARGUMENTS"
# Exports: TASK_NUMBERS, REMAINING_ARGS, TEAM_MODE, TEAM_SIZE,
#          EFFORT_FLAG, MODEL_FLAG, CLEAN_FLAG, FORCE_FLAG, FOCUS_PROMPT
```

If `len(TASK_NUMBERS) > 1`: dispatch to multi-task batch flow.
If `len(TASK_NUMBERS) == 1`: fall through to CHECKPOINT 1.

### CHECKPOINT 1: GATE IN

```bash
source .claude/scripts/command-gate-in.sh "$task_number" "<operation>"
# Exports: SESSION_ID, TASK_TYPE, TASK_STATUS, PROJECT_NAME, DESCRIPTION, PADDED_NUM
# Displays: [OPERATION] Task {N}: {project_name}
# Aborts if task not found or in terminal status
```

**On GATE IN success**: Task validated. **IMMEDIATELY CONTINUE** to STAGE 2.

### STAGE 2: DELEGATE

```bash
source .claude/scripts/command-route-skill.sh "<operation>" "$TASK_TYPE" "skill-<default>"
skill_name="$SKILL_NAME"
```

**Invoke the Skill tool NOW** with:
```
skill: "{skill_name}"
args: "task_number={N} session_id={SESSION_ID} effort_flag={EFFORT_FLAG} model_flag={MODEL_FLAG} clean_flag={CLEAN_FLAG} orchestrator_mode=false"
```

**On DELEGATE success**: **IMMEDIATELY CONTINUE** to CHECKPOINT 2.

### CHECKPOINT 2: GATE OUT

```bash
bash .claude/scripts/command-gate-out.sh "$task_number" "<operation>" "$SESSION_ID"
# Reads .return-meta.json; applies defensive status correction if needed
# Runs validate-artifact.sh --fix (non-blocking)
```

**On GATE OUT success**: **IMMEDIATELY CONTINUE** to CHECKPOINT 3.

### CHECKPOINT 3: COMMIT

```bash
git add -A
git commit -m "$(cat <<'EOF'
task {N}: <action>

Session: {SESSION_ID}

EOF
)"
```

Commit failure is non-blocking (log and continue).

## Output

```
<Operation> completed for Task #{N}

Artifact: specs/{NNN}_{SLUG}/<type>/MM_{short-slug}.md

Status: [<STATUS>]
Next: /<next-command> {N}
```

## Error Handling

- **GATE IN Failure**: Task not found or invalid status -- return error with guidance
- **DELEGATE Failure**: Keep in-progress status, log error; timeout preserves partial progress
- **GATE OUT Failure**: Missing artifacts -- log warning, continue with available

## Related Documentation

- [Creating Commands](../guides/creating-commands.md) - Step-by-step command creation
- [Command Lifecycle](../../context/workflows/command-lifecycle.md) - Checkpoint stage details
- [Return Format](../../context/formats/subagent-return.md) - Agent return-metadata schema
