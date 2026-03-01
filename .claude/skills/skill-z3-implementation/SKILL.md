---
name: skill-z3-implementation
description: Implement Z3 constraint solving tasks with solver verification. Invoke for z3 language tasks requiring implementation.
allowed-tools: Task, Bash, Edit, Read, Write
---

# Z3 Implementation Skill

Thin wrapper that delegates Z3/SMT implementation to `z3-implementation-agent` subagent.

**IMPORTANT**: This skill implements the skill-internal postflight pattern. After the subagent returns,
this skill handles all postflight operations (status update, artifact linking, git commit) before returning.

## Context References

Reference (do not load eagerly):
- Path: `.claude/context/core/formats/return-metadata-file.md` - Metadata file schema
- Path: `.claude/context/core/patterns/postflight-control.md` - Marker file protocol
- Path: `.claude/context/core/patterns/jq-escaping-workarounds.md` - jq escaping patterns

Note: This skill is a thin wrapper with internal postflight. Context is loaded by the delegated agent.

## Trigger Conditions

This skill activates when:
- Task language is "z3"
- Implementation is needed for Z3/SMT constraint development
- Task has status "planned" with implementation plan

---

## Execution Flow

### Stage 1: Input Validation

Validate required inputs:
- `task_number` - Must be provided and exist in state.json
- Task must have status "planned"
- Implementation plan must exist

```bash
# Lookup task
task_data=$(jq -r --argjson num "$task_number" \
  '.active_projects[] | select(.project_number == $num)' \
  specs/state.json)

# Validate status allows implementation
status=$(echo "$task_data" | jq -r '.status')
if [ "$status" != "planned" ]; then
  echo "Error: Task status is $status, expected planned"
  exit 1
fi

# Find plan file
padded_num=$(printf "%03d" "$task_number")
project_name=$(echo "$task_data" | jq -r '.project_name')
plan_file="specs/${padded_num}_${project_name}/plans/implementation-001.md"
```

---

### Stage 2: Preflight Status Update

Update task status to "implementing" BEFORE invoking subagent.

**Update state.json**:
```bash
jq --arg ts "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
   --arg status "implementing" \
   --arg sid "$session_id" \
  '(.active_projects[] | select(.project_number == '$task_number')) |= . + {
    status: $status,
    last_updated: $ts,
    session_id: $sid
  }' specs/state.json > /tmp/state.json && mv /tmp/state.json specs/state.json
```

**Update TODO.md**: Use Edit tool to change status marker to `[IMPLEMENTING]`.

---

### Stage 3: Create Postflight Marker

```bash
cat > "specs/${padded_num}_${project_name}/.postflight-pending" << EOF
{
  "session_id": "${session_id}",
  "skill": "skill-z3-implementation",
  "task_number": ${task_number},
  "operation": "implement",
  "reason": "Postflight pending"
}
EOF
```

---

### Stage 4: Prepare Delegation Context

```json
{
  "session_id": "sess_{timestamp}_{random}",
  "delegation_depth": 1,
  "delegation_path": ["orchestrator", "implement", "skill-z3-implementation"],
  "timeout": 7200,
  "task_context": {
    "task_number": N,
    "task_name": "{project_name}",
    "description": "{description}",
    "language": "z3"
  },
  "plan_path": "specs/{NNN}_{SLUG}/plans/implementation-001.md",
  "metadata_file_path": "specs/{NNN}_{SLUG}/.return-meta.json"
}
```

---

### Stage 5: Invoke Subagent

**CRITICAL**: Use the **Task** tool to spawn the subagent.

```
Tool: Task (NOT Skill)
Parameters:
  - subagent_type: "z3-implementation-agent"
  - prompt: [Include task_context, delegation_context, plan_path, metadata_file_path]
  - description: "Execute Z3 implementation for task {N}"
```

The subagent will:
- Execute implementation plan phases
- Create/modify Z3 constraint code
- Run Z3 solver verification
- Create implementation summary
- Write metadata to `specs/{NNN}_{SLUG}/.return-meta.json`

---

### Stage 6: Parse Subagent Return

Read metadata file after subagent returns:

```bash
metadata_file="specs/${padded_num}_${project_name}/.return-meta.json"

if [ -f "$metadata_file" ] && jq empty "$metadata_file" 2>/dev/null; then
    status=$(jq -r '.status' "$metadata_file")
    completion_summary=$(jq -r '.completion_data.completion_summary // ""' "$metadata_file")
    z3_version=$(jq -r '.metadata.z3_version // ""' "$metadata_file")
    artifact_path=$(jq -r '.artifacts[] | select(.type == "summary") | .path' "$metadata_file")
fi
```

---

### Stage 7: Update Task Status (Postflight)

If status is "implemented":

**Update state.json**:
```bash
jq --arg ts "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
   --arg status "completed" \
   --arg summary "$completion_summary" \
  '(.active_projects[] | select(.project_number == '$task_number')) |= . + {
    status: $status,
    last_updated: $ts,
    completed: $ts,
    completion_summary: $summary
  }' specs/state.json > /tmp/state.json && mv /tmp/state.json specs/state.json
```

**Update TODO.md**: Change status marker to `[COMPLETED]`.

**On partial/failed**: Keep status as "implementing" for resume.

---

### Stage 8: Link Artifacts

Add implementation artifacts to state.json:

```bash
# Add summary artifact
jq --arg path "$artifact_path" \
   --arg type "summary" \
   --arg summary "Implementation summary with Z3 verification" \
  '(.active_projects[] | select(.project_number == '$task_number')).artifacts += [{"path": $path, "type": $type, "summary": $summary}]' \
  specs/state.json > /tmp/state.json && mv /tmp/state.json specs/state.json
```

---

### Stage 9: Git Commit

```bash
git add -A
git commit -m "task ${task_number}: complete implementation

Session: ${session_id}

Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>"
```

---

### Stage 10: Cleanup

```bash
rm -f "specs/${padded_num}_${project_name}/.postflight-pending"
rm -f "specs/${padded_num}_${project_name}/.return-meta.json"
```

---

### Stage 11: Return Brief Summary

```
Z3 implementation completed for task {N}:
- All phases executed successfully
- Z3 version: {version}
- Files modified: {list}
- Solver tests: passing
- Created summary at specs/{NNN}_{SLUG}/summaries/implementation-summary-{DATE}.md
- Status updated to [COMPLETED]
- Changes committed
```

---

## Error Handling

- **Plan not found**: Return error immediately
- **Solver timeout**: Report with recommendation for longer timeout
- **Z3 constraint error**: Keep status as "implementing", report errors
- **Metadata file missing**: Keep status as "implementing"
- **Git commit failure**: Non-blocking, log and continue
