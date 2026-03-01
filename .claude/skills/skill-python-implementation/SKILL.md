---
name: skill-python-implementation
description: Implement Python and ModelChecker development tasks with testing and verification. Invoke for python language tasks requiring implementation.
allowed-tools: Task, Bash, Edit, Read, Write
---

# Python Implementation Skill

Thin wrapper that delegates Python/ModelChecker implementation to `python-implementation-agent` subagent.

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
- Task language is "python"
- Implementation is needed for ModelChecker development
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
  "skill": "skill-python-implementation",
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
  "delegation_path": ["orchestrator", "implement", "skill-python-implementation"],
  "timeout": 7200,
  "task_context": {
    "task_number": N,
    "task_name": "{project_name}",
    "description": "{description}",
    "language": "python"
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
  - subagent_type: "python-implementation-agent"
  - prompt: [Include task_context, delegation_context, plan_path, metadata_file_path]
  - description: "Execute Python implementation for task {N}"
```

The subagent will:
- Execute implementation plan phases
- Create/modify Python files
- Run pytest verification
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
   --arg summary "Implementation summary with test results" \
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
Python implementation completed for task {N}:
- All phases executed successfully
- Files modified: {list}
- Tests: {count} passing
- Created summary at specs/{NNN}_{SLUG}/summaries/implementation-summary-{DATE}.md
- Status updated to [COMPLETED]
- Changes committed
```

---

## Error Handling

- **Plan not found**: Return error immediately
- **Test failures**: Keep status as "implementing", report errors
- **Metadata file missing**: Keep status as "implementing"
- **Git commit failure**: Non-blocking, log and continue
