---
name: skill-z3-research
description: Conduct Z3 SMT solving research using codebase exploration and Z3 documentation. Invoke for z3 language tasks requiring research.
allowed-tools: Task, Bash, Edit, Read, Write
---

# Z3 Research Skill

Thin wrapper that delegates Z3/SMT research to `z3-research-agent` subagent.

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
- Research is needed for Z3/SMT constraint development
- Z3 documentation or patterns need to be gathered

---

## Execution Flow

### Stage 1: Input Validation

Validate required inputs:
- `task_number` - Must be provided and exist in state.json
- `focus_prompt` - Optional focus for research direction

```bash
# Lookup task
task_data=$(jq -r --argjson num "$task_number" \
  '.active_projects[] | select(.project_number == $num)' \
  specs/state.json)

# Validate exists and language is z3
language=$(echo "$task_data" | jq -r '.language // "general"')
if [ "$language" != "z3" ]; then
  echo "Warning: Task language is $language, not z3"
fi
```

---

### Stage 2: Preflight Status Update

Update task status to "researching" BEFORE invoking subagent.

**Update state.json**:
```bash
jq --arg ts "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
   --arg status "researching" \
   --arg sid "$session_id" \
  '(.active_projects[] | select(.project_number == '$task_number')) |= . + {
    status: $status,
    last_updated: $ts,
    session_id: $sid
  }' specs/state.json > /tmp/state.json && mv /tmp/state.json specs/state.json
```

**Update TODO.md**: Use Edit tool to change status marker to `[RESEARCHING]`.

---

### Stage 3: Create Postflight Marker

```bash
padded_num=$(printf "%03d" "$task_number")
mkdir -p "specs/${padded_num}_${project_name}"

cat > "specs/${padded_num}_${project_name}/.postflight-pending" << EOF
{
  "session_id": "${session_id}",
  "skill": "skill-z3-research",
  "task_number": ${task_number},
  "operation": "research",
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
  "delegation_path": ["orchestrator", "research", "skill-z3-research"],
  "timeout": 3600,
  "task_context": {
    "task_number": N,
    "task_name": "{project_name}",
    "description": "{description}",
    "language": "z3"
  },
  "focus_prompt": "{optional focus}",
  "metadata_file_path": "specs/{NNN}_{SLUG}/.return-meta.json"
}
```

---

### Stage 5: Invoke Subagent

**CRITICAL**: Use the **Task** tool to spawn the subagent.

```
Tool: Task (NOT Skill)
Parameters:
  - subagent_type: "z3-research-agent"
  - prompt: [Include task_context, delegation_context, focus_prompt, metadata_file_path]
  - description: "Execute Z3 research for task {N}"
```

The subagent will:
- Search ModelChecker codebase for Z3 patterns
- Search web for Z3/SMT documentation
- Analyze constraint patterns and solver tactics
- Create research report in `specs/{NNN}_{SLUG}/reports/`
- Write metadata to `specs/{NNN}_{SLUG}/.return-meta.json`

---

### Stage 6: Parse Subagent Return

Read metadata file after subagent returns:

```bash
metadata_file="specs/${padded_num}_${project_name}/.return-meta.json"

if [ -f "$metadata_file" ] && jq empty "$metadata_file" 2>/dev/null; then
    status=$(jq -r '.status' "$metadata_file")
    artifact_path=$(jq -r '.artifacts[0].path // ""' "$metadata_file")
fi
```

---

### Stage 7: Update Task Status (Postflight)

If status is "researched":

**Update state.json**:
```bash
jq --arg ts "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
   --arg status "researched" \
  '(.active_projects[] | select(.project_number == '$task_number')) |= . + {
    status: $status,
    last_updated: $ts,
    researched: $ts
  }' specs/state.json > /tmp/state.json && mv /tmp/state.json specs/state.json
```

**Update TODO.md**: Change status marker to `[RESEARCHED]`.

---

### Stage 8: Link Artifacts

Add artifact to state.json using two-step jq pattern (Issue #1132):

```bash
# Step 1: Filter existing research artifacts
jq '(.active_projects[] | select(.project_number == '$task_number')).artifacts =
    [(.active_projects[] | select(.project_number == '$task_number')).artifacts // [] | .[] | select(.type == "research" | not)]' \
  specs/state.json > /tmp/state.json && mv /tmp/state.json specs/state.json

# Step 2: Add new artifact
jq --arg path "$artifact_path" \
   --arg type "research" \
   --arg summary "$artifact_summary" \
  '(.active_projects[] | select(.project_number == '$task_number')).artifacts += [{"path": $path, "type": $type, "summary": $summary}]' \
  specs/state.json > /tmp/state.json && mv /tmp/state.json specs/state.json
```

---

### Stage 9: Git Commit

```bash
git add -A
git commit -m "task ${task_number}: complete research

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
Z3 research completed for task {N}:
- Found {count} relevant Z3 patterns and resources
- Identified constraint approach
- Created report at specs/{NNN}_{SLUG}/reports/research-{NNN}.md
- Status updated to [RESEARCHED]
- Changes committed
```

---

## Error Handling

- **Task not found**: Return error immediately
- **Metadata file missing**: Keep status as "researching"
- **Git commit failure**: Non-blocking, log and continue
