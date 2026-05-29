# Integration Example: Research Flow

This example traces a complete `/research` command through all three layers of the project agent system, showing how commands, skills, and agents work together.

---

## Scenario

A user runs `/research 427` to research task 427 (documenting the command/skill/subagent framework). This is a "meta" language task.

---

## Complete Flow Diagram

```
User Input: /research 427
       |
       v
[Layer 1: Command] .claude/commands/research.md
       |
       | 1. parse-command-args.sh -> task_number = 427
       | 2. command-gate-in.sh -> session_id, task validation
       | 3. command-route-skill.sh -> meta -> skill-researcher
       v
[Layer 2: Skill] skill-researcher/SKILL.md
       |
       | 1. skill-base.sh: validate, preflight, marker
       | 2. Prepare delegation context
       | 3. Invoke general-research-agent via Agent tool
       v
[Layer 3: Agent] general-research-agent.md
       |
       | 1. Parse delegation context
       | 2. Load required context files
       | 3. Execute research (codebase + web)
       | 4. Create report artifact
       | 5. Write .return-meta.json
       v
[Return Flow]
       |
       | Agent -> Skill (postflight) -> Command (gate-out) -> User
       v
Output: Research report created at specs/427_document.../reports/01_research-findings.md
```

---

## Step-by-Step Walkthrough

### Step 1: User Invokes Command

```bash
/research 427
```

Claude Code reads `.claude/commands/research.md`, which executes shared infrastructure scripts.

### Step 2: Command Parses Arguments and Validates Task

The command uses shared gate scripts instead of a separate orchestrator.

**STAGE 0: Parse Arguments** (`parse-command-args.sh`)
```bash
source .claude/scripts/parse-command-args.sh "427"
# Exports: TASK_NUMBERS=(427), TEAM_MODE=false, EFFORT_FLAG=, MODEL_FLAG=
```

**CHECKPOINT 1: Gate In** (`command-gate-in.sh`)
```bash
source .claude/scripts/command-gate-in.sh 427 "research"
# Validates task exists, generates session_id, updates status to "researching"
# Exports: SESSION_ID, TASK_TYPE="meta", PROJECT_NAME, PADDED_NUM
```

**STAGE 2: Route by Task Type** (`command-route-skill.sh`)
```bash
source .claude/scripts/command-route-skill.sh "research" "meta" "skill-researcher"
# Routes: meta -> skill-researcher (default)
# Extension task types route to domain-specific skills
```

### Step 3: Skill Validates and Delegates

The command invokes `skill-researcher` via the Skill tool. The skill uses `skill-base.sh` shared lifecycle functions.

**Skill Steps 1-3: Validate, Preflight, Marker** (`skill-base.sh`)

```bash
source .claude/scripts/skill-base.sh
skill_validate_input 427          # Lookup task, extract TASK_TYPE, PROJECT_NAME, etc.
skill_preflight_update 427 "research" "$session_id"  # Status -> researching
skill_create_postflight_marker 427 "$PROJECT_NAME" "$session_id" "skill-researcher" "research"
```

**Skill Step 4: Prepare Delegation Context**

```json
{
  "session_id": "sess_1736700000_abc123",
  "delegation_depth": 1,
  "delegation_path": ["orchestrator", "research", "skill-researcher"],
  "timeout": 3600,
  "task_context": {
    "task_number": 427,
    "task_name": "document_command_skill_subagent_framework",
    "description": "Systematically document the framework for using commands, skills, and subagents in conjunction.",
    "task_type": "meta"
  },
  "focus_prompt": null
}
```

**Skill Step 5: Invoke Subagent**

The skill invokes `general-research-agent` via the Agent tool.

### Step 4: Agent Executes Research

The agent (`general-research-agent.md`) receives the delegation context.

**Agent Stage 1: Parse Delegation Context**

Extract:
- task_number = 427
- task_name = "document_command_skill_subagent_framework"
- language = "meta"
- session_id = "sess_1736700000_abc123"

**Agent Stage 2: Determine Search Strategy**

Based on language = "meta":
- Primary: Context files + existing skills
- Secondary: WebSearch for Claude docs

**Agent Stage 3: Execute Searches**

```
Step 1: Codebase Exploration
- Glob(".claude/skills/**/SKILL.md") -> 9 skills found
- Glob(".claude/agents/*.md") -> 6 agents found
- Glob(".claude/commands/*.md") -> 9 commands found
- Read key files to understand patterns

Step 2: Context File Review
- Read .claude/context/templates/thin-wrapper-skill.md
- Read .claude/context/formats/subagent-return.md
- Read .claude/context/orchestration/orchestration-core.md

Step 3: Synthesize Findings
- 8 key patterns identified
- 5 documentation gaps found
- 4 recommendations formed
```

**Agent Stage 4: Generate Output**

Create research report following `report-format.md`:

```markdown
# Research Report: Task #427

**Task**: 427 - Document command, skill, and subagent framework
**Date**: 2026-01-12
**Focus**: Framework documentation

## Summary
This research analyzed the existing command, skill, and subagent
architecture. Found 8 key patterns, 5 documentation gaps, and
formed 4 recommendations.

## Findings
### 1. Current Architecture: Three-Layer Delegation Pattern
...

### 2. Component Relationships
...

## Recommendations
1. Create Component Selection Guide
2. Create Skill Creation Guide
...
```

**Agent Stage 5: Create Artifact**

```bash
mkdir -p specs/427_document_command_skill_subagent_framework/reports/
write 01_research-findings.md
```

**Agent Stage 6: Write Metadata File**

The agent writes `.return-meta.json` (not inline JSON return):

```json
{
  "status": "researched",
  "summary": "Research completed with 8 key findings on the three-layer architecture.",
  "artifacts": [
    {
      "type": "research",
      "path": "specs/427_document_command_skill_subagent_framework/reports/01_research-findings.md",
      "summary": "Research report with 8 findings and 4 recommendations"
    }
  ],
  "metadata": {
    "session_id": "sess_1736700000_abc123",
    "agent_type": "general-research-agent"
  }
}
```

### Step 5: Return Flow (Skill Postflight)

**Agent -> Skill Postflight** (`skill-base.sh` functions)

The skill reads the metadata file and runs postflight operations:

```bash
skill_read_metadata "$PADDED_NUM" "$PROJECT_NAME"     # Read .return-meta.json
skill_validate_artifact "$SUBAGENT_STATUS" "$ARTIFACT_PATH" "research"
skill_postflight_update 427 "research" "$session_id" "$SUBAGENT_STATUS"  # Status -> researched
skill_link_artifacts 427 "$ARTIFACT_PATH" "research" "$ARTIFACT_SUMMARY" '**Research**' '**Plan**'
skill_cleanup "$PADDED_NUM" "$PROJECT_NAME"            # Remove marker and metadata files
```

**Skill -> Command Gate Out** (`command-gate-out.sh`)

The command runs the gate-out checkpoint:

```bash
bash .claude/scripts/command-gate-out.sh 427 "research" "$SESSION_ID"
# Validates artifacts, applies defensive status correction if needed
```

**Command -> Git Commit**

```bash
git add -A && git commit -m "task 427: complete research\n\nSession: sess_..."
```

**User Sees:**
```
Research completed for Task #427

Report: specs/427_document.../reports/01_research-findings.md

Status: [RESEARCHED]
Next: /plan 427
```

---

## Key Decision Points

### Routing Decision

```
Input: /research 427 (task_type = "meta")

command-route-skill.sh resolves:
  source .claude/scripts/command-route-skill.sh "research" "meta" "skill-researcher"
  # Checks extension manifests for task_type-specific routing
  # Falls back to default: skill-researcher

Decision tree:
  Is task_type an extension type with custom routing? NO
  -> Use default: skill-researcher
```

If task 427 had a task type provided by an extension (e.g., `task_type: "python"`), the flow would route to the extension's skill:
```
command -> command-route-skill.sh -> skill-python-research -> python-research-agent
```

### Context Loading Decision

```
Agent: general-research-agent
Task type: "meta"

Context loading from index.json (4-tier progressive disclosure):
  Always load (tier 1):
    - repo/project-overview.md
    - patterns/anti-stop-patterns.md

  Task-type-specific (meta, tier 2-3):
    - meta/meta-guide.md
    - architecture/component-checklist.md
    - reference/skill-agent-mapping.md
    - (other entries matching task_type "meta" in index.json)

  Agent-specific:
    - formats/report-format.md (research agent context)
    - formats/return-metadata-file.md
```

---

## Artifact Locations

After `/research 427` completes:

```
specs/
├── state.json                 # Updated: task 427 status = "researched"
├── TODO.md                    # Updated: task 427 [RESEARCHED] with link
└── 427_document_command_skill_subagent_framework/
    └── reports/
        └── 01_research-findings.md    # Created: research report
```

---

## Error Scenarios

### Scenario A: Task Not Found

If user runs `/research 999` but task 999 does not exist:

```
command-gate-in.sh:
  Lookup task 999 in state.json -> NOT FOUND
  Aborts with: "Task 999 not found in state.json"

User sees:
  Error: Task 999 not found. Check task exists with /task --sync
```

### Scenario B: Network Error During Research

If WebSearch fails during research:

```
Agent Stage 3:
  WebSearch request fails -> network timeout

Agent continues with fallback:
  Use codebase-only patterns
  Note limitation in report

Return:
{
  "status": "partial",
  "summary": "Found 4 codebase patterns but WebSearch failed. Report contains local findings with suggested follow-up.",
  "errors": [{
    "type": "network",
    "message": "WebSearch request failed: connection timeout",
    "recoverable": true,
    "recommendation": "Retry research or proceed with codebase-only findings"
  }]
}
```

### Scenario C: Extension Task Type Routing

If user runs `/research 259` where task 259 has `task_type: "python"` (with the python extension loaded):

```
Orchestrator Stage 2:
  Lookup task 259 -> task_type = "python"

Orchestrator Stage 3:
  Routing: python -> skill-python-research

Flow:
  orchestrator -> skill-python-research -> python-research-agent

Agent uses:
  - WebSearch for library documentation
  - WebFetch for API references
  - Read for codebase exploration
  - Python-specific context files
```

---

## Session Tracking

The session_id flows through all layers:

```
command-gate-in.sh generates: session_id = "sess_1736700000_abc123"
         |
         v
Command passes session_id to skill via Skill tool args
         |
         v
Skill passes session_id in delegation context to agent
         |
         v
Agent includes session_id in .return-meta.json
         |
         v
command-gate-out.sh and git commit reference session_id
         |
         v
Session tracked for debugging/auditing
```

---

## Summary

This example demonstrated:

1. **Command Layer**: User entry point; shared gate scripts handle parsing, validation, and routing
2. **Skill Layer**: Shared lifecycle via `skill-base.sh`; validates, delegates to agent, runs postflight
3. **Agent Layer**: Executes work, creates artifacts, writes `.return-meta.json` metadata file
4. **Return Flow**: Skill reads metadata file, runs postflight (status update, artifact linking, git commit)
5. **Gate Out**: Command validates artifacts, applies defensive status correction
6. **Status Updates**: Atomic state.json + TODO.md updates via shared scripts

The three-layer architecture provides:
- Clean separation of concerns
- Shared infrastructure via gate scripts and skill-base.sh (~60% code reduction)
- Task-type-based routing via `command-route-skill.sh`
- File-based metadata exchange (`.return-meta.json`)
- Resume support via partial status and postflight markers

---

## Related Documentation

- [Component Selection](../guides/component-selection.md) - When to create each component
- [Creating Skills](../guides/creating-skills.md) - Skill creation guide
- [Creating Agents](../guides/creating-agents.md) - Agent creation guide
- `.claude/context/formats/subagent-return.md` - Return format schema

---

**Document Version**: 2.0 (Updated 2026-05-22 for shared infrastructure refactor)
**Created**: 2026-01-12
**Maintained By**: Project Development Team
