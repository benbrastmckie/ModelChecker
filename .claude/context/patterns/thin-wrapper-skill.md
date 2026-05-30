# Thin Wrapper Skill Pattern

**Created**: 2026-01-19
**Purpose**: Quick reference for the thin wrapper skill pattern
**Audience**: /meta agent, skill developers

---

## Overview

Thin wrapper skills are the standard pattern for workflow skills. They:
1. Validate inputs
2. Prepare delegation context
3. Invoke a subagent via Agent tool
4. Validate and propagate the return

They do NOT:
- Load heavy context (subagent does this)
- Execute business logic (subagent does this)
- Handle complex error recovery (subagent does this)

---

## Frontmatter

```yaml
---
name: skill-{name}
description: {One-line description}
allowed-tools: Agent
context: fork
agent: {agent-name}
---
```

**Key fields**:
- `allowed-tools: Agent` - Only tool needed for delegation
- `context: fork` - Do NOT load context eagerly; subagent loads context
- `agent: {name}` - Target subagent to invoke

---

## Execution Pattern

### 1. Input Validation

Validate task exists and arguments are correct:

```bash
task_data=$(jq -r --arg num "$task_number" \
  '.active_projects[] | select(.project_number == ($num | tonumber))' \
  specs/state.json)

if [ -z "$task_data" ]; then
  return error "Task $task_number not found"
fi
```

### 2. Context Preparation

Generate session_id and prepare delegation context:

```bash
session_id="sess_$(date +%s)_$(od -An -N3 -tx1 /dev/urandom | tr -d ' ')"
```

```json
{
  "session_id": "sess_{timestamp}_{random}",
  "delegation_depth": {current_depth + 1},
  "delegation_path": [..., "skill-{name}"],
  "timeout": {timeout_seconds},
  "task_context": {
    "task_number": N,
    "task_name": "{slug}",
    "description": "{description}",
    "task_type": "{task_type}"
  }
}
```

### 3. Invoke Subagent

**CRITICAL**: Use the **Agent** tool to spawn the subagent.

```
Tool: Agent (NOT Skill, NOT Plan)
Parameters:
  - subagent_type: "{agent-name}" (from frontmatter)
  - prompt: [Include task_context, delegation_context]
  - description: "Execute {operation} for task {N}"
```

**DO NOT** use `Skill({agent-name})` - this will FAIL.
Agents live in `.claude/agents/`, not `.claude/skills/`.

### 3b. Self-Execution Fallback

If the skill executor performed work inline (without spawning a subagent via Agent tool), it MUST write a `.return-meta.json` file before proceeding to postflight. This ensures postflight stages can read metadata regardless of execution path.

**Why this is needed**: The postflight stages (status update, artifact linking, git commit) depend on reading `.return-meta.json`. When work is done by a subagent, the subagent writes this file. When work is done inline, the skill executor must write it manually using the schema from `return-metadata-file.md`.

**Template** (add after Stage 5 / subagent invocation in each skill):
```markdown
### Stage 5b: Self-Execution Fallback

**CRITICAL**: If you performed the work above WITHOUT using the Agent tool (i.e., you read files,
wrote artifacts, or updated metadata directly instead of spawning a subagent), you MUST write a
`.return-meta.json` file now before proceeding to postflight. Use the schema from
`return-metadata-file.md` with the appropriate status value for this operation.

If you DID use the Agent tool (Stage 5), skip this stage -- the subagent already wrote the metadata.
```

### 4. Return Validation

Validate subagent return:
- Return is valid JSON
- Status is valid enum value
- Summary is non-empty and <100 tokens
- Artifacts array is present
- Session ID matches expected

### 5. Return Propagation

Return validated result to caller without modification.

---

## Example

```markdown
---
name: skill-{extension}-research
description: Research {extension} patterns and conventions.
allowed-tools: Agent
context: fork
agent: {extension}-research-agent
---

# {Extension} Research Skill

Specialized research for {extension} tasks.

## Trigger Conditions
- Task type is "{extension}"
- Research involves {extension}-specific patterns and tools

## Execution

### 1. Input Validation
Extract task_number. Validate task exists.

### 2. Context Preparation
Generate session_id. Prepare delegation context.

### 3. Invoke Subagent
Use Agent tool with subagent_type: {extension}-research-agent

### 4. Return Validation
Validate return matches subagent-return.md schema.

### 5. Return Propagation
Return validated result to caller.
```

---

## Two Delegation Sub-Patterns

Thin wrapper skills use one of two delegation approaches. The choice depends on whether structured context injection is needed.

### Pattern A: Core skill pattern (explicit `subagent_type`, no `context: fork`)

Used by: skill-researcher, skill-planner, skill-implementer, skill-reviser, skill-spawn, and other core workflow skills.

```yaml
---
name: skill-implementer
description: Execute implementation tasks.
allowed-tools: Agent, Bash, Edit, Read, Write
---
```

The skill body explicitly calls the Agent tool with `subagent_type`:
```
Tool: Agent
Parameters:
  subagent_type: "general-implementation-agent"
  prompt: [full structured context JSON: session_id, delegation_depth, memory_context, etc.]
```

**Why no `context: fork`**: Core skills have multi-stage postflight (status update, artifact linking, git commit). They inject structured context that requires knowing the exact agent. They do NOT use `context: fork` or `agent:` frontmatter.

---

### Pattern B: Extension skill pattern (`context: fork` + `agent:`, simpler delegation)

Used by: skill-lean-research, skill-present-research, and similar extension skills.

```yaml
---
name: skill-{ext}-research
description: Research {ext} patterns. Invoke for {ext} research tasks.
allowed-tools: Agent
context: fork
agent: {ext}-research-agent
---
```

The skill body passes simpler instructions to the agent without a full structured context JSON.

**Why `context: fork`**: Extension skills are thin wrappers with minimal postflight. The `context: fork` field prevents context files from being loaded into the skill's session, since the agent loads its own context.

**Note**: `context: fork` and `CLAUDE_CODE_FORK_SUBAGENT=1` are independent. See @.claude/context/patterns/fork-patterns.md for the full decision matrix and cache sharing mechanics.

---

## When NOT to Use This Pattern

Use direct execution instead when:
- Skill executes atomic operations (skill-status-sync)
- No subagent needed
- Work is trivial

Direct execution skills use:
```yaml
allowed-tools: Bash, Edit, Read
```

**Note**: Direct-execution skills do not need the Stage 5b self-execution fallback since they do not delegate to subagents and handle their own metadata directly.

### Extension Skills (Standard Pattern)

Extension skills follow the standard thin wrapper pattern, delegating to extension-provided agents. For example, an extension may provide `skill-{ext}-research` and `skill-{ext}-implementation` that delegate to `{ext}-research-agent` and `{ext}-implementation-agent` respectively.

---

## Postflight Boundary Restrictions

After the subagent returns, thin wrapper skills MUST NOT perform implementation work. See @.claude/context/standards/postflight-tool-restrictions.md for:
- Allowed tools (Read metadata, jq state updates, Edit TODO.md, git commit)
- Prohibited tools (Edit source files, build commands, MCP tools)
- MUST NOT section template to include in skills

---

## Related Documentation

- @.claude/context/templates/thin-wrapper-skill.md - Full template
- @.claude/context/patterns/skill-lifecycle.md - Complete skill lifecycle
- @.claude/context/formats/subagent-return.md - Return format
- @.claude/context/standards/postflight-tool-restrictions.md - Postflight boundary rules
- @.claude/docs/guides/creating-skills.md - Step-by-step guide
