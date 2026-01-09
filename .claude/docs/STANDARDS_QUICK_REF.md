# Standards Quick Reference

Quick reference for common standards in the ProofChecker .opencode system.

## Command Argument Handling

**File**: `.claude/context/core/standards/command-argument-handling.md`

### Task-Based Commands

```markdown
**Task Input (required):** $ARGUMENTS (task number; e.g., `/research 258`)
```

**Pattern**:
1. OpenCode sets `$ARGUMENTS = "258"`
2. Orchestrator extracts task_number from $ARGUMENTS
3. Orchestrator validates task exists in TODO.md
4. Orchestrator formats prompt as `"Task: 258"`
5. Subagent receives `"Task: 258"`

**Error Handling**:
- Missing: "Error: Task number required. Usage: /{command} TASK_NUMBER"
- Invalid: "Error: Task number must be an integer. Got: {input}"
- Not found: "Error: Task {N} not found in TODO.md"

### Direct Commands

```markdown
**Task Input (optional):** $ARGUMENTS (user input; e.g., `/meta "options"`)
```

**Pattern**:
1. OpenCode sets `$ARGUMENTS = "options"` (or empty)
2. Orchestrator reads $ARGUMENTS as-is
3. Orchestrator passes $ARGUMENTS to subagent
4. Subagent receives `"options"` (or empty)

## Delegation Standard

**File**: `.claude/context/core/standards/delegation.md`

### Return Format

```json
{
  "status": "completed|partial|failed|blocked",
  "summary": "Brief 2-5 sentence summary (<100 tokens)",
  "artifacts": [
    {
      "type": "research_report|plan|code|test|analysis",
      "path": ".claude/specs/{task_dir}/{artifact}.md",
      "description": "Brief description"
    }
  ],
  "metadata": {
    "session_id": "sess_...",
    "duration_seconds": 123,
    "agent_type": "researcher|planner|implementer",
    "delegation_depth": 1,
    "delegation_path": ["orchestrator", "research", "researcher"]
  },
  "errors": [],
  "next_steps": "What to do next (if partial/blocked)"
}
```

### Status Values

- **completed**: Work finished successfully, all artifacts created
- **partial**: Work partially done, can be resumed
- **failed**: Work failed, cannot proceed
- **blocked**: Work blocked by external dependency

## State Management

**File**: `.claude/context/core/system/state-management.md`

### Status Markers

```markdown
**Status**: [RESEARCHING] → [RESEARCHED]
**Status**: [PLANNING] → [PLANNED]
**Status**: [IMPLEMENTING] → [IMPLEMENTED]
**Status**: [REVIEWING] → [REVIEWED]
```

### State Schema

```json
{
  "task_number": 258,
  "title": "Task title",
  "status": "RESEARCHED",
  "language": "lean",
  "created": "2026-01-03T10:00:00Z",
  "updated": "2026-01-03T11:00:00Z",
  "artifacts": [
    {
      "type": "research_report",
      "path": ".claude/specs/258_task_title/reports/research-001.md",
      "created": "2026-01-03T11:00:00Z"
    }
  ]
}
```

## Routing Logic

**File**: `.claude/context/core/system/routing-logic.md`

### Language Extraction Priority

1. **Priority 1**: Project state.json (task-specific)
2. **Priority 2**: TODO.md task entry (**Language** field)
3. **Priority 3**: Default "general" (fallback)

### Agent Mapping

```yaml
routing:
  language_based: true
  lean: lean-research-agent
  default: researcher
```

**Logic**:
- If language == "lean" → route to lean-research-agent
- Else → route to researcher

### Validation

- Agent file must exist at `.claude/agent/subagents/{agent}.md`
- Lean tasks must route to lean-* agents
- Non-lean tasks must NOT route to lean-* agents

## Validation Rules

**File**: `.claude/context/core/system/validation-rules.md`

### Return Validation Steps

1. **JSON Structure**: Must be valid JSON
2. **Required Fields**: status, summary, artifacts, metadata, session_id
3. **Status Enum**: Must be completed|partial|failed|blocked
4. **Session ID**: Must match expected value
5. **Summary Length**: <100 tokens (~400 characters)

### Artifact Validation (CRITICAL)

**Only if status == "completed"**:

1. **Non-Empty Array**: artifacts.length > 0
2. **Files Exist**: All artifact paths exist on disk
3. **Non-Empty Files**: All artifact files have size > 0 bytes

**Prevents "phantom research"**: status=completed but no artifacts created

## Task Format

**File**: `.claude/context/core/standards/tasks.md`

### Task Entry Format

```markdown
### 258. Task title

**Status**: [RESEARCHED]  
**Language**: lean  
**Priority**: high  
**Created**: 2026-01-03  
**Updated**: 2026-01-03

**Description**: Brief description of the task

**Acceptance Criteria**:
- [ ] Criterion 1
- [ ] Criterion 2

**Dependencies**: None

**Notes**: Additional context
```

### Required Fields

- Task number (### N.)
- Title
- **Status** marker
- **Language** field (for language-based routing)
- **Description**
- **Acceptance Criteria**

## Context Loading

**File**: `.claude/context/index.md`

### Loading Strategy

```yaml
context_loading:
  strategy: lazy
  index: ".claude/context/index.md"
  required:
    - "core/standards/delegation.md"
    - "core/system/state-management.md"
    - "core/standards/command-argument-handling.md"
  optional:
    - "project/lean4/tools/leansearch-api.md"
  max_context_size: 50000
```

### Budget Allocation

- **Orchestrator**: <10% context window (~10KB)
- **Commands**: 10-20% context window (~20-40KB)
- **Agents**: 60-80% context window (~120-160KB)

### Loading Patterns

**Orchestrator** (Stage 1-3):
- Load NO context files during routing
- Make routing decisions with command frontmatter only

**Agents** (Stage 4+):
- Load only files needed for specific workflow
- Use index.md to identify required files
- Load context on-demand via @.claude/context/{category}/{file}

## Git Commits

**File**: `.claude/context/core/system/git-commits.md`

### Commit Message Format

```
{action} {scope}: {brief description}

{detailed description}

{list of changes}

{metadata}
```

### Examples

```
Implement research for Task 258

Conducted research on Lean 4 proof automation using LeanSearch API.

Changes:
- Created research report with 5 key findings
- Identified 3 relevant Mathlib theorems
- Documented proof strategies

Artifacts:
- .claude/specs/258_task/reports/research-001.md

Status: [RESEARCHING] → [RESEARCHED]
```

### Commit Patterns

- **Research**: "Conduct research for Task {N}"
- **Planning**: "Create implementation plan for Task {N}"
- **Implementation**: "Implement Task {N}"
- **Review**: "Review {scope}"
- **Fix**: "Fix {issue} in Task {N}"

## Artifact Management

**File**: `.claude/context/core/system/artifact-management.md`

### Artifact Naming

```
.claude/specs/{task_number}_{task_title}/
  reports/
    research-001.md
    research-002.md
  plans/
    implementation-001.md
  summaries/
    implementation-summary-20260103.md
  state.json
```

### Artifact Types

- **research_report**: Research findings and analysis
- **plan**: Implementation plan with phases
- **code**: Source code files
- **test**: Test files
- **analysis**: Analysis reports
- **summary**: Summary documents

### Lazy Directory Creation

Don't create directories until artifacts are ready to be written.

**Good**:
```bash
# Create directory only when writing artifact
mkdir -p .claude/specs/258_task/reports
echo "content" > .claude/specs/258_task/reports/research-001.md
```

**Bad**:
```bash
# Don't create empty directories
mkdir -p .claude/specs/258_task/reports
# ... later, maybe write artifact
```

## Quick Navigation

| Need | File |
|------|------|
| Command Arguments | `core/standards/command-argument-handling.md` |
| Delegation | `core/standards/delegation.md` |
| State Management | `core/system/state-management.md` |
| Routing | `core/system/routing-logic.md` |
| Validation | `core/system/validation-rules.md` |
| Task Format | `core/standards/tasks.md` |
| Plan Format | `core/standards/plan.md` |
| Artifact Management | `core/system/artifact-management.md` |
| Git Commits | `core/system/git-commits.md` |
| Context Loading | `context/index.md` |
| Lean Style | `project/lean4/standards/lean4-style-guide.md` |
| Proof Conventions | `project/logic/standards/proof-conventions.md` |

## Common Workflows

### Creating a New Command

1. Determine command type (task-based or direct)
2. Choose routing strategy (language-based or direct)
3. Create command file with frontmatter
4. Document $ARGUMENTS handling
5. Configure routing
6. Define context loading
7. Document workflow
8. Add error handling
9. Add usage examples
10. Test thoroughly

**See**: `.claude/docs/guides/creating-commands.md`

### Conducting Research

1. User: `/research 258`
2. Orchestrator: Parse task_number from $ARGUMENTS
3. Orchestrator: Extract language from task
4. Orchestrator: Route to appropriate agent
5. Agent: Conduct research
6. Agent: Create research report
7. Agent: Update status to [RESEARCHED]
8. Agent: Commit changes
9. Orchestrator: Validate return
10. Orchestrator: Relay result to user

### Creating Implementation Plan

1. User: `/plan 258`
2. Orchestrator: Parse task_number from $ARGUMENTS
3. Orchestrator: Route to planner (direct routing)
4. Planner: Create implementation plan
5. Planner: Update status to [PLANNED]
6. Planner: Commit changes
7. Orchestrator: Validate return
8. Orchestrator: Relay result to user

### Implementing Task

1. User: `/implement 258`
2. Orchestrator: Parse task_number from $ARGUMENTS
3. Orchestrator: Extract language from task
4. Orchestrator: Route to appropriate agent
5. Agent: Execute implementation
6. Agent: Create code and test artifacts
7. Agent: Update status to [IMPLEMENTED]
8. Agent: Commit changes
9. Orchestrator: Validate return
10. Orchestrator: Relay result to user

## Error Patterns

### Missing Required Argument

```
Error: Task number required for /research command

Usage: /research <task_number> [prompt]

Example: /research 258
```

### Invalid Argument Format

```
Error: Task number must be an integer. Got: abc

Usage: /research TASK_NUMBER

Example: /research 258
```

### Task Not Found

```
Error: Task 999 not found in TODO.md

Please verify the task number exists in .claude/specs/TODO.md

You can list all tasks with: grep "^###" .claude/specs/TODO.md
```

### Phantom Research

```
Error: Agent returned 'completed' status but created no artifacts

Recommendation: Verify researcher creates artifacts before updating status
```

### Routing Mismatch

```
Error: Lean task must route to lean-* agent

Routing validation failed: language=lean but agent=researcher
```

## Best Practices

### 1. Always Reference Standards

Don't duplicate logic. Reference standard files:
- `@.claude/context/core/standards/command-argument-handling.md`
- `@.claude/context/core/system/routing-logic.md`
- `@.claude/context/core/system/validation-rules.md`

### 2. Validate Early

Validate arguments in Stage 1 (orchestrator). Don't pass invalid data to subagents.

### 3. Keep Context Minimal

Only load context files actually needed. Follow budget allocation.

### 4. Document Thoroughly

Include clear descriptions, usage examples, error messages, and See Also references.

### 5. Test Edge Cases

Test missing arguments, invalid formats, non-existent tasks, empty inputs.

### 6. Follow Naming Conventions

- Commands: lowercase-with-hyphens
- Agents: lowercase-with-hyphens
- Files: match command/agent name exactly

### 7. Use Standard Patterns

Follow existing commands as templates. Don't reinvent the wheel.

### 8. Provide Clear Errors

Error messages should explain what went wrong, show correct usage, and provide examples.

### 9. Version Your Changes

Update `updated:` field in frontmatter. Document changes in commit messages.

### 10. Prevent Phantom Research

Always validate artifacts exist and are non-empty when status=completed.

## See Also

- **Creating Commands Guide**: `.claude/docs/guides/creating-commands.md`
- **Command Template**: `.claude/context/core/templates/command-template.md`
- **Orchestrator**: `.claude/agent/orchestrator.md`
- **Context Index**: `.claude/context/index.md`
- **Architecture**: `.claude/ARCHITECTURE.md`
