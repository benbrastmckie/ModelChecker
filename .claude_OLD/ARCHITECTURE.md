# Claude Agent System Architecture

[Back to ModelChecker](../README.md) | [Docs](docs/README.md) | [Context](context/README.md) | [CLAUDE.md](CLAUDE.md)

## Table of Contents

1. [Overview](#overview)
2. [Architecture Principles](#architecture-principles)
3. [Component Hierarchy](#component-hierarchy)
4. [Command Workflow](#command-workflow)
5. [Skill Details](#skill-details)
6. [State Management](#state-management)
7. [Language-Based Routing](#language-based-routing)
8. [Error Handling](#error-handling)
9. [Python/Z3 Integration](#pythonz3-integration)
10. [Extensibility](#extensibility)
11. [Related Documentation](#related-documentation)

---

## Overview

The `.claude/` system is a task management and automation framework for Python/Z3 semantic theory development. It provides structured workflows for research, planning, and implementation with language-based routing.

### Key Capabilities

- **Task Lifecycle**: Create, research, plan, implement, and archive tasks
- **Atomic State Sync**: TODO.md and state.json stay synchronized
- **Resume Support**: Interrupted implementations continue from last phase
- **Language Routing**: Python tasks route to Z3-specialized skills
- **Automatic Commits**: Scoped git commits after each stage
- **Error Tracking**: Persistent error logging with fix effectiveness analysis

### Directory Structure

```
.claude/
├── ARCHITECTURE.md                 # This file
├── CLAUDE.md                       # Quick reference entry point
├── commands/                       # Slash commands (9)
├── context/                        # Domain knowledge (95 files)
│   ├── core/                       # Reusable patterns (41 files)
│   └── project/                    # ModelChecker-specific (54 files)
├── docs/                           # Documentation
├── rules/                          # Automatic behaviors (6)
├── skills/                         # Specialized agents (8)
└── specs/                          # Task artifacts and state
```

---

## Architecture Principles

### 1. Delegation Safety

All delegation follows strict safety patterns:

| Pattern | Purpose |
|---------|---------|
| Session ID Tracking | Unique ID for each delegation |
| Depth Limits | Maximum 3 delegation levels |
| Cycle Detection | Check path before routing |
| Timeout Enforcement | Default 3600s timeout |
| Return Validation | Validate against standard format |

### 2. Standardized Returns

All skills return consistent JSON:

```json
{
  "status": "completed|failed|partial|blocked",
  "summary": "Brief 2-5 sentence summary",
  "artifacts": [{"path": "...", "type": "..."}],
  "metadata": {
    "session_id": "...",
    "duration_seconds": 123,
    "agent_type": "...",
    "delegation_depth": 1
  },
  "errors": [],
  "next_steps": "..."
}
```

### 3. Atomic State Updates

Status changes synchronize across files atomically:

```
Two-Phase Commit:
1. Prepare all updates in memory
2. Write state.json (machine state)
3. Write TODO.md (user-facing)
4. Rollback all on any failure
```

### 4. Fail-Safe Commits

Git commit failures are logged but do NOT block operations. Task progress is preserved.

---

## Component Hierarchy

```
Level 0: Orchestrator
    │
    ├── Level 1: Commands (/task, /research, /plan, /implement, ...)
    │       │
    │       └── Level 2: Skills (skill-researcher, skill-planner, ...)
    │               │
    │               └── Level 3: Context Files (domain knowledge)
```

### Level 0: Orchestrator

**Skill**: [skill-orchestrator](skills/skill-orchestrator/SKILL.md)

Central coordination responsible for:
- Language-based routing decisions
- Delegation registry management
- Cycle detection and depth enforcement
- Return validation

### Level 1: Commands

**Directory**: [commands/](commands/)

| Command | Purpose |
|---------|---------|
| [/task](commands/task.md) | Create, recover, divide, sync, abandon tasks |
| [/research](commands/research.md) | Conduct research, create reports |
| [/plan](commands/plan.md) | Create implementation plans |
| [/implement](commands/implement.md) | Execute with resume support |
| [/revise](commands/revise.md) | Create new plan version |
| [/review](commands/review.md) | Analyze codebase |
| [/errors](commands/errors.md) | Analyze errors, create fix plans |
| [/todo](commands/todo.md) | Archive completed tasks |
| [/meta](commands/meta.md) | Interactive system builder |

### Level 2: Skills

**Directory**: [skills/](skills/)

**Core Skills**:
| Skill | Purpose |
|-------|---------|
| [skill-orchestrator](skills/skill-orchestrator/SKILL.md) | Central routing and coordination |
| [skill-status-sync](skills/skill-status-sync/SKILL.md) | Atomic multi-file updates |
| [skill-git-workflow](skills/skill-git-workflow/SKILL.md) | Scoped git commits |

**Research Skills**:
| Skill | Purpose |
|-------|---------|
| [skill-researcher](skills/skill-researcher/SKILL.md) | General web/codebase research |
| [skill-python-research](skills/skill-python-research/SKILL.md) | Z3 API and pattern research |

**Implementation Skills**:
| Skill | Purpose |
|-------|---------|
| [skill-planner](skills/skill-planner/SKILL.md) | Create phased implementation plans |
| [skill-implementer](skills/skill-implementer/SKILL.md) | General implementation |
| [skill-theory-implementation](skills/skill-theory-implementation/SKILL.md) | TDD for semantic theories |

### Level 3: Context

**Directory**: [context/](context/README.md)

- **core/**: Reusable patterns (orchestration, formats, standards, workflows)
- **project/**: ModelChecker-specific (modelchecker, logic, lean4, math)

---

## Command Workflow

All task-based commands follow this pattern:

```
┌─────────────────────────────────────────────────────────────────┐
│                      Command Execution                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. Parse Arguments                                             │
│     Extract task number and options from $ARGUMENTS             │
│                              │                                  │
│                              ▼                                  │
│  2. Preflight                                                   │
│     Validate task exists, status allows operation               │
│     Update status to "in progress" variant                      │
│                              │                                  │
│                              ▼                                  │
│  3. Check Language                                              │
│     Read task language from state.json                          │
│     Determine target skill                                      │
│                              │                                  │
│                              ▼                                  │
│  4. Invoke Skill                                                │
│     Delegate to skill with session tracking                     │
│     Wait for return (with timeout)                              │
│                              │                                  │
│                              ▼                                  │
│  5. Process Results                                             │
│     Validate return format                                      │
│     Extract artifacts                                           │
│                              │                                  │
│                              ▼                                  │
│  6. Postflight                                                  │
│     Update status atomically                                    │
│     Create git commit                                           │
│                              │                                  │
│                              ▼                                  │
│  7. Return                                                      │
│     Report summary to user                                      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Skill Details

### skill-python-research

Specialized for Python/Z3 development:

**Tools**: WebSearch, WebFetch, Read, Grep, Glob

**Research Targets**:
- Z3 API patterns and solver strategies
- Existing codebase patterns
- Theory implementation approaches
- Testing strategies

### skill-theory-implementation

TDD workflow for semantic theories:

**Tools**: Read, Write, Edit, Bash(pytest), Bash(python)

**Workflow**:
1. Load implementation plan
2. Write failing tests first (TDD)
3. Implement minimal code to pass
4. Refactor while tests pass
5. Verify with full test suite

### skill-status-sync

Atomic multi-file status updates:

**Files Updated**:
- `specs/TODO.md` - Status marker
- `specs/state.json` - Status field
- Plan files - Phase markers

**Pattern**: Two-phase commit with rollback on failure

---

## State Management

### Dual-File System

| File | Purpose | Format |
|------|---------|--------|
| [specs/TODO.md](specs/TODO.md) | User-facing task list | Markdown |
| [specs/state.json](specs/state.json) | Machine-readable state | JSON |
| [specs/errors.json](specs/errors.json) | Error tracking | JSON |

### Status Transitions

```
[NOT STARTED] ──► [RESEARCHING] ──► [RESEARCHED]
                                         │
                                         ▼
                               [PLANNING] ──► [PLANNED]
                                                  │
                                                  ▼
                                      [IMPLEMENTING] ──► [COMPLETED]
                                             │
                                             ▼
                                        [PARTIAL] (enables resume)

Any state ──► [BLOCKED] (with reason)
Any state ──► [ABANDONED] (moves to archive)
```

### Task Artifact Structure

```
specs/{N}_{SLUG}/
├── reports/
│   └── research-001.md         # Research findings
├── plans/
│   └── implementation-001.md   # Phased implementation plan
└── summaries/
    └── implementation-summary-{DATE}.md
```

---

## Language-Based Routing

The orchestrator routes tasks to skills based on the Language field:

| Language | Research Skill | Implementation Skill |
|----------|---------------|---------------------|
| `python` | skill-python-research | skill-theory-implementation |
| `general` | skill-researcher | skill-implementer |
| `meta` | skill-researcher | skill-implementer |

### Language Detection

For `/task` command, language is auto-detected from keywords:

| Keywords | Language |
|----------|----------|
| Z3, pytest, theory, semantic | python |
| agent, command, skill, meta | meta |
| (default) | general |

---

## Error Handling

### Error Types

| Type | Description |
|------|-------------|
| `tool_failure` | External tool failed |
| `status_sync_failure` | TODO.md/state.json desync |
| `test_failure` | Tests failed during implementation |
| `import_error` | Python import failed |
| `z3_timeout` | Z3 solver timed out |
| `git_commit_failure` | Git operation failed |
| `timeout` | Operation exceeded timeout |

### Recovery Patterns

**Test Failure**:
1. Capture test output
2. Log to errors.json
3. Keep task [IMPLEMENTING]
4. Report failure with context

**Timeout/Interruption**:
1. Mark current phase [PARTIAL]
2. Commit partial progress
3. Next `/implement` resumes from partial phase

**State Sync Failure**:
1. Use git blame to determine latest
2. Sync to latest version
3. Log resolution

---

## Python/Z3 Integration

### Testing Commands

```bash
# Run all tests
PYTHONPATH=Code/src pytest Code/tests/ -v

# Run specific theory tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/logos/tests/ -v

# Run with coverage
pytest --cov=model_checker --cov-report=term-missing
```

### Theory Development Pattern

```python
# 1. semantic.py - Define semantic defaults
class MyTheorySemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {...}

# 2. operators.py - Register operators
def get_operators():
    return OperatorCollection([...])

# 3. examples.py - Create test examples
examples = [BuildExample(...), ...]

# 4. iterate.py - Add iteration support
class MyTheoryIterator(BaseModelIterator):
    ...
```

### Z3 Best Practices

- Use context managers for solver scope
- Minimize constraint count
- Use incremental solving where possible
- Add timeouts for complex satisfiability checks
- Prefer simpler constraint forms

---

## Extensibility

The architecture supports extension through:

| Component | Location | How to Add |
|-----------|----------|------------|
| Commands | `commands/` | Create `{name}.md` with frontmatter |
| Skills | `skills/` | Create `skill-{name}/SKILL.md` |
| Context | `context/project/` | Add domain-specific `.md` files |
| Rules | `rules/` | Create `{name}.md` with scope patterns |

### Adding a New Command

1. Create `commands/{name}.md` with frontmatter:
   ```yaml
   ---
   description: What the command does
   allowed-tools: Read, Write, Edit, Bash(git:*)
   argument-hint: ARGS
   model: claude-opus-4-5-20251101
   ---
   ```
2. Define execution steps
3. Document in [docs/README.md](docs/README.md)

### Adding a New Skill

1. Create `skills/skill-{name}/SKILL.md` with frontmatter:
   ```yaml
   ---
   name: skill-{name}
   description: What the skill does
   allowed-tools: Tool1, Tool2
   context: fork
   ---
   ```
2. Define trigger conditions and workflow
3. Update orchestrator routing if needed

---

## Related Documentation

### Quick Reference
- [CLAUDE.md](CLAUDE.md) - Entry point and quick reference

### Detailed Documentation
- [docs/README.md](docs/README.md) - Complete documentation hub
- [context/README.md](context/README.md) - Context organization

### Project Documentation
- [ModelChecker README](../README.md) - Main project documentation
- [Code/docs/](../Code/docs/) - Technical development standards
- [Code/docs/core/TESTING_GUIDE.md](../Code/docs/core/TESTING_GUIDE.md) - TDD requirements

---

[Back to ModelChecker](../README.md) | [Docs](docs/README.md) | [Context](context/README.md) | [CLAUDE.md](CLAUDE.md)
