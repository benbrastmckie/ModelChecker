# Claude Agent System Documentation

[Back to ModelChecker](../../README.md) | [Architecture](../ARCHITECTURE.md) | [Context](../context/README.md)

## Table of Contents

1. [Overview](#overview)
2. [Commands](#commands)
3. [Skills](#skills)
4. [Rules](#rules)
5. [Artifacts](#artifacts)
6. [State Management](#state-management)
7. [Git Workflow](#git-workflow)
8. [Guides](#guides)
9. [Templates](#templates)
10. [Related Documentation](#related-documentation)

---

## Overview

The `.claude/` directory contains a task management and automation system for ModelChecker development. It provides structured workflows for research, planning, and implementation with language-based routing for Python/Z3 development.

### Key Features

- **Task Lifecycle Management**: Create, research, plan, implement, and archive tasks
- **Language-Based Routing**: Python tasks route to Z3-specialized skills
- **Atomic State Sync**: TODO.md and state.json stay synchronized
- **Resume Support**: Interrupted implementations continue from where they stopped
- **Automatic Git Commits**: Scoped commits after each workflow stage

### Directory Structure

```
.claude/
├── ARCHITECTURE.md                 # System architecture overview
├── CLAUDE.md                       # Quick reference and entry point
├── commands/                       # Slash command definitions (9 commands)
├── context/                        # Domain knowledge and standards
│   ├── core/                       # Reusable patterns (orchestration, formats, standards)
│   └── project/                    # ModelChecker-specific context
├── docs/                           # This documentation directory
│   ├── README.md                   # This file - documentation hub
│   ├── guides/                     # How-to guides
│   ├── templates/                  # Reusable templates
│   └── architecture/               # Architecture analysis
├── rules/                          # Automatic behavior rules (6 rules)
├── skills/                         # Specialized skills (8 skills)
└── specs/                          # Task artifacts and state
    ├── TODO.md                     # User-facing task list
    ├── state.json                  # Machine-readable state
    ├── errors.json                 # Error tracking
    └── {N}_{SLUG}/                 # Task-specific artifacts
```

---

## Commands

Commands are user-invocable operations via `/command` syntax. Each command has a frontmatter defining its tools, arguments, and model.

| Command | Description | Arguments |
|---------|-------------|-----------|
| [/task](../commands/task.md) | Create, recover, divide, sync, or abandon tasks | `"description"` or `--recover N` or `--divide N` or `--sync` or `--abandon N` |
| [/research](../commands/research.md) | Conduct research and create reports | `TASK_NUMBER [FOCUS]` |
| [/plan](../commands/plan.md) | Create implementation plans from research | `TASK_NUMBER` |
| [/implement](../commands/implement.md) | Execute implementation with resume support | `TASK_NUMBER` |
| [/revise](../commands/revise.md) | Create new version of implementation plan | `TASK_NUMBER` |
| [/review](../commands/review.md) | Review code and create analysis reports | `[SCOPE]` |
| [/errors](../commands/errors.md) | Analyze errors and create fix plans | (reads errors.json) |
| [/todo](../commands/todo.md) | Archive completed and abandoned tasks | (no args) |
| [/meta](../commands/meta.md) | Interactive system builder for agent architectures | `[DOMAIN]` or `--analyze` or `--generate` |

### Typical Workflow

```
/task "Add new operator to logos theory"     # Create task #349
/research 349                                 # Research approaches
/plan 349                                     # Create implementation plan
/implement 349                                # Execute with TDD
```

---

## Skills

Skills are specialized agents invoked by commands or the orchestrator. They have defined tools, context handling, and return formats.

### Core Skills

| Skill | Purpose | Trigger |
|-------|---------|---------|
| [skill-orchestrator](../skills/skill-orchestrator/SKILL.md) | Central routing and coordination | Commands needing language-based routing |
| [skill-status-sync](../skills/skill-status-sync/SKILL.md) | Atomic multi-file status updates | Status changes in any command |
| [skill-git-workflow](../skills/skill-git-workflow/SKILL.md) | Scoped git commits | After task operations |

### Research Skills

| Skill | Purpose | When Used |
|-------|---------|-----------|
| [skill-researcher](../skills/skill-researcher/SKILL.md) | General web and codebase research | Non-Python research tasks |
| [skill-python-research](../skills/skill-python-research/SKILL.md) | Z3 API and pattern research | Python/Z3 research tasks |

### Implementation Skills

| Skill | Purpose | When Used |
|-------|---------|-----------|
| [skill-planner](../skills/skill-planner/SKILL.md) | Create phased implementation plans | `/plan` command |
| [skill-implementer](../skills/skill-implementer/SKILL.md) | Execute general implementations | Non-Python implementation |
| [skill-theory-implementation](../skills/skill-theory-implementation/SKILL.md) | TDD workflow for semantic theories | Python/Z3 implementation |

### Language-Based Routing

The orchestrator routes to skills based on task language:

| Language | Research Skill | Implementation Skill |
|----------|---------------|---------------------|
| `python` | skill-python-research | skill-theory-implementation |
| `general` | skill-researcher | skill-implementer |
| `meta` | skill-researcher | skill-implementer |

---

## Rules

Rules define automatic behaviors applied based on file paths. They are loaded when working in matching directories.

| Rule | Scope | Purpose |
|------|-------|---------|
| [state-management.md](../rules/state-management.md) | `.claude/specs/**` | Task state patterns and sync rules |
| [git-workflow.md](../rules/git-workflow.md) | All | Commit message conventions |
| [python-z3.md](../rules/python-z3.md) | `**/*.py` | Python/Z3 development patterns |
| [error-handling.md](../rules/error-handling.md) | `.claude/**` | Error recovery patterns |
| [artifact-formats.md](../rules/artifact-formats.md) | `.claude/specs/**` | Report, plan, summary formats |
| [workflows.md](../rules/workflows.md) | `.claude/**` | Command lifecycle patterns |

---

## Artifacts

Tasks produce artifacts stored in `.claude/specs/{N}_{SLUG}/`:

### Research Reports

**Location**: `reports/research-{NNN}.md`

```markdown
# Research Report: Task #{N}

**Task**: {title}
**Date**: {ISO_DATE}
**Focus**: {optional focus}

## Summary
## Findings
## Recommendations
## References
## Next Steps
```

### Implementation Plans

**Location**: `plans/implementation-{NNN}.md`

```markdown
# Implementation Plan: Task #{N}

**Task**: {title}
**Version**: {NNN}
**Created**: {ISO_DATE}
**Language**: {language}

## Overview
## Phases
### Phase 1: {Name}
**Status**: [NOT STARTED]
**Objectives**: ...
**Steps**: ...
**Verification**: ...
## Success Criteria
```

### Implementation Summaries

**Location**: `summaries/implementation-summary-{DATE}.md`

Created on task completion with changes made, files modified, and verification notes.

### Phase Status Markers

Plans use these markers for phase tracking:
- `[NOT STARTED]` - Phase not begun
- `[IN PROGRESS]` - Currently executing
- `[COMPLETED]` - Phase finished
- `[PARTIAL]` - Interrupted (enables resume)
- `[BLOCKED]` - Cannot proceed

---

## State Management

### Dual-File System

| File | Purpose | Format |
|------|---------|--------|
| `TODO.md` | User-facing task list | Markdown with status markers |
| `state.json` | Machine-readable state | JSON with task metadata |

Both files MUST stay synchronized. Updates use a two-phase commit pattern.

### Status Transitions

```
[NOT STARTED] --> [RESEARCHING] --> [RESEARCHED]
                                        |
                                        v
                              [PLANNING] --> [PLANNED]
                                                |
                                                v
                                    [IMPLEMENTING] --> [COMPLETED]

Any state --> [BLOCKED] (with reason)
Any state --> [ABANDONED] (moves to archive)
[IMPLEMENTING] --> [PARTIAL] (on timeout/error, enables resume)
```

### Task Entry Format

**TODO.md**:
```markdown
### {N}. {Title}
- **Effort**: {estimate}
- **Status**: [PLANNED]
- **Priority**: {High|Medium|Low}
- **Language**: {python|general|meta}
- **Research**: [link]
- **Plan**: [link]

**Description**: {details}
```

**state.json**:
```json
{
  "project_number": 349,
  "project_name": "task_slug",
  "status": "planned",
  "language": "python",
  "priority": "medium"
}
```

---

## Git Workflow

### Commit Message Format

```
task {N}: {action} {description}

Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>
```

### Standard Commit Actions

| Operation | Commit Message |
|-----------|----------------|
| Create task | `task {N}: create {title}` |
| Complete research | `task {N}: complete research` |
| Create plan | `task {N}: create implementation plan` |
| Complete phase | `task {N} phase {P}: {phase_name}` |
| Complete implementation | `task {N}: complete implementation` |
| Archive tasks | `todo: archive {N} completed tasks` |

### Commit Timing

Commits are created after:
- Task creation
- Research completion
- Plan creation
- Each implementation phase completion
- Final implementation completion

Git commit failures are logged but do NOT block operations.

---

## Guides

Detailed how-to guides for common operations:

| Guide | Purpose |
|-------|---------|
| [creating-commands.md](guides/creating-commands.md) | How to create new slash commands |
| [context-loading-best-practices.md](guides/context-loading-best-practices.md) | Efficient context loading strategies |
| [permission-configuration.md](guides/permission-configuration.md) | Configuring tool permissions |

---

## Templates

Reusable templates for creating new components:

| Template | Purpose |
|----------|---------|
| [command-template.md](templates/command-template.md) | Template for new commands |
| [agent-template.md](templates/agent-template.md) | Template for new agents/skills |
| [templates/README.md](templates/README.md) | Template documentation |

---

## Related Documentation

### System Architecture
- [ARCHITECTURE.md](../ARCHITECTURE.md) - Detailed system architecture
- [CLAUDE.md](../CLAUDE.md) - Quick reference and entry point

### Context Organization
- [context/README.md](../context/README.md) - Context file organization
- `context/core/` - Reusable patterns (orchestration, formats, standards, workflows)
- `context/project/` - ModelChecker-specific domain knowledge

### Project Documentation
- [ModelChecker README](../../README.md) - Main project documentation
- [Code/docs/](../../Code/docs/) - Technical development standards
- [Docs/](../../Docs/) - User-facing documentation

### Testing and Development
- [Code/docs/core/TESTING_GUIDE.md](../../Code/docs/core/TESTING_GUIDE.md) - TDD requirements
- [Code/docs/core/CODE_STANDARDS.md](../../Code/docs/core/CODE_STANDARDS.md) - Coding standards

---

## Quick Reference

### Essential Commands
```bash
/task "description"      # Create new task
/research N              # Research task
/plan N                  # Create plan
/implement N             # Execute implementation
/todo                    # Archive completed tasks
```

### Key Paths
```
.claude/specs/TODO.md           # Task list
.claude/specs/state.json        # Machine state
.claude/specs/errors.json       # Error tracking
.claude/specs/{N}_{SLUG}/       # Task artifacts
```

### Testing (for Python/Z3 development)
```bash
PYTHONPATH=Code/src pytest Code/tests/ -v                           # All tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/logos/tests/ -v  # Theory tests
```

---

[Back to ModelChecker](../../README.md) | [Architecture](../ARCHITECTURE.md) | [Context](../context/README.md)
