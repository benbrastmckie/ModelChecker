# ModelChecker Development System

A structured task management and agent orchestration system for semantic theory development in Python with Z3 SMT solver.

## Quick Reference

- **Task List**: @.claude/specs/TODO.md
- **Machine State**: @.claude/specs/state.json
- **Error Tracking**: @.claude/specs/errors.json
- **Architecture**: @.claude/ARCHITECTURE.md

## System Overview

ModelChecker is a framework for developing modular semantic theories using Z3. The development workflow uses numbered tasks with structured research → plan → implement cycles.

### Project Structure

```
ModelChecker/
├── Code/                    # Main implementation
│   ├── src/model_checker/   # Source code
│   │   ├── theory_lib/      # Semantic theories (logos, exclusion, imposition, bimodal)
│   │   ├── builder/         # Model construction and execution
│   │   ├── iterate/         # Model iteration framework
│   │   ├── models/          # Core model structures
│   │   ├── syntactic/       # Formula parsing
│   │   └── output/          # Result formatting
│   ├── docs/                # Technical standards
│   └── tests/               # Test suites
├── Docs/                    # User documentation
├── specs/                   # Legacy specs location
└── .claude/specs/           # Task management artifacts
```

## Task Management

### Status Markers
Tasks progress through these states:
- `[NOT STARTED]` - Initial state
- `[RESEARCHING]` → `[RESEARCHED]` - Research phase
- `[PLANNING]` → `[PLANNED]` - Planning phase
- `[IMPLEMENTING]` → `[COMPLETED]` - Implementation phase
- `[BLOCKED]`, `[ABANDONED]`, `[PARTIAL]` - Terminal/exception states

### Task Artifact Paths

Directory format uses 3-digit zero-padded numbers (see state-management.md):
```
.claude/specs/{NNN}_{SLUG}/
├── reports/                    # Research artifacts
│   └── research-{NNN}.md
├── plans/                      # Implementation plans
│   └── implementation-{NNN}.md
└── summaries/                  # Completion summaries
    └── implementation-summary-{DATE}.md
```

### Language-Based Routing

Tasks have a `Language` field that determines tool selection:

| Language | Research Tools | Implementation Tools |
|----------|----------------|---------------------|
| `python` | WebSearch, WebFetch, Read, Grep | Read, Write, Edit, Bash(pytest), Bash(python) |
| `general` | WebSearch, WebFetch, Read | Read, Write, Edit, Bash |
| `meta` | Read, Grep, Glob | Write, Edit |

## Command Workflows

### /task - Create or manage tasks
```
/task "Description"          # Create new task
/task --recover 343-345      # Recover from archive
/task --divide 326           # Split into subtasks
/task --sync                 # Sync TODO.md with state.json
/task --abandon 343-345      # Archive tasks
```

### /research N [focus] - Research a task
1. Validate task exists
2. Update status to [RESEARCHING]
3. Execute research (language-routed)
4. Create report in .claude/specs/{N}_{SLUG}/reports/
5. Update status to [RESEARCHED]
6. Git commit

### /plan N - Create implementation plan
1. Validate task is [RESEARCHED] or [NOT STARTED]
2. Update status to [PLANNING]
3. Create phased plan with steps
4. Write to .claude/specs/{N}_{SLUG}/plans/
5. Update status to [PLANNED]
6. Git commit

### /implement N - Execute implementation
1. Validate task is [PLANNED] or [IMPLEMENTING]
2. Load plan, find resume point
3. Update status to [IMPLEMENTING]
4. Execute phases sequentially
5. Update status to [COMPLETED]
6. Create summary, git commit

### /revise N - Create new plan version
Increments plan version (implementation-002.md, etc.)

### /review - Analyze codebase
Code review and architecture analysis

### /todo - Archive completed tasks
Moves completed/abandoned tasks to archive/

### /errors - Analyze error patterns
Reads errors.json, creates fix plans

### /meta - System builder
Interactive agent system generator

## State Synchronization

**Critical**: TODO.md and state.json must stay synchronized.

### Two-Phase Update Pattern
1. Read both files
2. Prepare updates in memory
3. Write state.json first (machine state)
4. Write TODO.md second (user-facing)
5. If either fails, log error

### state.json Structure
```json
{
  "next_project_number": 346,
  "active_projects": [
    {
      "project_number": 334,
      "project_name": "task_slug",
      "status": "planned",
      "language": "python",
      "priority": "high"
    }
  ]
}
```

## Git Commit Conventions

Commits are scoped to task operations:
```
task {N}: create {title}
task {N}: complete research
task {N}: create implementation plan
task {N} phase {P}: {phase_name}
task {N}: complete implementation
todo: archive {N} completed tasks
errors: create fix plan for {N} errors
```

## Python/Z3 Development

### Essential Commands
```bash
# Run all tests
PYTHONPATH=Code/src pytest Code/tests/ -v

# Run specific theory tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/logos/tests/ -v
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/imposition/tests/ -v

# Development CLI
cd Code && ./dev_cli.py examples/my_example.py

# Build package
cd Code && python -m build
```

### Test-Driven Development
All implementations follow TDD:
1. Write failing test first
2. Implement minimal code to pass
3. Refactor while tests pass

### Import Pattern
```python
# Standard library
import os
from pathlib import Path

# Third-party
import z3
from typing import Dict, List

# Local (prefer relative imports)
from .models import Model
from ..utils import helpers
```

### Theory Structure
Each theory follows:
```
theory_lib/{theory}/
├── semantic.py      # Core semantic framework
├── operators.py     # Operator registry
├── examples.py      # Test cases
├── iterate.py       # Theory-specific iteration
├── __init__.py      # Public API
└── tests/           # Unit & integration tests
```

## Rules References

Core rules (automatically applied based on file paths):
- @.claude/rules/state-management.md - Task state patterns (paths: .claude/specs/**)
- @.claude/rules/git-workflow.md - Commit conventions
- @.claude/rules/python-z3.md - Python/Z3 development patterns (paths: **/*.py)
- @.claude/rules/error-handling.md - Error recovery patterns (paths: .claude/**)
- @.claude/rules/artifact-formats.md - Report/plan formats (paths: .claude/specs/**)
- @.claude/rules/workflows.md - Command lifecycle patterns (paths: .claude/**)

## Project Context Imports

Domain knowledge (load as needed):
- @.claude/context/project/modelchecker/architecture.md - System architecture
- @.claude/context/project/modelchecker/theories.md - Theory library overview
- @.claude/context/project/modelchecker/z3-patterns.md - Z3 solver patterns
- @.claude/context/project/logic/domain/kripke-semantics-overview.md - Modal semantics

## Error Handling

### On Command Failure
- Keep task in current status (don't regress)
- Log error to errors.json if persistent
- Preserve partial progress for resume

### On Timeout
- Mark current phase [PARTIAL]
- Next /implement resumes from incomplete phase

## Session Patterns

### Starting Work on a Task
```
1. Read TODO.md to find task
2. Check current status
3. Use appropriate command (/research, /plan, /implement)
```

### Resuming Interrupted Work
```
1. /implement N automatically detects resume point
2. Continues from last incomplete phase
3. No manual intervention needed
```

## Key Development Principles

### From Code/docs/core/
- **TDD Mandatory**: Write tests BEFORE implementation
- **No Backwards Compatibility**: Clean breaks when improving
- **Fail-Fast**: Early validation, clear error messages
- **Explicit Data Flow**: No hidden state

### Quality Standards
- Type coverage: >90%
- Cyclomatic complexity: <10
- Test coverage: >85% overall, >90% critical paths
- All public APIs documented

## Important Notes

- Always update status BEFORE starting work (preflight)
- Always update status AFTER completing work (postflight)
- State.json is source of truth for machine operations
- TODO.md is source of truth for user visibility
- Git commits are non-blocking (failures logged, not fatal)
- PYTHONPATH must be set to `Code/src` for imports to work
