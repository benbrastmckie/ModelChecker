# ModelChecker Agent System Architecture

**Version**: 2.0
**Status**: Active
**Created**: 2026-01-09
**Purpose**: Document the architecture of the .claude system for ModelChecker

---

## System Overview

The .claude system is a task management and automation framework designed for Python/Z3 semantic theory development. This document describes the architecture adapted for the ModelChecker project.

### Purpose and Goals

- Provide structured task management with research, planning, and implementation workflows
- Prevent delegation hangs and infinite loops through explicit return handling
- Enable atomic state synchronization across multiple tracking files
- Support language-specific routing (Python vs general development)
- Track and analyze errors for continuous improvement
- Automate git commits with clear, scoped changes
- Enforce TDD workflow for all implementations

### Key Adaptations for ModelChecker

This system was adapted from a Lean 4 theorem proving system with these changes:

1. **Python/Z3 Focus**: Skills and rules target Python development with Z3 solver
2. **Theory Library**: Context organized around semantic theories (logos, exclusion, imposition, bimodal)
3. **Testing Integration**: pytest workflow with PYTHONPATH management
4. **No External MCP**: Uses standard tools (no lean-lsp equivalent needed)

---

## Architecture Principles

### 1. Delegation Safety

All delegation follows strict safety patterns to prevent hangs and loops:

- **Session ID Tracking**: Every delegation has a unique session ID for tracking
- **Depth Limits**: Maximum delegation depth of 3 levels
- **Cycle Detection**: Check delegation path before routing to prevent loops
- **Timeout Enforcement**: All delegations have timeouts (default 3600s)
- **Return Validation**: All subagent returns validated against standard format

### 2. Standardized Returns

All skills return a consistent JSON format:

```json
{
  "status": "completed|failed|partial|blocked",
  "summary": "Brief 2-5 sentence summary",
  "artifacts": [...],
  "metadata": {
    "session_id": "...",
    "duration_seconds": 123,
    "agent_type": "...",
    "delegation_depth": 1,
    "delegation_path": [...]
  },
  "errors": [...],
  "next_steps": "..."
}
```

### 3. Atomic State Updates

Status changes are synchronized atomically across multiple files:

- **Two-Phase Commit**: Prepare all updates in memory, then commit all or rollback
- **Files Synced**: TODO.md, state.json, project state.json, plan files
- **Rollback on Failure**: If any file update fails, all changes are rolled back
- **Consistency Guarantee**: Status is always consistent across all tracking files

### 4. Language-Based Routing

Tasks are routed to appropriate skills based on the Language field:

- `Language: python` → python-research, theory-implementation skills
- `Language: general` → general researcher, implementer skills
- `Language: meta` → meta system builder skills

### 5. Error Tracking and Recovery

All errors are logged to errors.json with:

- Error type and severity
- Context (command, task, skill, session)
- Fix status tracking
- Recurrence detection
- Fix effectiveness analysis

---

## Component Hierarchy

The system has four levels of components:

### Level 0: Orchestrator

**Skill**: `skill-orchestrator`

**Responsibilities**:
- Central coordination and routing
- Delegation registry management
- Cycle detection and depth enforcement
- Timeout monitoring
- Return validation

### Level 1: Commands

**Directory**: `.claude/commands/`

**Commands**:
- `/task`: Create tasks in TODO.md
- `/research`: Conduct research and create reports
- `/plan`: Create implementation plans
- `/implement`: Execute implementation with resume support
- `/revise`: Revise existing plans
- `/review`: Analyze codebase
- `/todo`: Maintain TODO.md (clean completed tasks)
- `/errors`: Analyze errors and create fix plans
- `/meta`: Build custom architectures through interactive interview

**Common Pattern**:
All commands that invoke skills follow this workflow:
1. ArgumentParsing: Extract and validate arguments
2. Preflight: Validate inputs and update status
3. CheckLanguage: Determine routing based on task language
4. InvokeSkill: Delegate to appropriate skill with session tracking
5. ReceiveResults: Wait for and receive skill return (with timeout)
6. ProcessResults: Extract artifacts and determine next steps
7. Postflight: Update status atomically and create git commit
8. ReturnSuccess: Return summary to user

### Level 2: Skills

**Directory**: `.claude/skills/`

**Core Skills**:
- `skill-orchestrator`: Central coordination and routing
- `skill-status-sync`: Atomic multi-file status updates
- `skill-git-workflow`: Scoped git commits with auto-generated messages
- `skill-researcher`: General research for non-Python tasks
- `skill-planner`: Implementation plan creation
- `skill-implementer`: Direct implementation for simple tasks

**Python-Specific Skills**:
- `skill-python-research`: Python/Z3 library research and pattern discovery
- `skill-theory-implementation`: Semantic theory development with TDD

### Level 3: Context Files

**Directory**: `.claude/context/`

Two-tier organization:
- `core/`: Reusable, project-agnostic patterns and standards
- `project/`: ModelChecker-specific domain knowledge

---

## Skill Overview

### skill-python-research

Specialized research for Python/Z3 development tasks:

**Tools Used**:
- WebSearch, WebFetch for Z3 documentation
- Read, Grep, Glob for codebase exploration
- Python REPL exploration when needed

**Research Targets**:
- Z3 API patterns and solver strategies
- Existing codebase patterns
- Theory implementation approaches
- Testing strategies

### skill-theory-implementation

Execute semantic theory implementation with TDD:

**Tools Used**:
- Read, Write, Edit for code modification
- Bash(pytest) for test execution
- Bash(python) for validation

**Workflow**:
1. Load implementation plan
2. Write failing tests first (TDD)
3. Implement minimal code to pass
4. Refactor while tests pass
5. Verify with full test suite

### skill-researcher

General-purpose research skill:

**Tools Used**:
- WebSearch, WebFetch for external research
- Read, Grep for codebase analysis

### skill-planner

Create implementation plans from research:

**Tools Used**:
- Read for loading research reports
- Write for creating plan files

### skill-implementer

Direct implementation for simple tasks:

**Tools Used**:
- Read, Write, Edit for code changes
- Bash for validation commands

---

## State Management

### TODO.md

**Location**: `.claude/specs/TODO.md`

**Purpose**: User-facing task list with status markers

**Format**:
```markdown
### 191. Add new operator to logos theory
- **Effort**: 4 hours
- **Status**: [PLANNED]
- **Priority**: medium
- **Language**: python
- **Started**: 2026-01-09T10:00:00Z
- **Plan**: [implementation-001.md](191_add_new_operator/plans/implementation-001.md)
- **Research**: [research-001.md](191_add_new_operator/reports/research-001.md)
```

**Status Markers**:
- `[NOT STARTED]`: Task created but not started
- `[RESEARCHING]`: Research in progress
- `[RESEARCHED]`: Research completed
- `[PLANNING]`: Plan being created
- `[PLANNED]`: Plan created
- `[IMPLEMENTING]`: Implementation in progress
- `[COMPLETED]`: Task fully completed
- `[ABANDONED]`: Task abandoned

### state.json

**Location**: `.claude/specs/state.json`

**Purpose**: Machine-readable project state

**Format**:
```json
{
  "next_project_number": 346,
  "active_projects": [
    {
      "project_number": 191,
      "project_name": "add_new_operator",
      "status": "planned",
      "language": "python",
      "priority": "medium",
      "started": "2026-01-09T10:00:00Z"
    }
  ]
}
```

### errors.json

**Location**: `.claude/specs/errors.json`

**Purpose**: Error tracking and fix effectiveness analysis

---

## Git Workflow

### Automatic Commits

Git commits are created automatically after:
- Task completion
- Phase completion (if using plan)
- Research completion
- Plan creation
- Error fix plan creation

### Commit Message Format

**Per-phase commits**:
```
task {number} phase {N}: {phase_description}
```

**Full task commits**:
```
task {number}: {task_description}
```

### Non-Blocking Failures

Git commit failures are logged but do NOT fail the task.

---

## Python/Z3 Integration

### Testing Workflow

All implementations follow TDD:

```bash
# Run specific theory tests
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/logos/tests/ -v

# Run with coverage
pytest --cov=model_checker --cov-report=term-missing

# Quick validation
PYTHONPATH=Code/src python -c "from model_checker import ..."
```

### Theory Development Pattern

```python
# 1. Define semantic defaults in semantic.py
class MyTheorySemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {...}

# 2. Register operators in operators.py
def get_operators():
    return OperatorCollection([...])

# 3. Create examples in examples.py
examples = [BuildExample(...), ...]

# 4. Add iteration support in iterate.py
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

## Context Organization

### Core Context (`context/core/`)

Reusable patterns and standards:
- `formats/`: Document structure templates
- `orchestration/`: Delegation and routing patterns
- `standards/`: Code and documentation standards
- `workflows/`: Command lifecycle patterns

### Project Context (`context/project/`)

ModelChecker-specific knowledge:
- `modelchecker/`: Architecture, theories, Z3 patterns
- `logic/`: Modal logic domain knowledge (shared from ProofChecker)
- `processes/`: Development workflows

---

## Rules

**Directory**: `.claude/rules/`

| Rule | Scope | Purpose |
|------|-------|---------|
| `state-management.md` | `.claude/specs/**` | Task state patterns |
| `git-workflow.md` | All | Commit conventions |
| `python-z3.md` | `**/*.py` | Python/Z3 development |
| `error-handling.md` | `.claude/**` | Error recovery |
| `artifact-formats.md` | `.claude/specs/**` | Document formats |
| `workflows.md` | `.claude/**` | Command lifecycle |

---

## Error Handling and Recovery

### Error Types

- `tool_failure`: External tool failed
- `status_sync_failure`: Failed to update TODO.md/state.json
- `test_failure`: Tests failed during implementation
- `import_error`: Python import failed
- `z3_timeout`: Z3 solver timed out
- `git_commit_failure`: Git commit failed
- `timeout`: Operation exceeded timeout

### Recovery Patterns

**Test Failure**:
1. Capture test output
2. Log to errors.json
3. Keep task IN PROGRESS
4. Report failure with context

**Z3 Timeout**:
1. Reduce constraint complexity
2. Increase timeout if justified
3. Consider incremental solving

**Import Error**:
1. Check PYTHONPATH set correctly
2. Verify package installed
3. Check relative import paths

---

## Future Enhancements

### Planned Features

1. **Parallel Phase Execution**: Execute independent phases in parallel
2. **Test Coverage Tracking**: Track coverage changes per task
3. **Theory Validation**: Automated semantic theory validation
4. **Performance Profiling**: Track and optimize slow operations

### Extensibility

The architecture supports extension through:
- New commands (add to `.claude/commands/`)
- New skills (add to `.claude/skills/`)
- New context (add to `.claude/context/project/`)
- New rules (add to `.claude/rules/`)

---

## Related Documentation

- Quick Reference: `.claude/CLAUDE.md`
- Project Standards: `Code/docs/README.md`
- Testing Guide: `Code/docs/core/TESTING_GUIDE.md`
- Architecture Overview: `Code/docs/core/ARCHITECTURE.md`
