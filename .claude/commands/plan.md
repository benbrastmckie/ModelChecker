---
description: Create implementation plan for a task
allowed-tools: Read, Write, Edit, Glob, Grep, Bash(git:*), TodoWrite
argument-hint: TASK_NUMBER
model: claude-opus-4-5-20251101
---

# /plan Command

Create a phased implementation plan for a task.

## Arguments

- `$1` - Task number (required)

## Execution

### 1. Parse and Validate

```
task_number = $ARGUMENTS
```

Read .claude/specs/state.json:
- Find task by project_number
- Extract: language, status, project_name, description
- If not found: Error "Task {N} not found"

### 2. Validate Status

Allowed: not_started, researched, partial
- If planned: Note existing plan, offer --force for revision
- If completed: Error "Task already completed"
- If implementing: Error "Task in progress, use /revise instead"

### 3. Load Context

Get directory name from state.json `directory` field, or construct it:
```bash
DIR=$(jq -r ".active_projects[] | select(.project_number == {N}) | .directory" .claude/specs/state.json)
# Fallback: PADDED=$(printf "%03d" {N}); DIR="${PADDED}_{SLUG}"
```

1. **Task description** from TODO.md
2. **Research reports** from .claude/specs/${DIR}/reports/
3. **Relevant codebase context**:
   - For lean: Related .lean files
   - For general: Related source files

### 4. Update Status to PLANNING

Update both files atomically:
1. state.json: status = "planning"
2. TODO.md: Status: [PLANNING]

### 5. Create Implementation Plan

Create directory if needed (use DIR from step 3):
```bash
mkdir -p .claude/specs/${DIR}/plans/
```

Find next plan version (implementation-001.md, implementation-002.md, etc.)

Write to `.claude/specs/${DIR}/plans/implementation-{NNN}.md`:

```markdown
# Implementation Plan: Task #{N}

**Task**: {title}
**Version**: {NNN}
**Created**: {ISO_DATE}
**Language**: {language}

## Overview

{Summary of implementation approach based on research findings}

## Phases

### Phase 1: {Name}

**Estimated effort**: {X hours}
**Status**: [NOT STARTED]

**Objectives**:
1. {Objective}
2. {Objective}

**Files to modify**:
- `path/to/file1.ext` - {what changes}
- `path/to/file2.ext` - {what changes}

**Steps**:
1. {Detailed step}
2. {Detailed step}
3. {Detailed step}

**Verification**:
- {How to verify this phase is complete}

---

### Phase 2: {Name}

**Estimated effort**: {X hours}
**Status**: [NOT STARTED]

{Same structure as Phase 1}

---

### Phase 3: {Name}

{Continue as needed, typically 2-5 phases}

## Dependencies

- {External dependency or prerequisite}
- {Related task that must complete first}

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| {Risk} | {High/Med/Low} | {High/Med/Low} | {Strategy} |

## Success Criteria

- [ ] {Measurable criterion 1}
- [ ] {Measurable criterion 2}
- [ ] {Tests pass / builds succeed}

## Rollback Plan

{How to revert if implementation fails}
```

### 6. Update Status to PLANNED

Update both files atomically:
1. state.json:
   - status = "planned"
   - planned = today's date (YYYY-MM-DD)
   - artifacts += [plan_path]
   - plan_path = path to plan
   - plan_metadata = {plan_version: NNN}
   - last_updated = now
2. TODO.md:
   - Status: [PLANNED]
   - Planned: {date}
   - Add Plan link

**Timestamp**: Set `planned` to today's date to record when planning completed.

### 7. Git Commit

```bash
git add .claude/specs/
git commit -m "task {N}: create implementation plan"
```

### 8. Output

```
Plan created for Task #{N}

Plan: .claude/specs/${DIR}/plans/implementation-{NNN}.md

Phases:
1. {Phase 1 name} - {effort}
2. {Phase 2 name} - {effort}
...

Total estimated effort: {sum}

Status: [PLANNED]
Next: /implement {N}
```
