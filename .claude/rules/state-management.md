---
paths: .claude/specs/**/*
---

# State Management Rules

## File Synchronization

TODO.md and state.json MUST stay synchronized. Any update to one requires updating the other.

### Canonical Sources
- **state.json**: Machine-readable source of truth
  - next_project_number
  - active_projects array with status, language, priority, timestamps
  - Faster to query (12ms vs 100ms for TODO.md parsing)

- **TODO.md**: User-facing source of truth
  - Human-readable task list with descriptions
  - Status markers in brackets: [STATUS]
  - Grouped by priority (High/Medium/Low)
  - Frontmatter with task_counts statistics

## Status Transitions

### Valid Transitions
```
[NOT STARTED] → [RESEARCHING] → [RESEARCHED]
[RESEARCHED] → [PLANNING] → [PLANNED]
[PLANNED] → [IMPLEMENTING] → [COMPLETED]

Any state → [BLOCKED] (with reason)
Any state → [ABANDONED] (moves to archive)
[IMPLEMENTING] → [PARTIAL] (on timeout/error)
```

### Invalid Transitions
- Cannot skip phases (e.g., NOT STARTED → PLANNED)
- Cannot regress (e.g., PLANNED → RESEARCHED) except for revisions
- Cannot mark COMPLETED without all phases done

## Two-Phase Update Pattern

When updating task status:

### Phase 1: Prepare
```
1. Read current state.json
2. Read current TODO.md
3. Validate task exists in both
4. Prepare updated content in memory
5. Validate updates are consistent
```

### Phase 2: Commit
```
1. Write state.json (machine state first)
2. Write TODO.md (user-facing second)
3. Verify both writes succeeded
4. If either fails: log error, preserve original state
```

## Project Number Format

Project numbers use **3-digit zero-padded format** for directory names and artifact paths:

```
Format: {NNN}  →  printf "%03d" $project_number
Examples: 001, 012, 345
```

This ensures:
- Consistent lexicographic sorting in file explorers
- Readable directory listings (001, 002, ... not 1, 10, 100, 2)
- Support for up to 999 active projects

**Usage in paths**: `.claude/specs/{NNN}_{SLUG}/`

**Note**: The `project_number` field in state.json stores the integer value (e.g., 1),
while directory names use the padded format (e.g., 001).

## TODO.md Frontmatter

The frontmatter contains metadata about the task list:

```yaml
---
last_updated: 2026-01-10T19:00:00Z
next_project_number: 3
task_counts:
  active: 2
  completed: 1
  in_progress: 1
---
```

### task_counts Fields
- `active`: Tasks not completed or abandoned
- `completed`: Tasks with status = completed
- `in_progress`: Tasks with status = researching, planning, or implementing

**Update task_counts**: Recalculate after task creation, completion, or archival.

## Task Entry Format

### TODO.md Entry
```markdown
### {NUMBER}. {TITLE}
- **Effort**: {estimate}
- **Status**: [{STATUS}]
- **Started**: {YYYY-MM-DD}
- **Researched**: {YYYY-MM-DD}
- **Planned**: {YYYY-MM-DD}
- **Completed**: {YYYY-MM-DD}
- **Priority**: {High|Medium|Low}
- **Language**: {python|general|meta|markdown}
- **Blocking**: {None|task numbers}
- **Dependencies**: {None|task numbers}
- **Research**: [link to report]
- **Plan**: [link to plan]
- **Summary**: [link to summary]

**Description**: {full description}
```

### Lifecycle Timestamps
| Field | Set When |
|-------|----------|
| Started | First transition from NOT STARTED (typically /research) |
| Researched | Research completes (/research) |
| Planned | Planning completes (/plan) |
| Completed | Implementation completes (/implement) |

### state.json Entry
```json
{
  "project_number": 334,
  "project_name": "task_slug_here",
  "status": "planned",
  "language": "python",
  "priority": "high",
  "effort": "4 hours",
  "created": "2026-01-08T10:00:00Z",
  "last_updated": "2026-01-08T14:30:00Z",
  "started": "2026-01-08",
  "researched": "2026-01-08",
  "planned": "2026-01-08",
  "completed": null,
  "artifacts": [
    ".claude/specs/334_task_slug/reports/research-001.md",
    ".claude/specs/334_task_slug/plans/implementation-001.md"
  ],
  "directory": "334_task_slug",
  "plan_path": ".claude/specs/334_task_slug/plans/implementation-001.md",
  "plan_metadata": {
    "plan_version": 1
  }
}
```

### state.json Timestamp Fields
| Field | Type | Description |
|-------|------|-------------|
| created | ISO timestamp | When task was created |
| last_updated | ISO timestamp | Last modification time |
| started | ISO date | When work began |
| researched | ISO date | When research completed |
| planned | ISO date | When planning completed |
| completed | ISO date | When implementation completed |
| artifacts | array | Paths to all artifacts |
| plan_path | string | Path to current plan |
| plan_metadata | object | Version and revision info |

## Status Values Mapping

| TODO.md Marker | state.json status |
|----------------|-------------------|
| [NOT STARTED] | not_started |
| [RESEARCHING] | researching |
| [RESEARCHED] | researched |
| [PLANNING] | planning |
| [PLANNED] | planned |
| [IMPLEMENTING] | implementing |
| [COMPLETED] | completed |
| [BLOCKED] | blocked |
| [ABANDONED] | abandoned |
| [PARTIAL] | partial |

## Artifact Linking

When creating artifacts, update TODO.md with links:

### Research Completion
```markdown
- **Status**: [RESEARCHED]
- **Research**: [.claude/specs/{NNN}_{SLUG}/reports/research-001.md]
```

### Plan Completion
```markdown
- **Status**: [PLANNED]
- **Plan**: [.claude/specs/{NNN}_{SLUG}/plans/implementation-001.md]
```

### Implementation Completion
```markdown
- **Status**: [COMPLETED]
- **Completed**: 2026-01-08
- **Summary**: [.claude/specs/{NNN}_{SLUG}/summaries/implementation-summary-20260108.md]
```

## Directory Creation

Create task directories lazily (only when first artifact is created):
```
.claude/specs/{NNN}_{SLUG}/
├── reports/      # Created on first research
├── plans/        # Created on first plan
└── summaries/    # Created on completion
```

## Error Handling

### On Write Failure
1. Do not update either file partially
2. Log error with context
3. Preserve original state
4. Return error to caller

### On Inconsistency Detection
1. Log the inconsistency
2. Use git blame to determine latest
3. Sync to latest version
4. Create backup of overwritten version
