# Status Markers Convention

**Status**: Active  
**Created**: 2026-01-05  
**Purpose**: Single source of truth for status markers across TODO.md and state.json

---

## Overview

This document defines the complete set of status markers used throughout this agent system for tracking task and phase progress. It serves as the authoritative reference for:

- **Status Marker Definitions**: All valid status markers and their meanings
- **TODO.md Format**: How markers appear in TODO.md task entries
- **state.json Format**: How status values appear in state.json
- **Valid Transitions**: Which status changes are allowed
- **Command Mappings**: Which commands trigger which status changes

---

## Status Marker Definitions

### Standard Status Markers

#### `[NOT STARTED]`
**TODO.md Format**: `- **Status**: [NOT STARTED]`  
**state.json Value**: `"status": "not_started"`  
**Meaning**: Task or phase has not yet begun.

**Valid Transitions**: Any command (research, plan, implement, revise) can run from this status.

#### `[RESEARCHING]`
**TODO.md Format**: `- **Status**: [RESEARCHING]`  
**state.json Value**: `"status": "researching"`  
**Meaning**: Research is actively underway.

**Valid Transitions**: Non-terminal; any command can run. Normally completes to `[RESEARCHED]`.

**Timestamps**: Always include `- **Researched**: YYYY-MM-DD` when started

#### `[RESEARCHED]`
**TODO.md Format**: `- **Status**: [RESEARCHED]`  
**state.json Value**: `"status": "researched"`  
**Meaning**: Research completed, deliverables created.

**Valid Transitions**: Any command (research, plan, implement, revise) can run from this status.

**Required Artifacts**: Research report linked in TODO.md

#### `[PLANNING]`
**TODO.md Format**: `- **Status**: [PLANNING]`  
**state.json Value**: `"status": "planning"`  
**Meaning**: Implementation plan is being created.

**Valid Transitions**: Non-terminal; any command can run. Normally completes to `[PLANNED]`.

**Timestamps**: Always include `- **Planned**: YYYY-MM-DD` when started

#### `[PLANNED]`
**TODO.md Format**: `- **Status**: [PLANNED]`  
**state.json Value**: `"status": "planned"`  
**Meaning**: Implementation plan completed, ready for implementation.

**Valid Transitions**: Any command (research, plan, implement, revise) can run from this status.

**Required Artifacts**: Implementation plan linked in TODO.md

#### `[REVISING]`
**TODO.md Format**: `- **Status**: [REVISING]`  
**state.json Value**: `"status": "revising"`  
**Meaning**: Plan revision is in progress.

**Valid Transitions**: Non-terminal; any command can run. Normally completes to `[REVISED]`.

**Timestamps**: Always include `- **Revised**: YYYY-MM-DD` when started

#### `[REVISED]`
**TODO.md Format**: `- **Status**: [REVISED]`  
**state.json Value**: `"status": "revised"`  
**Meaning**: Plan revision completed, new plan version created.

**Valid Transitions**: Any command (research, plan, implement, revise) can run from this status.

**Required Artifacts**: Revised plan linked in TODO.md (replaces previous plan link)

#### `[IMPLEMENTING]`
**TODO.md Format**: `- **Status**: [IMPLEMENTING]`  
**state.json Value**: `"status": "implementing"`  
**Meaning**: Implementation work is actively underway.

**Valid Transitions**: Non-terminal; any command can run. Normally completes to `[COMPLETED]` or `[PARTIAL]`.

**Timestamps**: Always include `- **Implemented**: YYYY-MM-DD` when started

#### `[COMPLETED]`
**TODO.md Format**: `- **Status**: [COMPLETED]`  
**state.json Value**: `"status": "completed"`  
**Meaning**: Task is finished successfully.

**Valid Transitions**: Terminal state (no further transitions)

**Required Information**:
- `- **Completed**: YYYY-MM-DD` timestamp
- Do not add emojis; rely on status marker and text alone

#### `[PARTIAL]`
**TODO.md Format**: `- **Status**: [PARTIAL]`  
**state.json Value**: `"status": "partial"`  
**Meaning**: Implementation partially completed (can resume).

**Valid Transitions**: Any command (research, plan, implement, revise) can run from this status.

#### `[BLOCKED]`
**TODO.md Format**: `- **Status**: [BLOCKED]`  
**state.json Value**: `"status": "blocked"`  
**Meaning**: Task is blocked by dependencies or issues.

**Valid Transitions**: Any command (research, plan, implement, revise) can run from this status.

**Required Information**:
- `- **Blocked**: YYYY-MM-DD` timestamp
- `- **Blocking Reason**: {reason}` or `- **Blocked by**: {dependency}`

#### `[ABANDONED]`
**TODO.md Format**: `- **Status**: [ABANDONED]`  
**state.json Value**: `"status": "abandoned"`  
**Meaning**: Task was started but abandoned without completion.

**Valid Transitions**: Terminal state. No further transitions (use `/task --recover` to restart).

**Required Information**:
- `- **Abandoned**: YYYY-MM-DD` timestamp
- `- **Abandonment Reason**: {reason}`

#### `[EXPANDED]`
**TODO.md Format**: `- **Status**: [EXPANDED]`
**state.json Value**: `"status": "expanded"`
**Meaning**: Parent task has been expanded into subtasks; work continues in subtasks.

**Valid Transitions**: Terminal state. No further transitions (work continues in subtasks).

**Note**: Any non-terminal status can transition to `[EXPANDED]` when task is divided.

**Required Information**:
- `- **Subtasks**: {list}` in TODO.md
- `"subtasks": [...]` array in state.json

---

## TODO.md vs state.json Mapping

| TODO.md Marker | state.json Value | Description |
|----------------|------------------|-------------|
| `[NOT STARTED]` | `not_started` | Task not begun |
| `[RESEARCHING]` | `researching` | Research in progress |
| `[RESEARCHED]` | `researched` | Research completed |
| `[PLANNING]` | `planning` | Planning in progress |
| `[PLANNED]` | `planned` | Plan created |
| `[REVISING]` | `revising` | Plan revision in progress |
| `[REVISED]` | `revised` | Plan revision completed |
| `[IMPLEMENTING]` | `implementing` | Implementation in progress |
| `[COMPLETED]` | `completed` | Task fully completed |
| `[PARTIAL]` | `partial` | Implementation partially complete |
| `[BLOCKED]` | `blocked` | Task blocked |
| `[ABANDONED]` | `abandoned` | Task abandoned |
| `[EXPANDED]` | `expanded` | Task expanded into subtasks |

**Conversion Rules**:
- TODO.md uses uppercase with underscores in brackets: `[NOT STARTED]`
- state.json uses lowercase with underscores: `"not_started"`
- Conversion: Remove brackets, convert to lowercase

---

## Command → Status Mapping

| Command | Preflight Status | Postflight Status | Notes |
|---------|------------------|-------------------|-------|
| `/research` | `[RESEARCHING]` | `[RESEARCHED]` | Creates research report |
| `/plan` | `[PLANNING]` | `[PLANNED]` | Creates implementation plan |
| `/revise` | `[REVISING]` | `[REVISED]` | Creates new plan version |
| `/implement` | `[IMPLEMENTING]` | `[COMPLETED]` or `[PARTIAL]` | Executes implementation |
| `/review` | N/A | N/A | Creates new tasks |

**Preflight**: Status updated BEFORE work begins  
**Postflight**: Status updated AFTER work completes

---

## Valid Transition Diagram

```
                    ┌─────────────────────────────────────────┐
                    │         Any Non-Terminal Status          │
                    │                                         │
                    │  NOT STARTED, RESEARCHING, RESEARCHED,  │
                    │  PLANNING, PLANNED, REVISING, REVISED,  │
                    │  IMPLEMENTING, PARTIAL, BLOCKED         │
                    └──────────────┬──────────────────────────┘
                                   │
              ┌────────────────────┼────────────────────┐
              │                    │                     │
              ▼                    ▼                     ▼
        /research             /plan, /revise        /implement
              │                    │                     │
              ▼                    ▼                     ▼
        [RESEARCHING]        [PLANNING]           [IMPLEMENTING]
              │               [REVISING]                │
              ▼                    │              ┌──────┴──────┐
        [RESEARCHED]               ▼              ▼             ▼
                             [PLANNED]       [COMPLETED]   [PARTIAL]
                             [REVISED]

    Terminal states (no further transitions):
    [COMPLETED], [ABANDONED], [EXPANDED]
```

---

## Status Update Protocol

Status updates are performed by `skill-base.sh` functions that all workflow skills source:

- `skill_preflight_update()` -- called BEFORE work begins. Sets the in-progress status variant (e.g., `[RESEARCHING]`, `[IMPLEMENTING]`) in both `state.json` and `TODO.md`.
- `skill_postflight_update()` -- called AFTER work completes. Sets the final status variant (e.g., `[RESEARCHED]`, `[COMPLETED]`) and links artifacts.

Both functions delegate to `update-task-status.sh` for the actual atomic file updates.

For manual corrections and recovery operations outside the normal workflow, use the `skill-status-sync` skill, which provides standalone preflight, postflight, and artifact-link operations.

### Preflight Status Update

**When**: BEFORE work begins  
**Path**: `skill_preflight_update()` in `skill-base.sh` -> `update-task-status.sh`  
**Purpose**: Signal work has started  
**Example**: `/research` calls `skill_preflight_update()` to set `[RESEARCHING]` before beginning research

### Postflight Status Update

**When**: AFTER work completes  
**Path**: `skill_postflight_update()` in `skill-base.sh` -> `update-task-status.sh`  
**Purpose**: Signal work has finished and link artifacts  
**Example**: `/research` calls `skill_postflight_update()` to set `[RESEARCHED]` after creating research report

---

## Atomic Synchronization

`update-task-status.sh` performs updates atomically in this order:
1. `state.json` (status field, timestamps, artifact_paths)
2. `TODO.md` (status marker, timestamps, artifact links)
3. Plan file (phase status markers, if plan exists)

All files are updated via temp-file + atomic rename so no partial state is written on failure.

---

## Validation Rules

### Status Transition Validation

**Permissive Rule**: Any command can run from any non-terminal status.

**Terminal States** (block all transitions):
- `[COMPLETED]` - No further transitions
- `[ABANDONED]` - No further transitions (use `/task --recover` to restart)
- `[EXPANDED]` - No further transitions (work continues in subtasks)

### Required Fields Validation

**For `[BLOCKED]` status**:
- MUST include `blocking_reason` or `blocked_by` parameter
- MUST include `- **Blocked**: YYYY-MM-DD` timestamp in TODO.md

**For `[ABANDONED]` status**:
- MUST include `abandonment_reason` parameter
- MUST include `- **Abandoned**: YYYY-MM-DD` timestamp in TODO.md

**For `[EXPANDED]` status**:
- MUST include `subtasks` array with subtask numbers
- MUST include `- **Subtasks**: {list}` in TODO.md

**For completion statuses** (`[RESEARCHED]`, `[PLANNED]`, `[REVISED]`, `[COMPLETED]`):
- MUST include `validated_artifacts` array with artifact paths
- Artifacts MUST exist on disk and be non-empty

---

## References

- **state-management.md**: Complete state management standard
- **skill-base.sh**: Source for `skill_preflight_update()` and `skill_postflight_update()` functions
- **update-task-status.sh**: Atomic status update script called by skill-base.sh functions
- **skill-status-sync/SKILL.md**: Standalone skill for manual status corrections and recovery

---

**Last Updated**: 2026-01-05
