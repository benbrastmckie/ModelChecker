# Implementation Plan: Task #2

**Task**: Improve metadata system for task tracking
**Version**: 001
**Created**: 2026-01-10
**Language**: meta

## Overview

Enhance the ModelChecker .claude/ metadata system by adopting valuable patterns from ProofChecker. The implementation adds lifecycle timestamps to task entries, task_counts statistics to TODO.md frontmatter, and updates all command files and skills to maintain these fields consistently. Changes are additive and backward-compatible.

## Phases

### Phase 1: Schema Documentation Updates

**Estimated effort**: 1 hour
**Status**: [COMPLETED]

**Objectives**:
1. Document new timestamp fields in state-management.md
2. Document updated TODO.md entry format in artifact-formats.md
3. Define task_counts frontmatter schema

**Files to modify**:
- `.claude/rules/state-management.md` - Add timestamp fields to schemas
- `.claude/rules/artifact-formats.md` - Add timestamps to entry format

**Steps**:
1. Update state-management.md "state.json Entry" section to include:
   - `started`: ISO date when work begins
   - `researched`: ISO date when research completes
   - `planned`: ISO date when planning completes
   - `completed`: ISO date when implementation completes
   - `artifacts`: Array of artifact paths
2. Update state-management.md "TODO.md Entry" section to include timestamp fields
3. Add task_counts schema to frontmatter documentation:
   ```yaml
   task_counts:
     active: N
     completed: N
     in_progress: N
   ```
4. Update artifact-formats.md task entry template with timestamp fields

**Verification**:
- Documentation accurately reflects new schema
- Examples are consistent across both files

---

### Phase 2: Enhance skill-status-sync

**Estimated effort**: 1.5 hours
**Status**: [COMPLETED]

**Objectives**:
1. Add timestamp field handling to skill-status-sync
2. Add artifacts array management
3. Add frontmatter task_counts update capability

**Files to modify**:
- `.claude/skills/skill-status-sync/SKILL.md` - Enhance with new operations

**Steps**:
1. Add new operation types to skill:
   - `set_timestamp`: Set a specific lifecycle timestamp
   - `add_artifact`: Add artifact to artifacts array
   - `update_task_counts`: Recalculate and update frontmatter
2. Update Status Mapping table to include timestamp fields:
   | Operation | Sets Timestamp |
   |-----------|----------------|
   | Start research | `started` (if null) |
   | Complete research | `researched` |
   | Complete planning | `planned` |
   | Complete implement | `completed` |
3. Add jq patterns for timestamp updates:
   ```bash
   # Set timestamp field
   jq --arg ts "$(date +%Y-%m-%d)" --arg field "$field_name" \
     '(.active_projects[] | select(.project_number == N)) |= . + {($field): $ts}'
   ```
4. Add task_counts calculation pattern:
   ```bash
   # Calculate from active_projects
   active=$(jq '[.active_projects[] | select(.status != "completed" and .status != "abandoned")] | length')
   completed=$(jq '[.active_projects[] | select(.status == "completed")] | length')
   in_progress=$(jq '[.active_projects[] | select(.status == "implementing" or .status == "researching" or .status == "planning")] | length')
   ```
5. Document frontmatter update pattern for TODO.md

**Verification**:
- skill-status-sync documentation includes all new operations
- jq patterns are correct and tested

---

### Phase 3: Update Command Files

**Estimated effort**: 2 hours
**Status**: [COMPLETED]

**Objectives**:
1. Update /task to initialize task_counts if missing
2. Update /research to set `started` and `researched` timestamps
3. Update /plan to set `planned` timestamp
4. Update /implement to set `completed` timestamp
5. Update /todo to recalculate task_counts after archival

**Files to modify**:
- `.claude/commands/task.md`
- `.claude/commands/research.md`
- `.claude/commands/plan.md`
- `.claude/commands/implement.md`
- `.claude/commands/todo.md`

**Steps**:

**Step 1: Update /task command**
- In "Create Task Mode", add step to check/initialize frontmatter task_counts
- Add task_counts update after task creation

**Step 2: Update /research command**
- In step 3 (Update Status to RESEARCHING), add:
  - Set `started` timestamp if not already set
- In step 6 (Update Status to RESEARCHED), add:
  - Set `researched` timestamp

**Step 3: Update /plan command**
- In step 6 (Update Status to PLANNED), add:
  - Set `planned` timestamp

**Step 4: Update /implement command**
- In step 8 (Complete Implementation), add:
  - Set `completed` timestamp

**Step 5: Update /todo command**
- In step 5 (Archive Tasks), add:
  - Recalculate task_counts from remaining active_projects
  - Update TODO.md frontmatter with new counts

**Verification**:
- Each command documents which timestamps it sets
- Commands reference skill-status-sync for atomic updates

---

### Phase 4: Initialize Current Data and Verify

**Estimated effort**: 30 minutes
**Status**: [COMPLETED]

**Objectives**:
1. Add task_counts to current TODO.md frontmatter
2. Backfill timestamps for existing Task 1 (completed)
3. Verify all files are in sync

**Files to modify**:
- `.claude/specs/TODO.md` - Add task_counts to frontmatter
- `.claude/specs/state.json` - Add timestamps to Task 1

**Steps**:
1. Add task_counts to TODO.md frontmatter:
   ```yaml
   task_counts:
     active: 1
     completed: 1
     in_progress: 0
   ```
2. Backfill Task 1 timestamps in state.json:
   ```json
   {
     "started": "2026-01-10",
     "researched": "2026-01-10",
     "planned": "2026-01-10",
     "completed": "2026-01-10"
   }
   ```
3. Add timestamps to Task 1 in TODO.md
4. Run /task --sync to verify consistency
5. Test workflow with a new task to ensure timestamps populate correctly

**Verification**:
- task_counts matches actual task status counts
- All tasks have appropriate timestamps
- /task --sync reports no inconsistencies

---

## Dependencies

- None - all changes are internal to .claude/ system

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Schema changes break existing parsing | Medium | Low | Changes are additive; old fields remain |
| Commands forget to update timestamps | Medium | Medium | Document clearly in each command |
| task_counts gets out of sync | Low | Medium | /todo recalculates; /task --sync can fix |

## Success Criteria

- [ ] state-management.md documents all new fields
- [ ] artifact-formats.md shows updated entry format
- [ ] skill-status-sync handles timestamps and task_counts
- [ ] All 5 command files updated with timestamp logic
- [ ] TODO.md has task_counts in frontmatter
- [ ] Existing tasks have backfilled timestamps
- [ ] New tasks automatically get timestamps populated
- [ ] /task --sync reports no inconsistencies

## Rollback Plan

If implementation fails:
1. Changes are additive - existing fields remain functional
2. Remove new fields from schema documentation
3. Revert command file changes
4. Remove task_counts from frontmatter
5. System continues working with original schema
