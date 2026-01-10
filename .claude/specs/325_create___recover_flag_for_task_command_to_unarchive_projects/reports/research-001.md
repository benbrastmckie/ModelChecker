# Research Report: --recover Flag for /task Command

**Task**: 325 - Create --recover flag for /task command to unarchive projects  
**Started**: 2026-01-06  
**Completed**: 2026-01-06  
**Effort**: 4-6 hours (estimated)  
**Priority**: Medium  
**Dependencies**: None  
**Sources/Inputs**:
- .opencode/command/task.md (task creation command)
- .opencode/command/todo.md (archival command)
- .opencode/scripts/todo_cleanup.py (archival script)
- .opencode/agent/subagents/status-sync-manager.md (state synchronization)
- .opencode/specs/state.json (active project state)
- .opencode/specs/archive/state.json (archived project state)
- .opencode/specs/TODO.md (user-facing task list)

**Artifacts**: .opencode/specs/325_create___recover_flag_for_task_command_to_unarchive_projects/reports/research-001.md  
**Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

---

## Executive Summary

This research investigates the current archival system and designs a recovery mechanism to unarchive projects. The system currently archives completed/abandoned tasks by moving project directories to `.opencode/specs/archive/`, removing entries from TODO.md and state.json, and adding them to archive/state.json. The proposed `--recover` flag will reverse this process atomically, restoring projects to active status while maintaining data integrity.

**Key Findings**:
1. Archive system uses atomic two-phase commit with git-only rollback
2. 130 projects currently archived (114 directories in archive/)
3. Archive state tracked in archive/state.json with full metadata
4. status-sync-manager supports create_task, archive_tasks, update_status, update_task_metadata operations
5. Recovery requires new operation: unarchive_task

**Recommended Approach**: Add `--recover <task_number>` flag to /task command, implement unarchive_task operation in status-sync-manager, reverse archival process atomically.

---

## Context & Scope

### Current Archival System

The archival system consists of:

1. **Command**: `/todo` command (`.opencode/command/todo.md`)
   - Scans state.json for completed/abandoned tasks
   - Confirms archival if > 5 tasks
   - Creates git snapshot before archival
   - Delegates to cleanup script
   - Commits archival changes

2. **Script**: `todo_cleanup.py` (`.opencode/scripts/todo_cleanup.py`)
   - Removes task blocks from TODO.md
   - Fixes divider stacking
   - Moves project directories to archive/
   - Updates state.json and archive/state.json
   - Exit codes: 0 (success), 1 (validation error), 2 (file I/O error), 3 (argument error)

3. **State Files**:
   - `.opencode/specs/state.json`: Active projects (51 active)
   - `.opencode/specs/archive/state.json`: Archived projects (130 archived)
   - Both use schema version 1.1.0

4. **Atomic Updates**:
   - Two-phase commit protocol
   - Temp files with session_id
   - Atomic rename operations
   - Git-only rollback (no backup files)

### Recovery Requirements

A `--recover` flag must:
1. Accept task number as argument: `/task --recover 123`
2. Validate task exists in archive/state.json
3. Move project directory from archive/ back to specs/
4. Remove entry from archive/state.json
5. Add entry to state.json active_projects
6. Add entry to TODO.md in appropriate priority section
7. Update status to [NOT STARTED] (or preserve original status if desired)
8. Maintain atomic updates across all files
9. Create git commit for recovery
10. Handle errors gracefully with rollback

---

## Key Findings

### Finding 1: Archive State Structure

Archive state.json contains full project metadata:

```json
{
  "project_number": 126,
  "project_name": "implement_bounded_search_and_matches_axiom_in_proofsearch",
  "type": "implementation",
  "status": "completed",
  "created": "2025-12-22T17:00:00Z",
  "completed": "2025-12-22T20:00:00Z",
  "archived": "2025-12-23T05:00:00Z",
  "summary": "Bounded search and axiom matching implemented...",
  "artifacts": {
    "base_path": ".opencode/specs/archive/126_implement_bounded_search_and_matches_axiom_in_proofsearch/"
  }
}
```

**Implications**:
- All metadata available for restoration
- Can preserve original created/completed dates
- Can restore with original status or reset to NOT STARTED
- Artifacts path needs to be updated after directory move

### Finding 2: status-sync-manager Operations

Current operations supported:
- `create_task`: Create new task entry
- `archive_tasks`: Archive multiple tasks (bulk operation)
- `update_status`: Update task status
- `update_task_metadata`: Update task fields

**Missing operation**: `unarchive_task` (needs to be added)

The status-sync-manager uses atomic write pattern:
1. Prepare updates in memory
2. Write to temp files with session_id
3. Verify temp files
4. Atomic rename (all or nothing)
5. Clean up temp files

**Implications**:
- Need to add unarchive_task operation to status-sync-manager
- Can reuse atomic write pattern for recovery
- Should follow same two-phase commit protocol

### Finding 3: TODO.md Structure

TODO.md has priority sections:
- `## High Priority`
- `## Medium Priority`
- `## Low Priority` (implied, not always present)

Task entries follow format:
```markdown
### 325. Create --recover flag for /task command to unarchive projects
- **Effort**: TBD
- **Status**: [NOT STARTED]
- **Priority**: Medium
- **Language**: meta
- **Blocking**: None
- **Dependencies**: None

**Description**: Create a --recover flag for the /task command...

---
```

**Implications**:
- Need to insert recovered task in correct priority section
- Need to preserve task number (no renumbering)
- Need to add divider after task block
- Can use existing divider fixing logic from todo_cleanup.py

### Finding 4: Project Directory Structure

Archived directories in `.opencode/specs/archive/`:
- Format: `{task_number}_{slug}/`
- Contains: reports/, plans/, summaries/, state.json (optional)
- Example: `126_implement_bounded_search_and_matches_axiom_in_proofsearch/`

**Implications**:
- Directory move is straightforward (reverse of archival)
- Need to verify directory exists before recovery
- Need to handle case where directory doesn't exist (task without artifacts)
- Need to update artifact paths in recovered metadata

### Finding 5: Git Integration

Archival process:
1. Auto-commit uncommitted changes
2. Create pre-cleanup snapshot commit
3. Run cleanup script
4. Commit archival changes

**Implications**:
- Recovery should follow similar pattern
- Create pre-recovery snapshot
- Perform recovery operations
- Commit recovery changes
- Use git-workflow-manager for scoped commits

### Finding 6: Error Handling

Archival uses comprehensive error handling:
- Validation errors (exit code 1)
- File I/O errors (exit code 2)
- Argument errors (exit code 3)
- Rollback on failure (git reset --hard HEAD~1)

**Implications**:
- Recovery should have similar error handling
- Should validate task exists in archive before starting
- Should rollback on any failure
- Should provide clear error messages

---

## Detailed Analysis

### Recovery Operation Flow

**Step 1: Parse Input**
```
Input: /task --recover 123
Parse: flag = "--recover", task_number = 123
Validate: task_number is positive integer
```

**Step 2: Validate Task in Archive**
```
Read: archive/state.json
Find: task with project_number == 123
Validate: task exists in archived_projects array
Extract: full task metadata
```

**Step 3: Prepare Recovery**
```
Read: state.json (active projects)
Read: TODO.md (active tasks)
Validate: task_number not already in active_projects
Validate: task_number not already in TODO.md
Prepare: TODO.md entry from archived metadata
Prepare: state.json entry from archived metadata
```

**Step 4: Execute Recovery (Atomic)**
```
Create temp files:
  - TODO.md.tmp.{session_id}
  - state.json.tmp.{session_id}
  - archive/state.json.tmp.{session_id}

Write updates:
  - Add task to TODO.md (correct priority section)
  - Add task to state.json active_projects
  - Remove task from archive/state.json archived_projects
  - Update next_project_number if needed

Verify temp files:
  - All files exist and size > 0

Atomic rename:
  - Rename all temp files to originals
  - All or nothing guarantee

Move directory (if exists):
  - Source: archive/{task_number}_{slug}/
  - Destination: {task_number}_{slug}/
  - Update artifact paths in metadata
```

**Step 5: Git Commit**
```
Stage files:
  - TODO.md
  - state.json
  - archive/state.json
  - Recovered directory (if exists)

Commit:
  - Message: "task: recover task {number} from archive"
```

**Step 6: Return Success**
```
Return:
  - status: "completed"
  - task_number: 123
  - files_updated: [TODO.md, state.json, archive/state.json]
  - directory_moved: true/false
  - message: "Task 123 recovered from archive"
```

### Status Restoration Strategy

**Option 1: Reset to NOT STARTED**
- Pros: Clean slate, clear that task needs work
- Cons: Loses original status information

**Option 2: Preserve Original Status**
- Pros: Maintains historical context
- Cons: May be confusing (completed task now active)

**Recommendation**: Reset to NOT STARTED by default, with optional `--preserve-status` flag for advanced use cases.

### Metadata Preservation

Fields to preserve from archive:
- `project_number` (required, immutable)
- `project_name` (required, immutable)
- `type` (optional, preserve)
- `priority` (required, preserve)
- `language` (required, preserve)
- `description` (optional, preserve)
- `effort` (optional, preserve)
- `created` (optional, preserve original creation date)
- `artifacts` (optional, update paths after directory move)

Fields to reset:
- `status` → "not_started"
- `phase` → "not_started"
- `last_updated` → current timestamp
- `completed` → remove
- `abandoned` → remove
- `archived` → remove

Fields to add:
- `recovered` → current timestamp
- `recovery_reason` → optional user-provided reason

### Edge Cases

**Case 1: Task without project directory**
- Archived task exists in archive/state.json
- No directory in archive/
- Solution: Recover metadata only, skip directory move

**Case 2: Task number conflict**
- Task 123 exists in both archive and active
- Should never happen (archival removes from active)
- Solution: Validate and abort with error

**Case 3: Partial recovery failure**
- TODO.md updated, state.json fails
- Solution: Atomic write pattern prevents this
- Rollback: Remove temp files, no changes committed

**Case 4: Directory move failure**
- Metadata recovered, directory move fails
- Solution: Log warning, continue (directory can be moved manually)
- Non-critical failure (metadata is source of truth)

**Case 5: Archive state.json missing**
- Archive directory exists, no state.json
- Solution: Abort with error, cannot recover without metadata
- Recommendation: User should investigate archive integrity

---

## Code Examples

### Example 1: /task Command Flag Parsing

```markdown
<stage id="1" name="ParseInput">
  <action>Parse task description and extract flags</action>
  <process>
    1. Check for --recover flag:
       - If present: Extract task_number from next argument
       - Validate task_number is positive integer
       - Skip to Stage 5 (RecoverTask)
       - Do NOT proceed to Stage 2-4 (task creation)
    
    2. If --recover not present:
       - Continue with normal task creation flow
       - Extract description, priority, effort, language, divide flags
  </process>
</stage>

<stage id="5" name="RecoverTask">
  <action>Recover archived task</action>
  <process>
    1. Delegate to status-sync-manager:
       - operation: "unarchive_task"
       - task_number: {task_number}
       - timestamp: $(date -I)
       - session_id: {session_id}
       - delegation_depth: {depth + 1}
       - delegation_path: [...path, "status-sync-manager"]
    
    2. Wait for status-sync-manager return
    
    3. Validate return:
       - status == "completed"
       - task_number present
       - files_updated includes [TODO.md, state.json, archive/state.json]
    
    4. Return success to user:
       - "Task {number} recovered from archive"
       - "Status: [NOT STARTED]"
       - "Project directory: {moved/not found}"
  </process>
</stage>
```

### Example 2: status-sync-manager unarchive_task Operation

```markdown
<unarchive_task_flow>
  <step_0_validate_inputs>
    <action>Validate unarchive_task inputs</action>
    <process>
      1. Validate task_number is positive integer
      2. Read archive/state.json
      3. Find task in archived_projects array
      4. If not found: abort with error "Task {number} not found in archive"
      5. Extract full task metadata
      6. Read state.json
      7. Validate task_number not in active_projects
      8. If already active: abort with error "Task {number} already active"
    </process>
  </step_0_validate_inputs>

  <step_1_prepare_recovery>
    <action>Prepare recovery updates</action>
    <process>
      1. Read current TODO.md
      2. Read current state.json
      3. Read current archive/state.json
      4. Format TODO.md entry from archived metadata:
         - Reset status to [NOT STARTED]
         - Preserve priority, effort, language, description
         - Add recovery timestamp
      5. Format state.json entry from archived metadata:
         - Reset status/phase to "not_started"
         - Preserve all other fields
         - Update last_updated to current timestamp
         - Add recovered timestamp
      6. Remove task from archive/state.json archived_projects
      7. Insert task into TODO.md (correct priority section)
      8. Append task to state.json active_projects
    </process>
  </step_1_prepare_recovery>

  <step_2_commit>
    <action>Commit updates atomically</action>
    <process>
      1. Write to temp files:
         - TODO.md.tmp.{session_id}
         - state.json.tmp.{session_id}
         - archive/state.json.tmp.{session_id}
      2. Verify temp files
      3. Atomic rename (all or nothing)
      4. Clean up temp files
    </process>
  </step_2_commit>

  <step_3_move_directory>
    <action>Move project directory from archive</action>
    <process>
      1. Check if directory exists:
         - Source: .opencode/specs/archive/{number}_{slug}/
      2. If exists:
         - Destination: .opencode/specs/{number}_{slug}/
         - Move directory: shutil.move(source, destination)
         - If move fails: Log warning (non-critical)
      3. If not exists:
         - Log info: "Task {number} has no project directory"
         - Continue (metadata recovery successful)
    </process>
  </step_3_move_directory>

  <step_4_return>
    <action>Return success</action>
    <process>
      1. Format return following subagent-return-format.md
      2. Include task_number
      3. Include files_updated
      4. Include directory_moved (true/false)
      5. Return status completed or failed
    </process>
  </step_4_return>
</unarchive_task_flow>
```

### Example 3: TODO.md Entry Insertion

```python
def insert_recovered_task(todo_lines, task_entry, priority):
    """
    Insert recovered task into TODO.md in correct priority section.
    
    Args:
        todo_lines: List of lines from TODO.md
        task_entry: Formatted task entry (list of lines)
        priority: Task priority (High, Medium, Low)
    
    Returns:
        Updated list of lines
    """
    # Find priority section
    section_header = f"## {priority} Priority"
    insert_index = -1
    
    for i, line in enumerate(todo_lines):
        if line.strip() == section_header:
            # Insert after section header
            insert_index = i + 1
            break
    
    if insert_index == -1:
        # Section not found, create it
        # Insert before first lower priority section or at end
        todo_lines.append("")
        todo_lines.append("---")
        todo_lines.append("")
        todo_lines.append(section_header)
        todo_lines.append("")
        insert_index = len(todo_lines)
    
    # Insert task entry
    for line in reversed(task_entry):
        todo_lines.insert(insert_index, line)
    
    return todo_lines
```

---

## Decisions

### Decision 1: Command Integration

**Question**: Should recovery be a flag on /task or a separate /recover command?

**Options**:
1. Flag on /task: `/task --recover 123`
2. Separate command: `/recover 123`

**Decision**: Flag on /task (`--recover`)

**Rationale**:
- /task already handles task creation, recovery is inverse operation
- Keeps task-related operations in one command
- Follows pattern of other flags (--divide, --priority, etc.)
- Simpler for users (one command for task management)

### Decision 2: Status Reset

**Question**: Should recovered tasks preserve original status or reset to NOT STARTED?

**Options**:
1. Reset to NOT STARTED
2. Preserve original status (completed/abandoned)
3. User choice via flag

**Decision**: Reset to NOT STARTED (default)

**Rationale**:
- Recovering implies task needs work again
- Preserving "completed" status is confusing
- Can add `--preserve-status` flag later if needed
- Simpler mental model for users

### Decision 3: Metadata Preservation

**Question**: Which metadata fields should be preserved vs. reset?

**Decision**:
- **Preserve**: project_number, project_name, type, priority, language, description, effort, created
- **Reset**: status, phase, last_updated, completed, abandoned, archived
- **Add**: recovered (timestamp)

**Rationale**:
- Preserve immutable identifiers (number, name)
- Preserve task characteristics (priority, effort, language)
- Reset lifecycle fields (status, dates)
- Track recovery for audit trail

### Decision 4: Directory Handling

**Question**: Should directory move failure abort recovery?

**Options**:
1. Abort recovery if directory move fails
2. Continue recovery, log warning

**Decision**: Continue recovery, log warning (non-critical failure)

**Rationale**:
- Metadata is source of truth
- Directory can be moved manually later
- Prevents recovery failure due to filesystem issues
- User can investigate and fix directory separately

### Decision 5: Bulk Recovery

**Question**: Should recovery support multiple tasks at once?

**Options**:
1. Single task only: `/task --recover 123`
2. Multiple tasks: `/task --recover 123,124,125`
3. Range support: `/task --recover 123-125`

**Decision**: Single task only (initial implementation)

**Rationale**:
- Simpler implementation
- Recovery is less common than archival
- Can add bulk support later if needed
- Follows YAGNI principle

---

## Recommendations

### Recommendation 1: Implement unarchive_task Operation

Add `unarchive_task` operation to status-sync-manager with:
- Input validation (task exists in archive, not in active)
- Atomic updates across TODO.md, state.json, archive/state.json
- Directory move with error handling
- Git commit integration
- Comprehensive error messages

**Priority**: High  
**Effort**: 3-4 hours

### Recommendation 2: Add --recover Flag to /task Command

Modify /task command to:
- Parse `--recover <task_number>` flag
- Delegate to status-sync-manager with unarchive_task operation
- Return success message with task number and status
- Handle errors gracefully

**Priority**: High  
**Effort**: 1-2 hours

### Recommendation 3: Add Recovery Tests

Create tests for:
- Successful recovery (with and without directory)
- Task not found in archive
- Task already active (conflict)
- Directory move failure (non-critical)
- Atomic rollback on failure

**Priority**: Medium  
**Effort**: 2-3 hours

### Recommendation 4: Update Documentation

Update documentation:
- /task command usage (add --recover flag)
- status-sync-manager operations (add unarchive_task)
- Archival workflow (mention recovery option)
- Error handling guide (recovery errors)

**Priority**: Medium  
**Effort**: 1 hour

### Recommendation 5: Add Audit Trail

Track recovery in metadata:
- `recovered` timestamp
- `recovery_reason` (optional user input)
- `recovery_count` (if task recovered multiple times)

**Priority**: Low  
**Effort**: 30 minutes

---

## Risks & Mitigations

### Risk 1: Data Loss During Recovery

**Risk**: Atomic write failure could corrupt state files

**Likelihood**: Low  
**Impact**: High

**Mitigation**:
- Use two-phase commit protocol (temp files + atomic rename)
- Git-only rollback (no backup files needed)
- Comprehensive validation before writes
- Test atomic write pattern thoroughly

### Risk 2: Directory Move Failure

**Risk**: Directory move could fail due to permissions or filesystem issues

**Likelihood**: Medium  
**Impact**: Low

**Mitigation**:
- Treat directory move as non-critical
- Log warning and continue if move fails
- User can move directory manually later
- Metadata recovery is source of truth

### Risk 3: Task Number Conflict

**Risk**: Task exists in both archive and active (should never happen)

**Likelihood**: Very Low  
**Impact**: Medium

**Mitigation**:
- Validate task not in active_projects before recovery
- Abort with clear error message if conflict detected
- Provide manual resolution instructions
- Log conflict to errors.json for investigation

### Risk 4: Archive State Corruption

**Risk**: archive/state.json is missing or corrupted

**Likelihood**: Low  
**Impact**: High

**Mitigation**:
- Validate archive/state.json exists before recovery
- Validate JSON structure before parsing
- Abort with clear error if validation fails
- Provide recovery instructions (restore from git)

### Risk 5: Incomplete Recovery

**Risk**: Some files updated, others fail (partial recovery)

**Likelihood**: Low  
**Impact**: Medium

**Mitigation**:
- Atomic write pattern prevents partial updates
- All temp files written before any renames
- All renames succeed or all fail
- Git rollback available if needed

---

## Appendix: Sources and Citations

### Source 1: /task Command Specification
- **File**: `.opencode/command/task.md`
- **Key Sections**: ParseInput, CreateTasks, workflow_execution
- **Relevance**: Command structure, flag parsing, delegation pattern

### Source 2: /todo Command Specification
- **File**: `.opencode/command/todo.md`
- **Key Sections**: ScanState, GitPreCommit, RunCleanupScript, GitPostCommit
- **Relevance**: Archival workflow, git integration, atomic updates

### Source 3: todo_cleanup.py Script
- **File**: `.opencode/scripts/todo_cleanup.py`
- **Key Functions**: archive_tasks, extract_task_block, fix_divider_stacking
- **Relevance**: Archival implementation, directory moves, error handling

### Source 4: status-sync-manager Specification
- **File**: `.opencode/agent/subagents/status-sync-manager.md`
- **Key Sections**: create_task_flow, archive_tasks_flow, operation_routing
- **Relevance**: Atomic updates, two-phase commit, operation patterns

### Source 5: state.json Schema
- **File**: `.opencode/specs/state.json`
- **Key Fields**: active_projects, next_project_number, _last_updated
- **Relevance**: Active project structure, metadata fields

### Source 6: archive/state.json Schema
- **File**: `.opencode/specs/archive/state.json`
- **Key Fields**: archived_projects, archived timestamp, summary
- **Relevance**: Archived project structure, metadata preservation

### Source 7: TODO.md Structure
- **File**: `.opencode/specs/TODO.md`
- **Key Sections**: Priority sections, task entry format, dividers
- **Relevance**: TODO.md formatting, priority sections, task blocks

---

## Conclusion

The `--recover` flag for the `/task` command is a straightforward inverse of the archival process. By adding an `unarchive_task` operation to status-sync-manager and integrating it with the /task command, we can provide users with a safe, atomic way to restore archived projects.

The implementation follows established patterns:
- Atomic two-phase commit for state updates
- Git-only rollback for error recovery
- Delegation to status-sync-manager for consistency
- Comprehensive validation and error handling

The estimated effort is 4-6 hours for full implementation including tests and documentation. The feature is low-risk due to reuse of existing atomic update patterns and comprehensive error handling.

**Next Steps**:
1. Create implementation plan based on this research
2. Implement unarchive_task operation in status-sync-manager
3. Add --recover flag to /task command
4. Add tests for recovery scenarios
5. Update documentation
