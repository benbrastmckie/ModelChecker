# Implementation Plan: --recover Flag for /task Command

**Task**: 325 - Create --recover flag for /task command to unarchive projects  
**Created**: 2026-01-06  
**Status**: [NOT STARTED]  
**Estimated Effort**: 6 hours  
**Complexity**: Medium  
**Language**: meta  
**Priority**: Medium

---

## Metadata

- **Task Number**: 325
- **Project Directory**: `.opencode/specs/325_create___recover_flag_for_task_command_to_unarchive_projects/`
- **Plan Version**: 1
- **Research Integrated**: Yes
- **Dependencies**: None
- **Blocking**: None

---

## Overview

### Problem Statement

The .opencode system currently supports archiving completed/abandoned tasks via the `/todo` command, which moves project directories to `.opencode/specs/archive/`, removes entries from TODO.md and state.json, and adds them to archive/state.json. However, there is no mechanism to reverse this process and restore archived projects back to active status. This creates a one-way archival system that prevents users from recovering valuable work or revisiting completed tasks.

### Solution Approach

Implement a `--recover` flag for the `/task` command that accepts a task number as an argument (e.g., `/task --recover 123`). This flag will reverse the archival process atomically by:
1. Validating the task exists in archive/state.json
2. Moving the project directory from archive/ back to specs/
3. Removing the entry from archive/state.json
4. Adding the entry to state.json active_projects
5. Adding the entry to TODO.md in the appropriate priority section
6. Resetting status to [NOT STARTED]
7. Creating a git commit for the recovery

The implementation will add a new `unarchive_task` operation to status-sync-manager, following the same atomic two-phase commit protocol used for archival.

### Scope

**In Scope**:
- Add `--recover <task_number>` flag parsing to /task command
- Implement `unarchive_task` operation in status-sync-manager
- Atomic updates to TODO.md, state.json, and archive/state.json
- Project directory move from archive/ to specs/
- Status reset to [NOT STARTED]
- Git commit integration
- Error handling and validation
- Metadata preservation (priority, effort, language, description)

**Out of Scope**:
- Bulk recovery (multiple tasks at once)
- Status preservation (--preserve-status flag)
- Recovery reason tracking
- Recovery count tracking
- Archive integrity validation tools

### Constraints

- Must use atomic two-phase commit protocol (temp files + atomic rename)
- Must delegate to status-sync-manager for state updates
- Must delegate to git-workflow-manager for commits
- Must handle directory move failures gracefully (non-critical)
- Must validate task exists in archive before starting
- Must validate task not already in active_projects
- Must preserve original task number (no renumbering)
- Must insert task in correct priority section of TODO.md

### Definition of Done

- [NOT STARTED] /task command parses `--recover <task_number>` flag
- [NOT STARTED] status-sync-manager implements `unarchive_task` operation
- [NOT STARTED] Recovery updates TODO.md, state.json, archive/state.json atomically
- [NOT STARTED] Project directory moved from archive/ to specs/ (if exists)
- [NOT STARTED] Task status reset to [NOT STARTED]
- [NOT STARTED] Git commit created for recovery
- [NOT STARTED] Error handling for all edge cases
- [NOT STARTED] All validation checks pass
- [NOT STARTED] Manual testing confirms recovery works end-to-end

---

## Research Integration

This plan integrates findings from 1 research report created on 2026-01-06:

**Integrated Reports**:
- **research-001.md** (2026-01-06): Comprehensive analysis of archival system and recovery mechanism design
  - Key Finding: Archive system uses atomic two-phase commit with git-only rollback
  - Key Finding: 130 projects currently archived with full metadata in archive/state.json
  - Key Finding: status-sync-manager supports create_task, archive_tasks, update_status, update_task_metadata operations
  - Key Finding: Recovery requires new operation: unarchive_task
  - Recommendation: Add `--recover <task_number>` flag to /task command
  - Recommendation: Implement unarchive_task operation in status-sync-manager
  - Recommendation: Reset status to NOT STARTED by default
  - Recommendation: Treat directory move as non-critical (metadata is source of truth)
  - Recommendation: Single task recovery only (no bulk support initially)

---

## Goals and Non-Goals

### Goals

1. **Atomic Recovery**: Restore archived tasks with atomic updates across all state files
2. **Metadata Preservation**: Preserve task characteristics (priority, effort, language, description)
3. **Safe Defaults**: Reset status to NOT STARTED for clear task state
4. **Error Resilience**: Handle edge cases gracefully with clear error messages
5. **Git Integration**: Create git commits for audit trail

### Non-Goals

1. **Bulk Recovery**: Support for recovering multiple tasks at once (future enhancement)
2. **Status Preservation**: Option to preserve original status (future enhancement)
3. **Audit Trail**: Track recovery reason or recovery count (future enhancement)
4. **Archive Validation**: Tools to validate archive integrity (separate task)

---

## Risks and Mitigations

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

---

## Implementation Phases

### Phase 1: Add --recover Flag Parsing to /task Command [NOT STARTED]

**Objective**: Modify /task command to detect and parse --recover flag

**Tasks**:
1. Update /task command Stage 1 (ParseInput) to detect `--recover` flag
2. Extract task_number from next argument after --recover
3. Validate task_number is positive integer
4. Skip normal task creation flow (Stages 2-4) if --recover present
5. Add new Stage 5 (RecoverTask) for recovery workflow
6. Update command documentation with --recover usage

**Acceptance Criteria**:
- [NOT STARTED] /task command detects `--recover` flag in $ARGUMENTS
- [NOT STARTED] task_number extracted and validated as positive integer
- [NOT STARTED] Normal task creation skipped when --recover present
- [NOT STARTED] Stage 5 (RecoverTask) invoked for recovery workflow

**Estimated Effort**: 1 hour

---

### Phase 2: Implement unarchive_task Operation in status-sync-manager [NOT STARTED]

**Objective**: Add unarchive_task operation to status-sync-manager with atomic updates

**Tasks**:
1. Add `unarchive_task` to operation routing in status-sync-manager
2. Implement step_0_validate_inputs for unarchive_task:
   - Validate task_number is positive integer
   - Read archive/state.json and find task in archived_projects
   - Abort if task not found in archive
   - Read state.json and validate task not in active_projects
   - Abort if task already active
3. Implement step_1_prepare_recovery:
   - Read current TODO.md, state.json, archive/state.json
   - Format TODO.md entry from archived metadata (reset status to [NOT STARTED])
   - Format state.json entry from archived metadata (reset status/phase)
   - Remove task from archive/state.json archived_projects
   - Insert task into TODO.md (correct priority section)
   - Append task to state.json active_projects
4. Implement step_2_commit with atomic write pattern:
   - Write to temp files (TODO.md.tmp, state.json.tmp, archive/state.json.tmp)
   - Verify temp files exist and size > 0
   - Atomic rename (all or nothing)
   - Clean up temp files
5. Implement step_3_move_directory:
   - Check if directory exists in archive/
   - Move directory if exists (log warning if fails, non-critical)
   - Continue if directory doesn't exist
6. Implement step_4_return with standardized format

**Acceptance Criteria**:
- [NOT STARTED] unarchive_task operation routes correctly
- [NOT STARTED] Input validation aborts on invalid task_number or missing task
- [NOT STARTED] Conflict detection aborts if task already active
- [NOT STARTED] TODO.md entry formatted correctly with reset status
- [NOT STARTED] state.json entry formatted correctly with reset status/phase
- [NOT STARTED] Atomic write pattern prevents partial updates
- [NOT STARTED] Directory move handled gracefully (non-critical failure)
- [NOT STARTED] Return format follows subagent-return-format.md

**Estimated Effort**: 3 hours

---

### Phase 3: Integrate Recovery Workflow in /task Command [NOT STARTED]

**Objective**: Connect /task command Stage 5 to status-sync-manager unarchive_task operation

**Tasks**:
1. Implement Stage 5 (RecoverTask) in /task command:
   - Prepare delegation context for status-sync-manager
   - Set operation to "unarchive_task"
   - Include task_number, timestamp, session_id
   - Invoke status-sync-manager with 60s timeout
2. Wait for status-sync-manager return
3. Validate return:
   - Verify status == "completed"
   - Verify task_number present
   - Verify files_updated includes [TODO.md, state.json, archive/state.json]
4. Return success message to user:
   - "Task {number} recovered from archive"
   - "Status: [NOT STARTED]"
   - "Project directory: {moved/not found}"
5. Handle errors:
   - Task not found in archive
   - Task already active
   - status-sync-manager failure
   - Provide clear error messages and recovery steps

**Acceptance Criteria**:
- [NOT STARTED] Stage 5 delegates to status-sync-manager correctly
- [NOT STARTED] Delegation context includes all required fields
- [NOT STARTED] Return validation checks status and files_updated
- [NOT STARTED] Success message displays task number and status
- [NOT STARTED] Error messages are clear and actionable

**Estimated Effort**: 1 hour

---

### Phase 4: Add Git Commit Integration [NOT STARTED]

**Objective**: Create git commits for recovery operations via git-workflow-manager

**Tasks**:
1. Update status-sync-manager unarchive_task to invoke git-workflow-manager:
   - Prepare delegation context with scope_files
   - Include TODO.md, state.json, archive/state.json
   - Include recovered directory (if moved)
   - Set message_template to "task {number}: recover from archive"
2. Invoke git-workflow-manager with 120s timeout
3. Wait for git-workflow-manager return
4. Validate return:
   - If status == "completed": Extract commit_hash, log success
   - If status == "failed": Log error (non-critical), continue
5. Include git commit hash in unarchive_task return (if successful)

**Acceptance Criteria**:
- [NOT STARTED] git-workflow-manager invoked after successful recovery
- [NOT STARTED] Scope files include all updated files and directory
- [NOT STARTED] Commit message follows standard format
- [NOT STARTED] Commit hash included in return (if successful)
- [NOT STARTED] Git failure logged but doesn't fail recovery

**Estimated Effort**: 0.5 hours

---

### Phase 5: Implement Error Handling and Edge Cases [NOT STARTED]

**Objective**: Handle all edge cases gracefully with clear error messages

**Tasks**:
1. Implement validation for edge cases:
   - Task without project directory (metadata-only recovery)
   - Task number conflict (already active)
   - Partial recovery failure (atomic write prevents this)
   - Directory move failure (non-critical)
   - Archive state.json missing or corrupted
2. Add error messages for each case:
   - "Task {number} not found in archive"
   - "Task {number} already active"
   - "Archive state.json missing or corrupted"
   - "Directory move failed (non-critical): {error}"
3. Add logging for non-critical failures:
   - Directory move failures
   - Git commit failures
4. Test each edge case manually
5. Document error handling in command and subagent files

**Acceptance Criteria**:
- [NOT STARTED] Task not found error is clear and actionable
- [NOT STARTED] Task conflict error provides resolution steps
- [NOT STARTED] Archive corruption error suggests git restore
- [NOT STARTED] Directory move failure logged but doesn't abort
- [NOT STARTED] All edge cases tested manually

**Estimated Effort**: 0.5 hours

---

## Testing and Validation

### Unit Tests

**Not applicable** - This is a meta-level command implementation without unit test infrastructure.

### Integration Tests

**Manual Testing Required**:

1. **Test Case 1: Successful Recovery with Directory**
   - Archive a task with project directory
   - Run `/task --recover {number}`
   - Verify task appears in TODO.md with [NOT STARTED] status
   - Verify task appears in state.json active_projects
   - Verify task removed from archive/state.json
   - Verify directory moved from archive/ to specs/
   - Verify git commit created

2. **Test Case 2: Successful Recovery without Directory**
   - Archive a task without project directory
   - Run `/task --recover {number}`
   - Verify task appears in TODO.md and state.json
   - Verify task removed from archive/state.json
   - Verify no directory move attempted
   - Verify git commit created

3. **Test Case 3: Task Not Found in Archive**
   - Run `/task --recover 999` (non-existent task)
   - Verify error message: "Task 999 not found in archive"
   - Verify no changes to TODO.md or state.json

4. **Test Case 4: Task Already Active**
   - Create a task (don't archive)
   - Run `/task --recover {number}`
   - Verify error message: "Task {number} already active"
   - Verify no changes to state files

5. **Test Case 5: Directory Move Failure**
   - Archive a task with directory
   - Make directory read-only or move it manually
   - Run `/task --recover {number}`
   - Verify metadata recovery succeeds
   - Verify warning logged for directory move failure
   - Verify git commit created

6. **Test Case 6: Metadata Preservation**
   - Archive a task with specific priority, effort, language
   - Run `/task --recover {number}`
   - Verify priority, effort, language preserved
   - Verify status reset to [NOT STARTED]
   - Verify created date preserved

### Validation Checklist

- [NOT STARTED] All 6 test cases pass
- [NOT STARTED] Atomic updates verified (all files updated or none)
- [NOT STARTED] Git commits created for successful recoveries
- [NOT STARTED] Error messages are clear and actionable
- [NOT STARTED] Non-critical failures don't abort recovery
- [NOT STARTED] Metadata preservation verified
- [NOT STARTED] Priority section insertion verified

---

## Artifacts and Outputs

### Primary Artifacts

1. **Modified Files**:
   - `.opencode/command/task.md` - Add --recover flag parsing and Stage 5
   - `.opencode/agent/subagents/status-sync-manager.md` - Add unarchive_task operation

2. **Documentation Updates**:
   - Update /task command usage documentation
   - Update status-sync-manager operations documentation
   - Update archival workflow documentation (mention recovery)

### Secondary Artifacts

1. **Implementation Summary**:
   - `.opencode/specs/325_create___recover_flag_for_task_command_to_unarchive_projects/summaries/implementation-summary-20260106.md`

2. **Git Commits**:
   - Commit for /task command changes
   - Commit for status-sync-manager changes
   - Commit for documentation updates

---

## Rollback/Contingency

### Rollback Plan

If recovery implementation causes issues:

1. **Immediate Rollback**:
   ```bash
   git log --oneline -10  # Find commit before recovery implementation
   git revert <commit_hash>  # Revert recovery changes
   ```

2. **Partial Rollback**:
   - If only /task command has issues: Revert task.md changes
   - If only status-sync-manager has issues: Revert status-sync-manager.md changes

3. **Manual Recovery**:
   - If a recovery operation fails mid-way:
     - Check git log for pre-recovery state
     - Manually restore TODO.md, state.json, archive/state.json from git
     - Move directory manually if needed

### Contingency Plan

If atomic write pattern fails:

1. **Verify temp files exist**: Check for .tmp files in specs/
2. **Check file permissions**: Ensure write access to specs/ and archive/
3. **Validate JSON structure**: Use `jq` to validate state.json and archive/state.json
4. **Restore from git**: Use `git checkout HEAD -- <file>` to restore corrupted files

If directory move consistently fails:

1. **Document manual move procedure**: Provide instructions for manual directory recovery
2. **Add --skip-directory flag**: Future enhancement to skip directory move
3. **Investigate filesystem issues**: Check permissions, disk space, filesystem errors

---

## Success Metrics

### Quantitative Metrics

- **Recovery Success Rate**: 100% for valid archived tasks
- **Atomic Update Success**: 100% (all files updated or none)
- **Git Commit Success**: >95% (non-critical failures acceptable)
- **Directory Move Success**: >90% (non-critical failures acceptable)
- **Error Detection Rate**: 100% for invalid inputs

### Qualitative Metrics

- **User Experience**: Clear error messages, predictable behavior
- **Code Quality**: Follows existing patterns, well-documented
- **Maintainability**: Easy to extend (e.g., bulk recovery, status preservation)
- **Reliability**: Atomic updates prevent data corruption

### Acceptance Criteria

- [NOT STARTED] All 6 manual test cases pass
- [NOT STARTED] Recovery works for tasks with and without directories
- [NOT STARTED] Error handling covers all edge cases
- [NOT STARTED] Git commits created for audit trail
- [NOT STARTED] Documentation updated
- [NOT STARTED] Code follows existing patterns and standards

---

## Dependencies

### Internal Dependencies

- **status-sync-manager**: Must support new unarchive_task operation
- **git-workflow-manager**: Used for git commit creation
- **archive/state.json**: Must exist and be valid JSON
- **TODO.md**: Must have priority sections for task insertion

### External Dependencies

None

---

## Notes

### Implementation Order

1. Phase 2 (status-sync-manager) should be implemented first
2. Phase 1 (/task command flag parsing) can be done in parallel
3. Phase 3 (integration) requires Phases 1 and 2 complete
4. Phase 4 (git integration) requires Phase 2 complete
5. Phase 5 (error handling) should be done last

### Future Enhancements

1. **Bulk Recovery**: Support `/task --recover 123,124,125` or `/task --recover 123-125`
2. **Status Preservation**: Add `--preserve-status` flag to keep original status
3. **Recovery Reason**: Add optional `--reason` flag to track why task was recovered
4. **Recovery Count**: Track how many times a task has been recovered
5. **Archive Validation**: Tool to validate archive integrity and detect conflicts

### Related Tasks

- Task 323: Fix /todo command to run markdown formatter after completion
- Task 326: Create --divide flag for /task command with task division capability
- Task 328: Fix /task command to only create task entries and never implement directly

---

## Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-06 | Planner | Initial implementation plan created |
