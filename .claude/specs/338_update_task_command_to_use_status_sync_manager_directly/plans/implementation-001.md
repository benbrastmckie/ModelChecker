# Implementation Plan: Update /task Command to Use status-sync-manager Directly

- **Task**: 338 - Update /task command to use status-sync-manager directly
- **Status**: [NOT STARTED]
- **Effort**: 2-3 hours
- **Priority**: High
- **Dependencies**: None
- **Research Inputs**: Analysis of /task command routing issue (task-creator deprecated 2026-01-05)
- **Artifacts**: 
  - plans/implementation-001.md (this file)
  - .opencode/command/task.md (to be updated)
- **Standards**:
  - .opencode/context/core/formats/plan-format.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/orchestration/delegation.md
- **Type**: general
- **Lean Intent**: false

## Overview

Fix critical architectural issue in /task command where Stage 3 (CreateTasks) delegates to deprecated task-creator subagent instead of status-sync-manager directly. The task-creator was deprecated on 2026-01-05 with replacement being status-sync-manager (operation: create_task). This causes unpredictable behavior and adds unnecessary delegation layer (40-50% performance overhead).

## Goals & Non-Goals

**Goals**:
- Update Stage 3 (CreateTasks) to delegate directly to status-sync-manager
- Remove delegation to deprecated task-creator subagent
- Follow pattern from /research and /implement commands (Stage 1.5 Preflight)
- Add validation gates to verify task creation succeeded
- Test with multiple scenarios (single task, multiple tasks, inline --divide)
- Achieve 40-50% performance improvement by eliminating delegation layer

**Non-Goals**:
- Removing task-creator.md file (separate task 339)
- Updating other commands (separate task 340)
- Creating deprecation policy (separate task 341)

## Risks & Mitigations

| Risk | Mitigation |
|------|-----------|
| Breaking existing /task command | Test thoroughly with all flags (--divide, --recover, --sync, --abandon) |
| Incorrect delegation parameters | Follow status-sync-manager interface exactly (operation, task_number, title, description, priority, effort, language) |
| Missing validation gates | Add pre-execution and post-execution validation per /research pattern |

## Implementation Phases

### Phase 1: Analyze Current Delegation Pattern [NOT STARTED]
- **Goal:** Understand current task-creator delegation and status-sync-manager interface
- **Tasks:**
  - [ ] Read /task command Stage 3 (CreateTasks) - lines 175-222
  - [ ] Read task-creator.md delegation interface - lines 120-145
  - [ ] Read status-sync-manager.md create_task operation - lines 156-288
  - [ ] Compare delegation parameters (task-creator vs status-sync-manager)
  - [ ] Identify differences in return format
  - [ ] Document required changes
- **Timing:** 30 minutes

### Phase 2: Update Stage 3 Delegation [NOT STARTED]
- **Goal:** Replace task-creator delegation with status-sync-manager delegation
- **Tasks:**
  - [ ] Update Stage 3 (CreateTasks) process section:
    * Change delegation target from task-creator to status-sync-manager
    * Add operation: "create_task" parameter
    * Update delegation parameters to match status-sync-manager interface
    * Keep task_number, title, description, priority, effort, language
    * Add new_status: "not_started" parameter
    * Add timestamp parameter (ISO 8601 format)
  - [ ] Update return format validation:
    * Verify status == "completed"
    * Extract task_number from return
    * Verify files_updated includes ["TODO.md", "state.json"]
  - [ ] Update error handling:
    * Handle status-sync-manager errors (not task-creator errors)
    * Include files_updated in error details
- **Timing:** 1 hour

### Phase 3: Add Validation Gates [NOT STARTED]
- **Goal:** Add pre-execution and post-execution validation gates
- **Tasks:**
  - [ ] Add pre-execution validation in Stage 3:
    * Verify state.json exists and is readable
    * Verify TODO.md exists and is readable
    * Verify all required parameters present (title, description, priority, effort, language)
    * Verify language is valid value
  - [ ] Add post-execution validation in Stage 3:
    * Verify task_number returned is positive integer
    * Verify files_updated includes both TODO.md and state.json
    * Verify no artifacts created (architectural constraint)
    * Verify task entry exists in TODO.md
    * Verify task entry exists in state.json
  - [ ] Add validation error handling:
    * Return clear error messages
    * Include validation failure details
    * Suggest recovery steps
- **Timing:** 45 minutes

### Phase 4: Test All Scenarios [NOT STARTED]
- **Goal:** Verify /task command works correctly with all flags
- **Tasks:**
  - [ ] Test single task creation:
    * /task "Test task description"
    * Verify task created in TODO.md and state.json
    * Verify task number incremented
    * Verify no artifacts created
  - [ ] Test task creation with flags:
    * /task "Test task" --priority High --effort "2 hours" --language lean
    * Verify all metadata fields set correctly
  - [ ] Test inline --divide:
    * /task "Task 1, Task 2, Task 3" --divide
    * Verify 3 tasks created
    * Verify all have same priority/effort/language
  - [ ] Test other flags (--recover, --sync, --abandon):
    * Verify these still work (they don't use task-creator)
  - [ ] Measure performance improvement:
    * Time task creation before and after
    * Verify 40-50% improvement
- **Timing:** 45 minutes

## Testing & Validation

- [ ] All test scenarios pass
- [ ] Task creation works for single and multiple tasks
- [ ] All flags work correctly (--divide, --recover, --sync, --abandon)
- [ ] Validation gates prevent invalid operations
- [ ] Performance improved by 40-50%
- [ ] No regression in existing functionality
- [ ] Error messages are clear and actionable

## Artifacts & Outputs

- Updated .opencode/command/task.md (Stage 3 rewritten)
- Test results documenting all scenarios
- Performance comparison (before/after)

## Rollback/Contingency

If update fails:
- Revert .opencode/command/task.md to previous version
- Use git to restore original file
- Document failure reason
- Create new task to investigate root cause
