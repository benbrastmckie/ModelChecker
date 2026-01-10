# Research Report: Comprehensive /task Command Enhancements

**Task**: 332 - Design and implement comprehensive /task command enhancements  
**Started**: 2026-01-07  
**Completed**: 2026-01-07  
**Effort**: 18-24 hours (estimated)  
**Priority**: Medium  
**Dependencies**: 325, 326, 322, 330  
**Sources/Inputs**:
- .opencode/specs/325_create___recover_flag_for_task_command_to_unarchive_projects/reports/research-001.md
- .opencode/specs/325_create___recover_flag_for_task_command_to_unarchive_projects/plans/implementation-001.md
- .opencode/specs/326_create___divide_flag_for_task_command_with_task_division_capability/reports/research-001.md
- .opencode/command/task.md (current /task command implementation)
- .opencode/agent/subagents/status-sync-manager.md (atomic state synchronization)
- .opencode/specs/state.json (task metadata structure)
- .opencode/specs/TODO.md (user-facing task list)

**Artifacts**: .opencode/specs/332_design_and_implement_comprehensive_task_command_enhancements/reports/research-001.md  
**Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

---

## Executive Summary

This research analyzes four dependency tasks (325, 326, 322, 330) to design a unified architecture for comprehensive /task command enhancements. The goal is to consolidate these features into a cohesive implementation that avoids conflicts, ensures architectural consistency, and improves the integrity of the /task command through atomic operations, proper error handling, and integration with existing status-sync-manager patterns.

**Key Findings**:
1. **Task 325 (--recover)**: Unarchive projects from specs/archive/ - 6 hours, PLANNED, comprehensive research and plan complete
2. **Task 326 (--divide)**: Divide existing tasks into subtasks with dependencies - 12-17 hours, RESEARCHED, comprehensive research complete
3. **Task 322 (bulk operations)**: Add bulk create/update operations to status-sync-manager - TBD effort, NOT STARTED, no research
4. **Task 330 (--sync)**: Synchronize TODO.md and state.json with optional task ranges - TBD effort, NOT STARTED, no research
5. **Common Patterns**: All features require atomic operations, status-sync-manager delegation, git integration, error handling
6. **Potential Conflicts**: Task number allocation, concurrent operations, rollback complexity, state file locking
7. **Architectural Consistency**: Two-phase commit protocol, temp file pattern, git-only rollback, standardized return format

**Recommended Approach**: Implement features in dependency order (325 → 326 → 322 → 330), establish shared infrastructure for atomic operations and bulk processing, create unified error handling framework, and ensure all features integrate seamlessly with existing status-sync-manager patterns.

---

## Context & Scope

### Dependency Task Analysis

#### Task 325: --recover Flag (PLANNED)

**Status**: PLANNED (research and implementation plan complete)  
**Effort**: 6 hours  
**Complexity**: Medium

**Purpose**: Unarchive projects from specs/archive/ back to active status

**Key Requirements**:
- Accept task number: `/task --recover 123`
- Validate task exists in archive/state.json
- Move project directory from archive/ to specs/
- Remove entry from archive/state.json
- Add entry to state.json active_projects
- Add entry to TODO.md in appropriate priority section
- Reset status to [NOT STARTED]
- Create git commit for recovery

**Implementation Approach**:
- Add `unarchive_task` operation to status-sync-manager
- Use atomic two-phase commit protocol
- Treat directory move as non-critical (metadata is source of truth)
- Single task recovery only (no bulk support initially)

**Research Completeness**: [PASS] - Comprehensive research report (791 lines) and implementation plan (544 lines) complete

#### Task 326: --divide Flag (RESEARCHED)

**Status**: RESEARCHED (comprehensive research complete, no plan yet)  
**Effort**: 12-17 hours  
**Complexity**: Medium-High

**Purpose**: Divide existing tasks into subtasks with automatic dependency tracking

**Key Requirements**:
- Accept task number: `/task --divide 326 [optional prompt]`
- Validate task exists and allows division
- Analyze task description for natural divisions (1-5 subtasks)
- Allocate N task numbers sequentially
- Create N subtasks atomically via status-sync-manager
- Update parent task with subtask dependencies
- Rollback on partial failure
- Create git commit for all changes

**Implementation Approach**:
- Reuse existing division logic from `/task "description" --divide`
- Add task analysis for existing tasks (read from state.json)
- Implement rollback mechanism for atomic subtask creation
- Add dependency management to status-sync-manager
- Parent depends on subtasks (not vice versa)

**Research Completeness**: [PASS] - Comprehensive research report (1136 lines) with detailed analysis, code examples, and effort estimation

#### Task 322: Bulk Operations (NOT STARTED)

**Status**: NOT STARTED (no research or plan)  
**Effort**: TBD  
**Complexity**: Unknown

**Purpose**: Add bulk create/update operations to status-sync-manager for elegant executions

**Key Requirements** (inferred from description):
- Bulk task creation (create multiple tasks in one operation)
- Bulk task updates (update multiple tasks in one operation)
- Integration with existing bulk functionality (/abandon, /task --divide)
- Optimization for performance and atomicity

**Implementation Approach** (to be researched):
- Extend status-sync-manager with `bulk_create_tasks` operation
- Extend status-sync-manager with `bulk_update_tasks` operation
- Atomic updates across all tasks (all or nothing)
- Efficient state file updates (single write cycle)

**Research Completeness**: [FAIL] - No research conducted, requirements unclear

#### Task 330: --sync Flag (NOT STARTED)

**Status**: NOT STARTED (no research or plan)  
**Effort**: TBD  
**Complexity**: Unknown

**Purpose**: Synchronize TODO.md and state.json with optional task ranges

**Key Requirements** (from description):
- Accept optional task ranges: `/task --sync 343-345,337`
- Sync all tasks if no numbers provided: `/task --sync`
- Improve upon current /sync command implementation
- Avoid needless complexity, omit dry-run mode

**Implementation Approach** (to be researched):
- Detect discrepancies between TODO.md and state.json
- Resolve conflicts by preferring most recently updated data
- Perform atomic updates using status-sync-manager
- Support range/list parsing (reuse patterns from task 311)

**Research Completeness**: [FAIL] - No research conducted, requirements unclear

### Current /task Command Architecture

The current `/task` command (`.opencode/command/task.md`) implements:

**Stage 1: ParseInput**
- Extract description from $ARGUMENTS
- Extract flags: --priority, --effort, --language, --divide
- Validate inputs

**Stage 2: ReformulateDescription**
- Clean and normalize description
- Ensure proper sentence structure
- Generate title from description
- Detect language from keywords

**Stage 3: DivideIfRequested**
- Check if --divide flag present (for NEW tasks only)
- Analyze description for natural divisions
- Determine number of subtasks (1-5)
- Generate subtask descriptions

**Stage 4: CreateTasks**
- For each task in task_list:
  - Delegate to status-sync-manager (create_task operation)
  - Collect task_number from return
  - Handle errors with rollback

**Stage 5: ReturnSuccess**
- Format success message
- Return task numbers to user
- Provide next steps

**Limitations**:
- No --recover flag (task 325)
- No --divide TASK_NUMBER for existing tasks (task 326)
- No --sync flag (task 330)
- No bulk operations support (task 322)

### Current status-sync-manager Architecture

The status-sync-manager (`.opencode/agent/subagents/status-sync-manager.md`) implements:

**Operations**:
- `create_task`: Create single task entry
- `archive_tasks`: Archive multiple tasks (bulk operation)
- `update_status`: Update task status
- `update_task_metadata`: Update task fields

**Atomic Write Pattern**:
1. Prepare updates in memory
2. Write to temp files with session_id
3. Verify temp files exist and size > 0
4. Atomic rename (all or nothing)
5. Clean up temp files

**Limitations**:
- No `unarchive_task` operation (needed for task 325)
- No bulk create operation (needed for task 322)
- No bulk update operation (needed for task 322)
- No sync operation (needed for task 330)
- No dependency management in update_task_metadata (needed for task 326)

---

## Key Findings

### Finding 1: Common Architectural Patterns

All four dependency tasks share common architectural patterns:

**Atomic Operations**:
- Two-phase commit protocol (temp files + atomic rename)
- All files updated or none (rollback on failure)
- Git-only rollback (no backup files)

**status-sync-manager Delegation**:
- All features delegate to status-sync-manager for state updates
- Standardized return format (subagent-return-format.md)
- Error handling with clear messages

**Git Integration**:
- All features create git commits via git-workflow-manager
- Scoped commits (only affected files)
- Non-critical git failures (log warning, continue)

**Error Handling**:
- Input validation before operations
- Clear error messages with recovery steps
- Graceful degradation for non-critical failures

**Implications**:
- Can create shared infrastructure for atomic operations
- Can standardize error handling across all features
- Can reuse git integration patterns
- Can ensure consistent user experience

### Finding 2: Potential Conflicts and Dependencies

**Task Number Allocation Conflicts**:
- Task 326 (--divide) allocates N sequential task numbers
- Task 322 (bulk operations) may allocate M task numbers
- Concurrent operations could allocate same numbers
- **Mitigation**: Use state.json next_project_number as single source of truth, atomic updates via temp file pattern

**State File Locking**:
- Multiple concurrent /task operations could conflict
- status-sync-manager uses temp files but no explicit locking
- **Mitigation**: Session-based temp files prevent conflicts, atomic rename ensures consistency

**Rollback Complexity**:
- Task 326 (--divide) requires rollback if subtask creation fails
- Task 322 (bulk operations) requires rollback if any task fails
- Nested rollbacks could be complex
- **Mitigation**: Implement rollback at status-sync-manager level, track created tasks for cleanup

**Dependency Management**:
- Task 326 (--divide) adds dependencies to parent task
- Task 322 (bulk operations) may need to update dependencies
- Task 330 (--sync) may need to sync dependencies
- **Mitigation**: Extend update_task_metadata to support dependency updates, validate no circular dependencies

**Implications**:
- Need careful coordination of task number allocation
- Need to ensure atomic operations across all features
- Need comprehensive rollback mechanisms
- Need dependency validation and conflict detection

### Finding 3: Implementation Order and Dependencies

**Dependency Graph**:
```
Task 325 (--recover)
  ↓ (no dependencies)
  
Task 326 (--divide)
  ↓ (depends on dependency management)
  
Task 322 (bulk operations)
  ↓ (needed by --divide for efficiency)
  
Task 330 (--sync)
  ↓ (depends on all features for comprehensive sync)
```

**Recommended Implementation Order**:
1. **Task 325 (--recover)**: Independent, well-researched, clear requirements
2. **Task 322 (bulk operations)**: Needed by --divide for efficient subtask creation
3. **Task 326 (--divide)**: Depends on bulk operations for performance
4. **Task 330 (--sync)**: Depends on all features for comprehensive sync

**Rationale**:
- Task 325 is independent and can be implemented first
- Task 322 provides infrastructure for task 326
- Task 326 benefits from bulk operations for atomic subtask creation
- Task 330 should be last to sync all new features

**Implications**:
- Can implement features incrementally
- Can test each feature independently
- Can ensure later features build on earlier infrastructure
- Can avoid rework by establishing patterns early

### Finding 4: Shared Infrastructure Opportunities

**Atomic Operation Framework**:
- All features use two-phase commit protocol
- Can create shared atomic write utilities
- Can standardize temp file naming (session_id pattern)
- Can centralize rollback logic

**Bulk Processing Framework**:
- Task 322 (bulk operations) provides foundation
- Task 326 (--divide) uses bulk creation for subtasks
- Task 330 (--sync) uses bulk updates for sync
- Can create shared bulk processing utilities

**Error Handling Framework**:
- All features need input validation
- All features need clear error messages
- All features need graceful degradation
- Can create shared error handling utilities

**Git Integration Framework**:
- All features create git commits
- All features use git-workflow-manager
- All features handle git failures gracefully
- Can create shared git integration utilities

**Implications**:
- Can reduce code duplication
- Can ensure consistency across features
- Can simplify maintenance and testing
- Can improve reliability through shared code

### Finding 5: status-sync-manager Extension Requirements

**New Operations Needed**:

1. **unarchive_task** (for task 325):
   - Validate task exists in archive/state.json
   - Move task from archive to active
   - Update TODO.md, state.json, archive/state.json atomically
   - Move directory from archive/ to specs/

2. **bulk_create_tasks** (for task 322):
   - Accept array of task objects
   - Allocate N sequential task numbers
   - Create all tasks atomically (all or nothing)
   - Single write cycle for efficiency

3. **bulk_update_tasks** (for task 322):
   - Accept array of task updates
   - Update all tasks atomically (all or nothing)
   - Single write cycle for efficiency

4. **sync_tasks** (for task 330):
   - Detect discrepancies between TODO.md and state.json
   - Resolve conflicts by timestamp
   - Update both files atomically
   - Support task range filtering

**Operation Extensions Needed**:

1. **update_task_metadata** (for task 326):
   - Support dependencies field updates
   - Validate no circular dependencies
   - Support blocking/blocking_reason updates

**Implications**:
- status-sync-manager will grow significantly
- Need to maintain atomic guarantees across all operations
- Need comprehensive testing for all operations
- Need clear documentation for all operations

### Finding 6: Argument Parsing Complexity

**Current Parsing**:
- Simple flag extraction (--priority, --effort, --language, --divide)
- No complex argument patterns

**New Parsing Requirements**:

1. **--recover TASK_NUMBER** (task 325):
   - Pattern: `--recover 123`
   - Extract task number after flag
   - Validate positive integer

2. **--divide TASK_NUMBER [OPTIONAL_PROMPT]** (task 326):
   - Pattern: `--divide 326 "Focus on implementation phases"`
   - Extract task number and optional prompt
   - Validate task number, allow arbitrary prompt

3. **--sync [TASK_RANGES]** (task 330):
   - Pattern: `--sync 343-345,337` or `--sync`
   - Parse ranges and lists (reuse task 311 patterns)
   - Validate task numbers exist

**Parsing Challenges**:
- Multiple flag patterns with different argument structures
- Optional arguments after flags
- Range/list parsing complexity
- Backward compatibility with existing flags

**Implications**:
- Need robust argument parsing logic
- Need clear error messages for invalid syntax
- Need comprehensive validation
- Need to maintain backward compatibility

### Finding 7: Testing and Validation Requirements

**Unit Testing**:
- Not applicable (meta-level command implementation)

**Integration Testing** (manual):

1. **Task 325 (--recover)**:
   - Successful recovery with/without directory
   - Task not found in archive
   - Task already active
   - Directory move failure
   - Metadata preservation

2. **Task 326 (--divide)**:
   - Successful division (2-5 subtasks)
   - Task not found
   - Task already divided
   - Task too simple (no divisions)
   - Subtask creation partial failure (rollback)
   - Parent task update failure

3. **Task 322 (bulk operations)**:
   - Bulk create success (N tasks)
   - Bulk create partial failure (rollback)
   - Bulk update success (N tasks)
   - Bulk update partial failure (rollback)

4. **Task 330 (--sync)**:
   - Sync all tasks (no discrepancies)
   - Sync with discrepancies (TODO.md vs state.json)
   - Sync specific ranges
   - Conflict resolution by timestamp

**Validation Checklist**:
- All features work independently
- All features work together (no conflicts)
- Atomic operations verified (all or nothing)
- Git commits created for all operations
- Error messages clear and actionable
- Rollback mechanisms work correctly

**Implications**:
- Need comprehensive manual testing
- Need to test feature interactions
- Need to test edge cases and failures
- Need to document test procedures

---

## Detailed Analysis

### Unified Architecture Design

**Command Structure**:
```
/task [DESCRIPTION] [FLAGS]

Flags:
  --priority Low|Medium|High    Set task priority (default: Medium)
  --effort ESTIMATE             Set effort estimate (default: TBD)
  --language LANG               Set task language (default: auto-detect)
  --divide                      Divide new task into subtasks (existing)
  --divide TASK_NUMBER [PROMPT] Divide existing task into subtasks (NEW - task 326)
  --recover TASK_NUMBER         Recover archived task (NEW - task 325)
  --sync [TASK_RANGES]          Sync TODO.md and state.json (NEW - task 330)
```

**Stage Flow**:
```
Stage 1: ParseInput
  ├─ Detect flag type (create, divide, recover, sync)
  ├─ Extract flag-specific arguments
  ├─ Validate inputs
  └─ Route to appropriate stage

Stage 2: ReformulateDescription (create mode only)
  ├─ Clean and normalize
  ├─ Generate title
  └─ Detect language

Stage 3: DivideIfRequested (create mode with --divide only)
  ├─ Analyze description
  ├─ Determine subtasks
  └─ Prepare task list

Stage 4: CreateTasks (create mode)
  ├─ Delegate to status-sync-manager
  ├─ Collect task numbers
  └─ Handle errors

Stage 5: DivideExistingTask (--divide TASK_NUMBER mode)
  ├─ Validate parent task
  ├─ Analyze for divisions
  ├─ Allocate task numbers
  ├─ Create subtasks (bulk operation)
  ├─ Update parent dependencies
  └─ Create git commit

Stage 6: RecoverTask (--recover mode)
  ├─ Validate task in archive
  ├─ Delegate to status-sync-manager (unarchive_task)
  ├─ Validate return
  └─ Return success

Stage 7: SyncTasks (--sync mode)
  ├─ Parse task ranges (if provided)
  ├─ Delegate to status-sync-manager (sync_tasks)
  ├─ Validate return
  └─ Return sync summary

Stage 8: ReturnSuccess
  ├─ Format success message
  ├─ Return task numbers/summary
  └─ Provide next steps
```

### status-sync-manager Extension Design

**New Operations**:

1. **unarchive_task** (task 325):
```markdown
<unarchive_task_flow>
  <step_0_validate_inputs>
    - Validate task_number is positive integer
    - Read archive/state.json, find task
    - Abort if not found
    - Read state.json, validate not already active
    - Abort if already active
  </step_0_validate_inputs>

  <step_1_prepare_recovery>
    - Read TODO.md, state.json, archive/state.json
    - Format TODO.md entry (reset status to [NOT STARTED])
    - Format state.json entry (reset status/phase)
    - Remove from archive/state.json
    - Insert into TODO.md (correct priority section)
    - Append to state.json active_projects
  </step_1_prepare_recovery>

  <step_2_commit>
    - Write to temp files (TODO.md.tmp, state.json.tmp, archive/state.json.tmp)
    - Verify temp files
    - Atomic rename (all or nothing)
    - Clean up temp files
  </step_2_commit>

  <step_3_move_directory>
    - Check if directory exists in archive/
    - Move if exists (log warning if fails, non-critical)
    - Continue if doesn't exist
  </step_3_move_directory>

  <step_4_return>
    - Return task_number, files_updated, directory_moved
  </step_4_return>
</unarchive_task_flow>
```

2. **bulk_create_tasks** (task 322):
```markdown
<bulk_create_tasks_flow>
  <step_0_validate_inputs>
    - Validate tasks is non-empty array
    - For each task: validate title, description, priority, effort, language
    - Read next_project_number from state.json
    - Allocate N sequential task numbers
    - Validate no conflicts
  </step_0_validate_inputs>

  <step_1_prepare_entries>
    - For each task: generate slug, format TODO.md entry, format state.json entry
    - Validate all entries well-formed
  </step_1_prepare_entries>

  <step_2_prepare_update>
    - Read current TODO.md and state.json
    - Insert all TODO.md entries (correct priority sections)
    - Append all entries to active_projects array
    - Increment next_project_number by N
    - Update _last_updated timestamp
  </step_2_prepare_update>

  <step_3_commit>
    - Write to temp files (single write cycle)
    - Verify temp files
    - Atomic rename (all or nothing)
    - Clean up temp files
  </step_3_commit>

  <step_4_return>
    - Return array of task_numbers created
  </step_4_return>
</bulk_create_tasks_flow>
```

3. **bulk_update_tasks** (task 322):
```markdown
<bulk_update_tasks_flow>
  <step_0_validate_inputs>
    - Validate updates is non-empty array
    - For each update: validate task_number exists, validate updated_fields
    - Read state.json, verify all tasks exist
  </step_0_validate_inputs>

  <step_1_prepare_updates>
    - Read current TODO.md and state.json
    - For each update: apply changes to TODO.md entry and state.json entry
    - Validate all updates well-formed
  </step_1_prepare_updates>

  <step_2_commit>
    - Write to temp files (single write cycle)
    - Verify temp files
    - Atomic rename (all or nothing)
    - Clean up temp files
  </step_2_commit>

  <step_3_return>
    - Return array of task_numbers updated
  </step_3_return>
</bulk_update_tasks_flow>
```

4. **sync_tasks** (task 330):
```markdown
<sync_tasks_flow>
  <step_0_validate_inputs>
    - Validate task_numbers is array or null (null = sync all)
    - If array: validate all task numbers are positive integers
  </step_0_validate_inputs>

  <step_1_detect_discrepancies>
    - Read TODO.md and state.json
    - Parse all tasks from both files
    - For each task (or filtered by task_numbers):
      * Compare status, priority, effort, language, description
      * Detect discrepancies
      * Determine source of truth (most recent last_updated)
  </step_1_detect_discrepancies>

  <step_2_prepare_sync>
    - For each discrepancy:
      * Update TODO.md entry from state.json (or vice versa)
      * Preserve most recent data
    - Validate all updates well-formed
  </step_2_prepare_sync>

  <step_3_commit>
    - Write to temp files (single write cycle)
    - Verify temp files
    - Atomic rename (all or nothing)
    - Clean up temp files
  </step_3_commit>

  <step_4_return>
    - Return sync_summary: {tasks_synced, discrepancies_resolved}
  </step_4_return>
</sync_tasks_flow>
```

**Operation Extension**:

**update_task_metadata** (for task 326):
```markdown
<update_task_metadata_flow>
  <!-- Existing steps 0-2 unchanged -->

  <step_2_prepare_update>
    <!-- Existing logic -->
    
    <!-- NEW: Dependency management -->
    - If updated_fields contains "dependencies":
      * Validate dependencies is array of positive integers
      * Validate all dependency task numbers exist in state.json
      * Detect circular dependencies (task depends on itself, or A→B→A)
      * Abort if circular dependency detected
      * Update dependencies field in state.json entry
      * Update TODO.md entry with dependencies
  </step_2_prepare_update>

  <!-- Existing steps 3-4 unchanged -->
</update_task_metadata_flow>
```

### Argument Parsing Strategy

**Unified Parsing Logic**:
```bash
# Stage 1: ParseInput

# Detect flag type
if [[ "$ARGUMENTS" =~ ^--recover[[:space:]]+([0-9]+) ]]; then
  # --recover mode
  mode="recover"
  task_number="${BASH_REMATCH[1]}"
  
elif [[ "$ARGUMENTS" =~ ^--divide[[:space:]]+([0-9]+)(.*)$ ]]; then
  # --divide TASK_NUMBER mode
  mode="divide_existing"
  task_number="${BASH_REMATCH[1]}"
  optional_prompt="${BASH_REMATCH[2]}"
  optional_prompt=$(echo "$optional_prompt" | xargs)  # trim
  
elif [[ "$ARGUMENTS" =~ ^--sync(.*)$ ]]; then
  # --sync mode
  mode="sync"
  task_ranges="${BASH_REMATCH[1]}"
  task_ranges=$(echo "$task_ranges" | xargs)  # trim
  
elif [[ "$ARGUMENTS" =~ --divide ]]; then
  # --divide mode (new task creation)
  mode="create"
  divide=true
  # Extract description before --divide
  description=$(echo "$ARGUMENTS" | sed 's/--divide.*//' | xargs)
  
else
  # Normal create mode
  mode="create"
  divide=false
  # Extract description before first --flag
  description=$(echo "$ARGUMENTS" | sed 's/--[a-z].*//' | xargs)
fi

# Route to appropriate stage based on mode
case "$mode" in
  create)
    # Continue to Stage 2 (ReformulateDescription)
    ;;
  divide_existing)
    # Skip to Stage 5 (DivideExistingTask)
    ;;
  recover)
    # Skip to Stage 6 (RecoverTask)
    ;;
  sync)
    # Skip to Stage 7 (SyncTasks)
    ;;
esac
```

### Rollback Mechanism Design

**Rollback Levels**:

1. **status-sync-manager Level** (atomic write pattern):
   - Temp files written but rename fails
   - Solution: Remove temp files, return failed status
   - No state changes committed

2. **Bulk Operation Level** (task 322):
   - Some tasks created, then failure
   - Solution: Delete created tasks via bulk_delete_tasks operation
   - Restore next_project_number

3. **Subtask Creation Level** (task 326):
   - Some subtasks created, then failure
   - Solution: Delete created subtasks via bulk_delete_tasks
   - Do not update parent task dependencies

**Rollback Implementation**:
```markdown
<rollback_mechanism>
  <track_created_tasks>
    - Maintain array of created task numbers during operation
    - Example: created_tasks = [327, 328, 329]
  </track_created_tasks>

  <detect_failure>
    - If any operation fails (status != "completed")
    - Log error with details
    - Initiate rollback
  </detect_failure>

  <execute_rollback>
    - For each task in created_tasks:
      * Delegate to status-sync-manager (delete_task operation)
      * Remove from TODO.md and state.json
      * Log rollback action
    - Restore next_project_number (decrement by length of created_tasks)
    - Return failed status with rollback summary
  </execute_rollback>

  <rollback_validation>
    - Verify all created tasks removed
    - Verify next_project_number restored
    - Verify state files consistent
  </rollback_validation>
</rollback_mechanism>
```

**Note**: Requires new `delete_task` operation in status-sync-manager for rollback support.

### Error Handling Framework

**Error Categories**:

1. **Input Validation Errors**:
   - Invalid task number
   - Invalid flag syntax
   - Missing required arguments
   - **Response**: Clear error message, usage example, abort

2. **State Validation Errors**:
   - Task not found
   - Task already exists
   - Invalid status for operation
   - **Response**: Clear error message, current state, abort

3. **Operation Errors**:
   - status-sync-manager failure
   - Git commit failure
   - Directory move failure
   - **Response**: Error details, rollback if needed, recovery steps

4. **Conflict Errors**:
   - Circular dependency
   - Task number conflict
   - Concurrent operation conflict
   - **Response**: Conflict details, resolution steps, abort

**Error Message Template**:
```
Error: {error_type}

Details: {error_details}

Current State:
  - Task Number: {number}
  - Status: {status}
  - {other_relevant_state}

Recovery Steps:
  1. {step_1}
  2. {step_2}
  3. {step_3}

For help: /task --help
```

### Git Integration Strategy

**Git Commit Patterns**:

1. **Task 325 (--recover)**:
   - Message: `task {number}: recover from archive`
   - Scope: TODO.md, state.json, archive/state.json, recovered directory

2. **Task 326 (--divide)**:
   - Message: `task {number}: divide into {N} subtasks ({first}-{last})`
   - Scope: TODO.md, state.json

3. **Task 322 (bulk operations)**:
   - Message: `task: bulk create {N} tasks ({first}-{last})`
   - Scope: TODO.md, state.json

4. **Task 330 (--sync)**:
   - Message: `task: sync {N} tasks (resolved {M} discrepancies)`
   - Scope: TODO.md, state.json

**Git Integration via git-workflow-manager**:
```markdown
<git_integration>
  <prepare_delegation>
    - scope_files: [list of affected files]
    - message_template: {commit message}
    - task_context: {task_number, description}
    - session_id: {session_id}
    - delegation_depth: {depth + 1}
  </prepare_delegation>

  <invoke_git_workflow_manager>
    - Timeout: 120s
    - Wait for return
  </invoke_git_workflow_manager>

  <validate_return>
    - If status == "completed": Extract commit_hash, log success
    - If status == "failed": Log error (non-critical), continue
  </validate_return>

  <include_in_return>
    - Add commit_hash to return object (if successful)
    - Add git_status to return object (completed/failed)
  </include_in_return>
</git_integration>
```

---

## Decisions

### Decision 1: Implementation Order

**Question**: In what order should the four features be implemented?

**Options**:
1. Dependency order: 325 → 326 → 322 → 330
2. Complexity order: 325 → 322 → 326 → 330
3. Value order: 326 → 325 → 330 → 322
4. Parallel implementation: All at once

**Decision**: Dependency order (325 → 322 → 326 → 330)

**Rationale**:
- Task 325 is independent and well-researched (can start immediately)
- Task 322 provides infrastructure for task 326 (bulk operations for subtasks)
- Task 326 benefits from bulk operations for atomic subtask creation
- Task 330 should be last to sync all new features
- Sequential implementation reduces risk of conflicts
- Can test each feature independently before moving to next

### Decision 2: Bulk Operations Scope

**Question**: What should bulk operations support?

**Options**:
1. Bulk create only
2. Bulk create and bulk update
3. Bulk create, bulk update, and bulk delete
4. Full CRUD operations (create, read, update, delete)

**Decision**: Bulk create, bulk update, and bulk delete (Option 3)

**Rationale**:
- Bulk create needed for task 326 (subtask creation)
- Bulk update needed for task 330 (sync operations)
- Bulk delete needed for rollback mechanism
- Read operations don't need bulk support (single file read)
- Provides complete set of operations for all features

### Decision 3: Rollback Strategy

**Question**: How should rollback be handled for partial failures?

**Options**:
1. No rollback (keep partial changes)
2. Manual rollback (user fixes via git)
3. Automatic rollback (delete created tasks)
4. Checkpoint rollback (restore from checkpoint)

**Decision**: Automatic rollback via bulk delete (Option 3)

**Rationale**:
- Atomic guarantee: all tasks created or none
- Prevents partial division (confusing state)
- Clean rollback (no orphaned tasks)
- User can retry operation after fixing issue
- Requires bulk_delete_tasks operation in status-sync-manager

### Decision 4: Dependency Direction

**Question**: For task division, should parent depend on subtasks or vice versa?

**Options**:
1. Parent depends on subtasks
2. Subtasks depend on parent
3. Bidirectional dependencies
4. No dependencies (just metadata link)

**Decision**: Parent depends on subtasks (Option 1)

**Rationale**:
- Parent cannot be implemented until subtasks complete
- Standard dependency model (task depends on prerequisites)
- Automatic blocking detection
- Clear dependency chain for task ordering
- Matches task 326 research recommendation

### Decision 5: Sync Conflict Resolution

**Question**: How should conflicts be resolved during sync?

**Options**:
1. Prefer TODO.md (user-facing)
2. Prefer state.json (authoritative)
3. Prefer most recent (by timestamp)
4. Ask user to resolve manually

**Decision**: Prefer most recent by timestamp (Option 3)

**Rationale**:
- Most recent data is likely correct
- Automatic resolution (no user intervention)
- Consistent with architectural principle (state.json is authoritative for reads)
- Can be overridden manually if needed

---

## Recommendations

### Recommendation 1: Implement Task 325 First (--recover)

**Priority**: High  
**Effort**: 6 hours  
**Dependencies**: None

**Rationale**:
- Independent feature (no dependencies on other tasks)
- Well-researched with comprehensive plan
- Clear requirements and implementation approach
- Provides immediate value (recover archived tasks)
- Establishes patterns for other features

**Action Items**:
1. Implement unarchive_task operation in status-sync-manager (3 hours)
2. Add --recover flag parsing to /task command (1 hour)
3. Integrate recovery workflow (1 hour)
4. Add git commit integration (0.5 hours)
5. Implement error handling and edge cases (0.5 hours)

### Recommendation 2: Research and Implement Task 322 Second (Bulk Operations)

**Priority**: High  
**Effort**: 8-12 hours (estimated)  
**Dependencies**: None

**Rationale**:
- Provides infrastructure for task 326 (subtask creation)
- Needed for efficient bulk operations
- Establishes patterns for atomic multi-task operations
- Enables rollback mechanism for task 326

**Action Items**:
1. Research bulk operations requirements (2-3 hours)
2. Implement bulk_create_tasks operation (2-3 hours)
3. Implement bulk_update_tasks operation (2-3 hours)
4. Implement bulk_delete_tasks operation (1-2 hours)
5. Add comprehensive testing (1-2 hours)

### Recommendation 3: Implement Task 326 Third (--divide)

**Priority**: High  
**Effort**: 12-17 hours  
**Dependencies**: Task 322 (bulk operations)

**Rationale**:
- Well-researched with detailed analysis
- Benefits from bulk operations for atomic subtask creation
- Provides significant value (divide complex tasks)
- Establishes dependency management patterns

**Action Items**:
1. Add --divide TASK_NUMBER flag parsing (2-3 hours)
2. Implement task analysis for existing tasks (3-4 hours)
3. Implement atomic subtask creation with rollback (3-4 hours)
4. Implement dependency management (2-3 hours)
5. Add git integration and testing (2-3 hours)

### Recommendation 4: Research and Implement Task 330 Last (--sync)

**Priority**: Medium  
**Effort**: 6-10 hours (estimated)  
**Dependencies**: Tasks 325, 322, 326

**Rationale**:
- Depends on all features for comprehensive sync
- Provides value for maintaining consistency
- Can sync all new features (recover, divide, bulk)
- Should be last to ensure all features work correctly

**Action Items**:
1. Research sync requirements and conflict resolution (2-3 hours)
2. Implement sync_tasks operation (2-3 hours)
3. Add --sync flag parsing with range support (1-2 hours)
4. Implement conflict resolution by timestamp (1-2 hours)

### Recommendation 5: Create Shared Infrastructure

**Priority**: High  
**Effort**: 4-6 hours  
**Dependencies**: None (can be done in parallel with task 325)

**Rationale**:
- Reduces code duplication
- Ensures consistency across features
- Simplifies maintenance and testing
- Improves reliability through shared code

**Action Items**:
1. Create atomic operation utilities (1-2 hours)
2. Create bulk processing utilities (1-2 hours)
3. Create error handling framework (1-2 hours)
4. Document shared infrastructure (1 hour)

### Recommendation 6: Add Comprehensive Testing

**Priority**: High  
**Effort**: 6-8 hours  
**Dependencies**: All features implemented

**Rationale**:
- Ensures all features work independently
- Ensures all features work together (no conflicts)
- Validates atomic operations and rollback
- Provides confidence for production use

**Action Items**:
1. Create test plan for all features (1 hour)
2. Test task 325 (--recover) scenarios (1-2 hours)
3. Test task 322 (bulk operations) scenarios (1-2 hours)
4. Test task 326 (--divide) scenarios (1-2 hours)
5. Test task 330 (--sync) scenarios (1-2 hours)
6. Test feature interactions (1 hour)

---

## Risks & Mitigations

### Risk 1: Task Number Allocation Conflicts

**Risk**: Concurrent operations allocate same task numbers

**Likelihood**: Low  
**Impact**: High

**Mitigation**:
- Use state.json next_project_number as single source of truth
- Atomic updates via temp file pattern
- Sequential allocation (no parallelism)
- Validate task numbers not already in use

### Risk 2: Rollback Complexity

**Risk**: Nested rollbacks or partial rollbacks fail

**Likelihood**: Medium  
**Impact**: High

**Mitigation**:
- Implement rollback at status-sync-manager level
- Track created tasks for cleanup
- Test rollback thoroughly
- Provide manual recovery instructions

### Risk 3: State File Corruption

**Risk**: Atomic write pattern fails, corrupting state files

**Likelihood**: Low  
**Impact**: Critical

**Mitigation**:
- Two-phase commit protocol (temp files + atomic rename)
- Git-only rollback (restore from git)
- Comprehensive validation before writes
- Test atomic write pattern thoroughly

### Risk 4: Feature Interaction Conflicts

**Risk**: Features conflict when used together

**Likelihood**: Medium  
**Impact**: Medium

**Mitigation**:
- Test feature interactions comprehensively
- Ensure atomic operations across all features
- Validate state consistency after each operation
- Document known limitations and conflicts

### Risk 5: Implementation Scope Creep

**Risk**: Features grow beyond original scope

**Likelihood**: High  
**Impact**: Medium

**Mitigation**:
- Stick to defined requirements for each task
- Defer enhancements to future tasks
- Focus on core functionality first
- Review scope regularly during implementation

---

## Effort Estimation

### Phase 1: Task 325 (--recover) - 6 hours
- Implement unarchive_task operation: 3 hours
- Add --recover flag parsing: 1 hour
- Integrate recovery workflow: 1 hour
- Add git integration and error handling: 1 hour

### Phase 2: Task 322 (Bulk Operations) - 10 hours
- Research bulk operations: 2 hours
- Implement bulk_create_tasks: 2.5 hours
- Implement bulk_update_tasks: 2.5 hours
- Implement bulk_delete_tasks: 1.5 hours
- Testing and documentation: 1.5 hours

### Phase 3: Task 326 (--divide) - 14 hours
- Add --divide TASK_NUMBER parsing: 2 hours
- Implement task analysis: 3 hours
- Implement atomic subtask creation: 4 hours
- Implement dependency management: 3 hours
- Git integration and testing: 2 hours

### Phase 4: Task 330 (--sync) - 8 hours
- Research sync requirements: 2 hours
- Implement sync_tasks operation: 3 hours
- Add --sync flag parsing: 1.5 hours
- Testing and documentation: 1.5 hours

### Phase 5: Shared Infrastructure - 5 hours
- Atomic operation utilities: 1.5 hours
- Bulk processing utilities: 1.5 hours
- Error handling framework: 1.5 hours
- Documentation: 0.5 hours

### Phase 6: Comprehensive Testing - 7 hours
- Test plan creation: 1 hour
- Feature-specific testing: 5 hours
- Integration testing: 1 hour

**Total Estimated Effort**: 50 hours

**Note**: Original estimate was 18-24 hours, but comprehensive analysis reveals significantly more work required, especially for tasks 322 and 330 which lack research. Revised estimate accounts for research, implementation, testing, and integration.

---

## Appendix: Sources and Citations

### Source 1: Task 325 Research Report
- **File**: `.opencode/specs/325_create___recover_flag_for_task_command_to_unarchive_projects/reports/research-001.md`
- **Key Sections**: Archive system analysis, recovery workflow, atomic updates, error handling
- **Relevance**: Comprehensive research for --recover flag implementation

### Source 2: Task 325 Implementation Plan
- **File**: `.opencode/specs/325_create___recover_flag_for_task_command_to_unarchive_projects/plans/implementation-001.md`
- **Key Sections**: Phase breakdown, acceptance criteria, testing plan
- **Relevance**: Detailed implementation plan for --recover flag

### Source 3: Task 326 Research Report
- **File**: `.opencode/specs/326_create___divide_flag_for_task_command_with_task_division_capability/reports/research-001.md`
- **Key Sections**: Task division workflow, dependency management, rollback mechanism
- **Relevance**: Comprehensive research for --divide flag implementation

### Source 4: /task Command Specification
- **File**: `.opencode/command/task.md`
- **Key Sections**: ParseInput, ReformulateDescription, DivideIfRequested, CreateTasks
- **Relevance**: Current command structure and patterns

### Source 5: status-sync-manager Specification
- **File**: `.opencode/agent/subagents/status-sync-manager.md`
- **Key Sections**: create_task_flow, archive_tasks_flow, atomic write pattern
- **Relevance**: Atomic operations and state synchronization patterns

### Source 6: state.json Schema
- **File**: `.opencode/specs/state.json`
- **Key Fields**: active_projects, next_project_number, dependencies
- **Relevance**: Task metadata structure and state tracking

### Source 7: TODO.md Structure
- **File**: `.opencode/specs/TODO.md`
- **Key Sections**: Priority sections, task entry format
- **Relevance**: User-facing task list structure

---

## Conclusion

This research provides a comprehensive analysis of the four dependency tasks (325, 326, 322, 330) and designs a unified architecture for /task command enhancements. The key findings reveal common patterns (atomic operations, status-sync-manager delegation, git integration), potential conflicts (task number allocation, rollback complexity), and implementation dependencies (task 322 provides infrastructure for task 326).

The recommended approach implements features in dependency order (325 → 322 → 326 → 330), establishes shared infrastructure for atomic operations and bulk processing, creates a unified error handling framework, and ensures all features integrate seamlessly with existing patterns.

The revised effort estimate is 50 hours (significantly higher than the original 18-24 hours) due to the need for research on tasks 322 and 330, comprehensive testing, and integration work. However, this investment ensures architectural consistency, avoids conflicts, and improves the integrity of the /task command.

**Next Steps**:
1. Create implementation plan for task 332 based on this research
2. Begin implementation with task 325 (--recover flag)
3. Research and implement task 322 (bulk operations)
4. Implement task 326 (--divide flag for existing tasks)
5. Research and implement task 330 (--sync flag)
6. Create shared infrastructure and comprehensive testing
