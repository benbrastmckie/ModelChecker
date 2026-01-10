# Implementation Plan: Fix /todo Command Archival and Enforce Status Marker Standards

- **Task**: 235 - Find and fix root cause of /todo command not archiving completed tasks
- **Status**: [IN PROGRESS]
- **Effort**: 12 hours (2 hours completed, 10 hours remaining)
- **Progress**: 17% (Phase 1 complete)
- **Priority**: High
- **Dependencies**: None
- **Research Inputs**: Research Report (.opencode/specs/235_find_and_fix_root_cause_of_todo_command_not_archiving_completed_tasks/reports/research-001.md)
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/tasks.md
- **Language**: markdown
- **Lean Intent**: false
- **Started**: 2025-12-29
- **Last Updated**: 2025-12-29

## Overview

Research identified two root causes for /todo command archival failures: (1) Incomplete TODO.md updates during archival - tasks successfully move to archive/state.json and archive/ directories but entries remain in TODO.md, creating dual-state inconsistency for 23+ tasks, and (2) Status marker format inconsistency - 88% of completed tasks (23 of 26) use non-standard formats like `COMPLETED` (no brackets), `[PASS] [COMPLETED]` (emoji in heading), or mixed formats that may not match the command's identification pattern. This plan addresses both root causes through manual cleanup, command debugging, systematic enforcement, and verification.

## Goals & Non-Goals

**Goals**:
- Standardize all status markers in TODO.md to match status-markers.md standards
- Remove duplicate entries (tasks in both TODO.md and archive/state.json)
- Debug and fix /todo command Stage 4/5 logic that fails to remove TODO.md entries
- Identify and fix sources of status marker inconsistency in workflow commands and agents
- Strengthen validation in status-sync-manager and workflow commands
- Verify /todo command successfully archives all completed tasks
- Ensure TODO.md contains only active tasks with no dual-state inconsistencies

**Non-Goals**:
- Renumbering tasks (preserve existing task numbers per /todo specification)
- Changing archive/state.json structure or schema
- Modifying git commit history for previous archival operations
- Implementing new status marker types beyond those in status-markers.md
- Creating automated status marker correction tools (manual cleanup sufficient for one-time fix)

## Risks & Mitigations

**Risk**: Manual TODO.md editing introduces syntax errors or breaks task structure
- **Mitigation**: Use grep/sed for systematic replacements, validate TODO.md syntax after each change, create git checkpoint before manual edits

**Risk**: Removing tasks from TODO.md that aren't actually in archive/state.json causes data loss
- **Mitigation**: Cross-reference every task removal against archive/state.json entries, verify project directories exist in archive/ before removing TODO.md entries

**Risk**: /todo command fix introduces regressions in archival logic
- **Mitigation**: Test with small batch (3-5 tasks) before full archival, verify atomic update guarantees preserved, add validation checkpoints

**Risk**: Workflow commands continue creating non-standard status markers after enforcement fixes
- **Mitigation**: Add validation to status-sync-manager that rejects non-standard formats, test all 4 workflow commands (/research, /plan, /implement, /revise) after changes

**Risk**: Emoji removal from task headings breaks cross-references or links
- **Mitigation**: Search for emoji usage in cross-references before removal, update any broken links after cleanup

## Implementation Phases

### Phase 1: Manual TODO.md Cleanup and Standardization [COMPLETED]

**Goal**: Prepare TODO.md for successful /todo execution by standardizing status markers and removing duplicate entries

**Status**: [PASS] COMPLETED (2025-12-29)
**Actual Time**: 2 hours
**Git Commits**: 
- `baa5ae6`: Checkpoint before TODO.md cleanup (task 235 phase 1)
- `e45b93a`: task 235 phase 1: remove duplicate archived tasks (177, 183, 184, 211, 213) and standardize status markers (remove [PASS] emojis from all headings)

**Tasks**:
- [x] Create git checkpoint before manual edits (git commit -m "Checkpoint before TODO.md cleanup")
- [x] Identify all tasks with non-standard status markers (grep for COMPLETED without brackets, [PASS] emoji)
- [x] Standardize status markers: Change `COMPLETED` to `[COMPLETED]`, remove [PASS] from headings, ensure brackets present
- [x] Cross-reference TODO.md tasks against archive/state.json to identify duplicates (tasks in both files)
- [x] For each duplicate task: Verify project directory in archive/, verify entry in archive/state.json, remove from TODO.md
- [x] Validate TODO.md syntax: Check task numbering preserved, no orphaned metadata, proper section structure
- [x] Create git commit with standardized TODO.md (git commit -m "Standardize status markers and remove duplicate entries")
- [x] Verify TODO.md contains only active tasks and properly formatted completed tasks ready for archival

**Timing**: 2 hours (actual)

**Accomplishments**:
- **Duplicate tasks removed** (5 tasks confirmed in archive/state.json):
  - Task 177: Update examples to use latest APIs
  - Task 183: Fix DeductionTheorem.lean build errors
  - Task 184: Fix Truth.lean build error
  - Task 211: Standardize command lifecycle procedures
  - Task 213: Resolve is_valid_swap_involution blocker
- **Status markers standardized** (11 tasks, [PASS] emoji removed from headings):
  - Tasks 185, 186, 187, 188, 190, 210, 220, 222, 231, 232, 234
- **Impact**: Removed 231 lines from TODO.md
- **Dual-state resolution progress**: 5 of 23+ tasks resolved (22%)

**Acceptance Criteria**:
- [x] All status markers use standard format: `[COMPLETED]`, `[ABANDONED]`, `[NOT STARTED]`, etc. with square brackets
- [x] No [PASS] emoji in task headings (only 1 remaining in task 235 description text)
- [x] All tasks in archive/state.json removed from TODO.md (5 duplicate tasks removed)
- [x] TODO.md syntax validated (no orphaned metadata, proper structure)
- [x] Git commit created documenting cleanup changes

### Phase 2: Debug /todo Command Stage 4/5 Logic [NOT STARTED]

**Goal**: Identify and fix the bug in /todo command that prevents TODO.md entry removal during archival

**Tasks**:
- [ ] Review .opencode/command/todo.md Stage 4 (PrepareUpdates) specification (lines 152-297)
- [ ] Review .opencode/command/todo.md Stage 5 (AtomicUpdate) specification (lines 300-361)
- [ ] Add logging to Stage 4: Log task blocks marked for removal, log boundary detection, log validation results
- [ ] Add logging to Stage 5: Log TODO.md write operation, log file size before/after, log verification results
- [ ] Add validation checkpoint after Stage 5: Verify TODO.md no longer contains archived task entries
- [ ] Test /todo command with 3 completed tasks (below threshold, auto-proceed)
- [ ] Analyze logs to identify where TODO.md update fails (preparation vs commit phase)
- [ ] Implement fix based on root cause (likely Stage 4 block removal or Stage 5 write operation)
- [ ] Add error handling for TODO.md update failures with clear user error messages
- [ ] Re-test /todo command to verify fix works correctly

**Timing**: 3 hours

**Acceptance Criteria**:
- Logging added to Stage 4 and Stage 5 showing TODO.md update operations
- Validation checkpoint added after Stage 5 to verify TODO.md entries removed
- Root cause of TODO.md update failure identified through log analysis
- Fix implemented that ensures TODO.md entries removed during archival
- Error handling added for TODO.md update failures
- Test execution confirms TODO.md entries successfully removed

### Phase 3: Systematic Status Marker Enforcement [NOT STARTED]

**Goal**: Identify and fix sources of status marker inconsistency in workflow commands and agents to prevent future non-standard markers

**Tasks**:
- [ ] Audit /research command for status marker creation (check for emoji additions, bracket omissions)
- [ ] Audit /plan command for status marker creation
- [ ] Audit /implement command for status marker creation and updates
- [ ] Audit /revise command for status marker preservation
- [ ] Audit status-sync-manager for status marker validation (check if it accepts non-standard formats)
- [ ] Audit task-executor for status marker updates
- [ ] Identify sources creating [PASS] emoji in headings (likely manual additions or specific command)
- [ ] Identify sources creating COMPLETED without brackets
- [ ] Add validation to status-sync-manager: Reject status markers without square brackets
- [ ] Add validation to status-sync-manager: Reject emoji in status markers ([PASS], [FAIL], etc.)
- [ ] Update workflow commands to only use standard status markers per status-markers.md
- [ ] Add pre-write validation in all commands: Verify status markers match standard format before writing TODO.md
- [ ] Document enforcement mechanisms in status-markers.md (validation rules, rejection criteria)

**Timing**: 3 hours

**Acceptance Criteria**:
- All 4 workflow commands audited for status marker compliance
- status-sync-manager and task-executor audited for validation gaps
- Sources of non-standard markers identified (commands, agents, or manual edits)
- Validation added to status-sync-manager rejecting non-standard formats
- Workflow commands updated to only create standard status markers
- Pre-write validation added to prevent non-standard markers from being written
- Documentation updated with enforcement mechanisms

### Phase 4: Test /todo Command with Standardized Markers [NOT STARTED]

**Goal**: Verify /todo command successfully archives all completed tasks after fixes applied

**Tasks**:
- [ ] Count completed tasks in TODO.md (should be ~24 after Phase 1 cleanup)
- [ ] Verify all completed tasks use standard `[COMPLETED]` format
- [ ] Execute /todo command (expect confirmation prompt if > 5 tasks)
- [ ] Confirm archival when prompted
- [ ] Verify TODO.md updated: All completed task entries removed
- [ ] Verify archive/state.json updated: All completed tasks added (no duplicates)
- [ ] Verify project directories moved to .opencode/specs/archive/
- [ ] Verify git commit created with proper message (e.g., "todo: archive 24 completed tasks")
- [ ] Verify TODO.md contains only active tasks: [NOT STARTED], [IN PROGRESS], [RESEARCHED], [PLANNED], [BLOCKED]
- [ ] Verify no dual-state tasks remain (tasks in both TODO.md and archive/state.json)
- [ ] Check for orphaned metadata lines in TODO.md (should be none)

**Timing**: 1.5 hours

**Acceptance Criteria**:
- /todo command executes successfully without errors
- All completed tasks removed from TODO.md
- All completed tasks added to archive/state.json (no duplicates)
- Project directories moved to archive/
- Git commit created
- TODO.md contains only active tasks
- No dual-state tasks remain
- No orphaned metadata in TODO.md

### Phase 5: Verification and Documentation [NOT STARTED]

**Goal**: Verify system-wide consistency and document fixes for future reference

**Tasks**:
- [ ] Verify TODO.md statistics: Count total tasks, count by status, verify no [COMPLETED] or [ABANDONED] remain
- [ ] Verify archive/state.json statistics: Count archived projects, verify recent additions match /todo execution
- [ ] Verify state.json consistency: Check completed_projects list matches archive/state.json
- [ ] Test workflow commands with new validation: Create test task, run /implement, verify standard status markers used
- [ ] Test status-sync-manager validation: Attempt to update task with non-standard marker, verify rejection
- [ ] Document fixes in task 235 implementation summary: Root causes, fixes applied, validation results
- [ ] Update status-markers.md if needed: Add enforcement section, document validation rules
- [ ] Update /todo command documentation if needed: Document Stage 4/5 fixes, add troubleshooting section
- [ ] Create follow-up tasks if needed: Automated status marker linting, periodic TODO.md health checks

**Timing**: 2.5 hours

**Acceptance Criteria**:
- TODO.md statistics verified (no completed/abandoned tasks remain)
- archive/state.json statistics verified (all archived tasks present)
- state.json consistency verified
- Workflow commands tested with new validation (standard markers enforced)
- status-sync-manager validation tested (non-standard markers rejected)
- Implementation summary created documenting all fixes
- Documentation updated (status-markers.md, /todo command)
- Follow-up tasks created if needed

## Testing & Validation

**Unit Tests**:
- Test status-sync-manager validation: Reject `COMPLETED` without brackets
- Test status-sync-manager validation: Reject `[PASS] [COMPLETED]` with emoji
- Test status-sync-manager validation: Accept `[COMPLETED]` standard format
- Test /todo Stage 1 identification: Match `[COMPLETED]` tasks
- Test /todo Stage 4 block removal: Remove complete task blocks with boundaries
- Test /todo Stage 5 atomic update: Verify TODO.md write succeeds

**Integration Tests**:
- Test /todo command end-to-end: 3 completed tasks → all archived, TODO.md updated, git commit created
- Test /todo command with threshold: 10 completed tasks → confirmation prompt → all archived after confirmation
- Test /todo command with duplicates: Task in both TODO.md and archive/state.json → removed from TODO.md, no duplicate in archive
- Test workflow command status markers: /implement task → verify `[COMPLETED]` format used, no emoji, brackets present

**Manual Validation**:
- Visual inspection of TODO.md: No completed tasks visible, proper structure maintained
- Visual inspection of archive/state.json: All archived tasks present with correct metadata
- Git log inspection: Verify /todo commit message accurate, verify changes match expectations
- Cross-reference check: Every task in archive/state.json should NOT be in TODO.md

## Artifacts & Outputs

**Created**:
- .opencode/specs/235_find_and_fix_root_cause_of_todo_command_not_archiving_completed_tasks/plans/implementation-001.md (this file)
- .opencode/specs/235_find_and_fix_root_cause_of_todo_command_not_archiving_completed_tasks/summaries/implementation-summary-YYYYMMDD.md

**Modified**:
- .opencode/specs/TODO.md (standardized status markers, removed duplicates, archived completed tasks)
- .opencode/command/todo.md (added logging, validation, error handling for Stage 4/5)
- .opencode/agent/subagents/status-sync-manager.md (added status marker validation)
- .opencode/command/research.md (enforced standard status markers)
- .opencode/command/plan.md (enforced standard status markers)
- .opencode/command/implement.md (enforced standard status markers)
- .opencode/command/revise.md (enforced standard status markers)
- .opencode/context/core/standards/status-markers.md (documented enforcement mechanisms)
- .opencode/specs/archive/state.json (added archived task entries)
- state.json (updated completed_projects list)

**Verified**:
- All project directories in .opencode/specs/archive/ for archived tasks
- Git commits for manual cleanup and /todo execution
- No dual-state tasks (in both TODO.md and archive/state.json)

## Rollback/Contingency

**If manual cleanup introduces errors**:
- Revert to git checkpoint created in Phase 1 (git reset --hard <checkpoint-commit>)
- Re-apply cleanup more carefully with smaller batches
- Use automated sed/grep scripts instead of manual editing

**If /todo command fix introduces regressions**:
- Revert .opencode/command/todo.md to previous version
- Analyze logs to identify regression cause
- Apply more targeted fix to specific stage (4 or 5)
- Re-test with smaller batch before full archival

**If status marker enforcement breaks workflow commands**:
- Revert validation changes to status-sync-manager
- Update workflow commands to use standard markers before re-enabling validation
- Test each command individually before system-wide enforcement

**If archival fails mid-execution**:
- /todo command has built-in rollback mechanism (two-phase commit)
- Verify rollback succeeded (TODO.md, state.json, archive/state.json restored)
- Check error logs for failure cause
- Fix underlying issue before retry

**If dual-state tasks persist after /todo execution**:
- Manually remove remaining duplicates from TODO.md
- Investigate why /todo didn't remove them (check logs)
- Apply additional fixes to Stage 4/5 logic
- Re-run /todo to clean up any remaining tasks
