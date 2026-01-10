# Implementation Plan: Fix Systematic status-sync-manager TODO.md Update Failures

- **Task**: 227 - Fix systematic status-sync-manager TODO.md update failures across all workflow commands
- **Status**: [NOT STARTED]
- **Effort**: 11 hours
- **Priority**: High
- **Dependencies**: None
- **Research Inputs**: .opencode/specs/227_fix_systematic_status_sync_manager_failures/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/tasks.md
- **Language**: markdown
- **Lean Intent**: false

## Overview

Research has identified the root cause of systematic status update failures: ALL 4 workflow commands (/research, /plan, /revise, /implement) specify delegation to status-sync-manager in their documentation but do NOT actually invoke it during execution. Instead, commands perform manual TODO.md updates and skip global state.json updates entirely, creating inconsistent state where TODO.md shows one status but state.json shows another (or nothing). This is a delegation gap, not a status-sync-manager bug. The fix requires removing all manual file updates from commands and adding proper status-sync-manager delegation with validation, following the two-phase commit protocol specified in command-lifecycle.md. Success means 100% atomic updates across TODO.md + state.json + project state.json for all workflow commands.

## Goals & Non-Goals

**Goals**:
- Remove all manual TODO.md and state.json updates from all 4 workflow commands
- Add status-sync-manager delegation to all 4 commands with complete parameters
- Add pre-commit validation to catch errors before status-sync-manager invocation
- Add post-commit validation to verify status-sync-manager actually updated all files
- Ensure atomicity across TODO.md + state.json + project state.json for all commands
- Test rollback mechanism works correctly on failures
- Achieve 100% atomic update success rate across all workflow commands

**Non-Goals**:
- Modifying status-sync-manager implementation (research confirms it's correct)
- Changing status marker definitions or state schema
- Refactoring command-lifecycle.md workflow stages
- Adding new status markers or workflow states
- Performance optimization of status-sync-manager

## Risks & Mitigations

- **Risk**: Breaking existing workflows during delegation changes. **Mitigation**: Extensive testing with existing tasks (224, etc.) before deployment. Feature flag for delegation if needed.
- **Risk**: status-sync-manager has undiscovered bugs that surface when actually invoked. **Mitigation**: Thorough testing of status-sync-manager in isolation before integration. Fix bugs as discovered.
- **Risk**: Incomplete rollback leaves corrupted state. **Mitigation**: Test rollback extensively with simulated failures. Add comprehensive logging. Document manual state restoration procedure.
- **Risk**: Validation too strict, rejects valid operations. **Mitigation**: Careful validation design based on actual command outputs. Extensive testing with real tasks. Adjust validation rules based on feedback.
- **Risk**: Two-phase commit adds latency to commands. **Mitigation**: Acceptable tradeoff for correctness. Optimize status-sync-manager if needed. Add caching if performance becomes issue.

## Implementation Phases

### Phase 1: Fix /research Command Delegation [NOT STARTED]

- **Goal**: Remove manual updates from /research and add status-sync-manager delegation with validation
- **Tasks**:
  - [ ] Read current /research command implementation (.opencode/command/research.md)
  - [ ] Identify all manual TODO.md update locations (sed/awk commands)
  - [ ] Identify all manual state.json update locations (jq commands)
  - [ ] Identify all manual project state.json creation locations
  - [ ] Remove all manual update code from /research Stage 7 (Postflight)
  - [ ] Add status-sync-manager delegation call with parameters: task_number, new_status="researched", timestamp, session_id, validated_artifacts
  - [ ] Add pre-commit validation: validate_before_status_sync(task_number, "researched", researcher_return, "research")
  - [ ] Add post-commit validation: validate_after_status_sync(task_number, "[RESEARCHED]", status_sync_result)
  - [ ] Add error handling for status-sync-manager failures with rollback reporting
  - [ ] Update /research documentation to reflect delegation pattern
  - [ ] Test with Task 224 (existing researched task) - verify TODO.md, state.json, project state.json all updated
  - [ ] Test with new task - verify atomic updates work
  - [ ] Test rollback - simulate write failure, verify all files restored
  - [ ] Verify no manual updates remain in /research code
- **Timing**: 2 hours
- **Acceptance Criteria**:
  - /research delegates to status-sync-manager with all required parameters
  - TODO.md, state.json, project state.json all updated atomically
  - Pre-commit validation catches errors before status-sync-manager invocation
  - Post-commit validation verifies all files updated correctly
  - Rollback works on simulated failures
  - No manual file updates remain in /research code
  - Tests pass with both existing and new tasks

### Phase 2: Fix /plan Command Delegation [NOT STARTED]

- **Goal**: Remove manual updates from /plan and add status-sync-manager delegation with plan_metadata
- **Tasks**:
  - [ ] Read current /plan command implementation (.opencode/command/plan.md)
  - [ ] Identify all manual TODO.md update locations
  - [ ] Identify all manual state.json update locations
  - [ ] Remove all manual update code from /plan Stage 7 (Postflight)
  - [ ] Add status-sync-manager delegation call with parameters: task_number, new_status="planned", timestamp, session_id, validated_artifacts, plan_path, plan_metadata
  - [ ] Extract plan_metadata from planner return (phase_count, estimated_hours, complexity)
  - [ ] Add pre-commit validation: validate_before_status_sync(task_number, "planned", planner_return, "plan")
  - [ ] Validate plan_metadata present in planner return before delegation
  - [ ] Add post-commit validation: validate_after_status_sync(task_number, "[PLANNED]", status_sync_result)
  - [ ] Add error handling for missing plan_metadata with clear error message
  - [ ] Add error handling for status-sync-manager failures
  - [ ] Update /plan documentation to reflect delegation pattern
  - [ ] Test with existing planned task - verify TODO.md, state.json, project state.json, plan link all updated
  - [ ] Test with new task - verify plan_metadata stored in state.json correctly
  - [ ] Test rollback - verify all files restored on failure
  - [ ] Verify no manual updates remain in /plan code
- **Timing**: 2 hours
- **Acceptance Criteria**:
  - /plan delegates to status-sync-manager with plan_path and plan_metadata
  - plan_metadata extracted from planner return and validated before delegation
  - TODO.md updated with plan link, state.json updated with plan_path and plan_metadata
  - All files updated atomically
  - Validation catches missing plan_metadata before commit
  - Rollback works correctly
  - Tests pass with both existing and new tasks

### Phase 3: Fix /revise Command Delegation [NOT STARTED]

- **Goal**: Remove manual updates from /revise and add status-sync-manager delegation with plan_version
- **Tasks**:
  - [ ] Read current /revise command implementation (.opencode/command/revise.md)
  - [ ] Identify all manual TODO.md update locations
  - [ ] Identify all manual state.json update locations
  - [ ] Remove all manual update code from /revise Stage 7 (Postflight)
  - [ ] Add status-sync-manager delegation call with parameters: task_number, new_status="revised", timestamp, session_id, validated_artifacts, plan_path, plan_metadata, plan_version, revision_reason
  - [ ] Extract plan_version from planner return
  - [ ] Extract revision_reason from user prompt
  - [ ] Add pre-commit validation: validate_before_status_sync(task_number, "revised", planner_return, "revise")
  - [ ] Add post-commit validation: validate_after_status_sync(task_number, "[REVISED]", status_sync_result)
  - [ ] Verify plan_versions array appended correctly in state.json
  - [ ] Add error handling for status-sync-manager failures
  - [ ] Update /revise documentation to reflect delegation pattern
  - [ ] Test with existing revised task - verify TODO.md, state.json, plan link all updated
  - [ ] Test plan_versions array - verify new version appended correctly
  - [ ] Test rollback - verify all files restored on failure
  - [ ] Verify no manual updates remain in /revise code
- **Timing**: 1.5 hours
- **Acceptance Criteria**:
  - /revise delegates to status-sync-manager with plan_version and revision_reason
  - TODO.md updated with new plan link, state.json plan_versions array appended
  - All files updated atomically
  - Validation works correctly
  - Rollback works correctly
  - Tests pass with existing and new revisions

### Phase 4: Fix /implement Command Delegation [NOT STARTED]

- **Goal**: Remove manual updates from /implement and add status-sync-manager delegation with phase_statuses
- **Tasks**:
  - [ ] Read current /implement command implementation (.opencode/command/implement.md)
  - [ ] Identify all manual TODO.md update locations
  - [ ] Identify all manual state.json update locations
  - [ ] Identify all manual plan file update locations
  - [ ] Remove all manual update code from /implement Stage 7 (Postflight)
  - [ ] Add status-sync-manager delegation call with parameters: task_number, new_status="completed", timestamp, session_id, validated_artifacts, plan_path, phase_statuses
  - [ ] Extract phase_statuses from task-executor return (for phased implementations)
  - [ ] Add validation for phase_statuses format before delegation
  - [ ] Add pre-commit validation: validate_before_status_sync(task_number, "completed", implementer_return, "implement")
  - [ ] Add special validation for phased vs direct implementations
  - [ ] Add post-commit validation: validate_after_status_sync(task_number, "[COMPLETED]", status_sync_result)
  - [ ] Verify plan file phase statuses updated correctly (if phased)
  - [ ] Add error handling for missing phase_statuses in phased implementations
  - [ ] Add error handling for status-sync-manager failures
  - [ ] Update /implement documentation to reflect delegation pattern
  - [ ] Test with phased implementation - verify TODO.md, state.json, plan file all updated
  - [ ] Test with direct implementation - verify TODO.md, state.json updated (no plan file)
  - [ ] Test phase_statuses - verify plan file updated with correct phase statuses
  - [ ] Test rollback - verify all files restored on failure
  - [ ] Verify no manual updates remain in /implement code
- **Timing**: 2.5 hours
- **Acceptance Criteria**:
  - /implement delegates to status-sync-manager with phase_statuses (if phased)
  - phase_statuses extracted and validated before delegation
  - TODO.md updated with checkmark, state.json updated, plan file phase statuses updated (if phased)
  - All files updated atomically
  - Validation distinguishes phased vs direct implementations correctly
  - Rollback works correctly for both modes
  - Tests pass with both phased and direct implementations

### Phase 5: Integration Testing and Validation [NOT STARTED]

- **Goal**: Comprehensive end-to-end testing of all 4 commands with status-sync-manager delegation
- **Tasks**:
  - [ ] Create integration test suite for status-sync-manager delegation
  - [ ] Test /research end-to-end: new task, verify TODO.md + state.json + project state.json updated
  - [ ] Test /plan end-to-end: researched task, verify plan_metadata stored correctly
  - [ ] Test /revise end-to-end: planned task, verify plan_versions array updated
  - [ ] Test /implement end-to-end (phased): planned task, verify phase_statuses updated in plan file
  - [ ] Test /implement end-to-end (direct): task without plan, verify completion
  - [ ] Test rollback scenarios: simulate write failures for each command, verify rollback works
  - [ ] Test validation failures: invalid status transitions, missing artifacts, malformed metadata
  - [ ] Test with existing tasks: Task 224 and others, verify no regressions
  - [ ] Test atomicity: verify all files update or none update (no partial updates)
  - [ ] Test timestamp consistency: verify timestamps match across all files
  - [ ] Measure success rate: verify 100% atomic update success across all commands
  - [ ] Document test results and any issues found
  - [ ] Fix any bugs discovered during integration testing
  - [ ] Re-test after bug fixes to verify 100% success rate
- **Timing**: 2 hours
- **Acceptance Criteria**:
  - All integration tests pass for all 4 commands
  - 100% atomic update success rate verified
  - Rollback works in all failure scenarios tested
  - Validation catches all error types tested
  - No regressions with existing tasks
  - Timestamp consistency verified across all files
  - All bugs found during testing are fixed and re-tested

### Phase 6: Documentation and Cleanup [NOT STARTED]

- **Goal**: Update documentation and ensure all changes are properly documented
- **Tasks**:
  - [ ] Update command-lifecycle.md with delegation examples from implementation
  - [ ] Add troubleshooting guide for status-sync-manager failures
  - [ ] Document validation checks in command-lifecycle.md
  - [ ] Add examples of correct delegation pattern to each command file
  - [ ] Update IMPLEMENTATION_STATUS.md with task 227 completion
  - [ ] Document pre-commit and post-commit validation patterns
  - [ ] Add error handling examples for common failure scenarios
  - [ ] Document rollback procedure for manual state restoration (if needed)
  - [ ] Review all 4 command files for documentation accuracy
  - [ ] Verify no outdated manual update instructions remain in docs
  - [ ] Add comments in command files explaining delegation flow
  - [ ] Create summary of changes for user-facing documentation
- **Timing**: 1 hour
- **Acceptance Criteria**:
  - command-lifecycle.md updated with delegation examples
  - Troubleshooting guide complete and accurate
  - All 4 command files have accurate documentation
  - IMPLEMENTATION_STATUS.md updated
  - No outdated manual update instructions remain
  - Examples clear and correct

## Testing & Validation

### Pre-Implementation Testing
- [ ] Verify status-sync-manager.md specification is complete and correct
- [ ] Review command-lifecycle.md Stage 7 requirements for delegation
- [ ] Identify all manual update anti-patterns in current command implementations

### Per-Phase Testing
- [ ] Phase 1: Test /research with Task 224 and new task
- [ ] Phase 2: Test /plan with existing and new tasks
- [ ] Phase 3: Test /revise with existing revised task
- [ ] Phase 4: Test /implement with phased and direct modes
- [ ] Phase 5: Integration testing across all commands
- [ ] Phase 6: Documentation review and accuracy check

### Post-Implementation Testing
- [ ] End-to-end workflow test: /research → /plan → /implement on new task
- [ ] Verify TODO.md, state.json, project state.json consistency across workflow
- [ ] Test rollback on simulated failures for each command
- [ ] Verify 100% atomic update success rate
- [ ] Test with multiple existing tasks to verify no regressions
- [ ] Measure command latency impact (should be < 500ms increase)

### Validation Criteria
- [ ] All manual TODO.md updates removed from commands
- [ ] All manual state.json updates removed from commands
- [ ] All manual plan file updates removed from commands
- [ ] status-sync-manager delegation present in all 4 commands
- [ ] Pre-commit validation present in all 4 commands
- [ ] Post-commit validation present in all 4 commands
- [ ] Error handling for status-sync-manager failures in all commands
- [ ] Rollback mechanism tested and working
- [ ] 100% atomic update success rate achieved
- [ ] No "status-sync-manager didn't update TODO.md" errors occur

## Artifacts & Outputs

### Implementation Artifacts
- .opencode/command/research.md (updated with delegation)
- .opencode/command/plan.md (updated with delegation)
- .opencode/command/revise.md (updated with delegation)
- .opencode/command/implement.md (updated with delegation)

### Documentation Artifacts
- .opencode/context/core/workflows/command-lifecycle.md (updated with examples)
- .opencode/specs/227_fix_systematic_status_sync_manager_failures/summaries/implementation-summary-YYYYMMDD.md

### Testing Artifacts
- Integration test results documentation
- Rollback test results documentation
- Performance measurement results

## Rollback/Contingency

### If Delegation Changes Break Workflows
1. Revert all 4 command files to previous versions
2. Restore manual update code temporarily
3. Add feature flag for status-sync-manager delegation
4. Debug delegation issues in isolation
5. Re-deploy with feature flag enabled for testing
6. Remove feature flag once stable

### If status-sync-manager Has Bugs
1. Document bug details with reproduction steps
2. Fix status-sync-manager.md specification if needed
3. Test fix in isolation before re-integrating
4. Re-run integration tests after fix
5. Continue with command delegation once status-sync-manager stable

### If Rollback Mechanism Fails
1. Document failure scenario and corrupted state
2. Create manual state restoration procedure
3. Restore TODO.md, state.json, project state.json manually from backups
4. Fix rollback mechanism in status-sync-manager
5. Test rollback fix extensively before re-deploying

### Manual State Restoration Procedure
If atomic updates fail and rollback doesn't work:
1. Identify which files are corrupted (TODO.md, state.json, project state.json)
2. Restore TODO.md from git history: `git checkout HEAD~1 .opencode/specs/TODO.md`
3. Restore state.json from git history: `git checkout HEAD~1 .opencode/specs/state.json`
4. Restore project state.json from git history: `git checkout HEAD~1 .opencode/specs/{task_number}_*/state.json`
5. Verify all files restored to consistent state
6. Re-run command after fixing underlying issue
