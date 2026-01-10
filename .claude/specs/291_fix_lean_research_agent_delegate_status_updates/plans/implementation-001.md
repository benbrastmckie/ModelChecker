# Implementation Plan: Fix lean-research-agent to Delegate Status Updates

**Task**: 291 - Fix lean-research-agent to delegate status updates to status-sync-manager instead of direct file manipulation  
**Status**: [NOT STARTED]  
**Estimated Effort**: 2.5 hours  
**Complexity**: Low-Medium  
**Language**: markdown  
**Priority**: High  
**Dependencies**: Task 290 (researched)  
**Plan Version**: 001  
**Created**: 2026-01-04  

---

## Overview

### Problem Statement

Task 290 identified that `/research 290` (a Lean research task) failed to update status markers despite successfully creating research artifacts. The research report was created, but:

1. TODO.md status remained `[NOT STARTED]` instead of updating to `[RESEARCHED]`
2. No artifact link was added to TODO.md
3. state.json was not updated
4. No git commit was created

Research confirmed the root cause: lean-research-agent.md step_6 (lines 651-662) directly manipulates TODO.md and state.json files instead of delegating to status-sync-manager and git-workflow-manager like researcher.md does. This bypasses atomic updates and causes status synchronization failures.

### Scope

This implementation will:
1. Replace direct TODO.md updates with status-sync-manager delegation
2. Replace direct state.json updates with status-sync-manager delegation (handled atomically)
3. Add git-workflow-manager delegation for automatic commit creation
4. Remove summary artifact requirement (align with researcher.md behavior)
5. Update step_6 documentation to reflect delegation pattern

**In Scope**:
- Modify `.opencode/agent/subagents/lean-research-agent.md` step_6 implementation
- Match researcher.md step_4_postflight delegation pattern exactly
- Remove summary artifact validation and linking
- Test with Lean research task

**Out of Scope**:
- Changes to other Lean subagents (lean-planner, lean-implementation-agent)
- Changes to status-sync-manager or git-workflow-manager
- Changes to general researcher.md (already correct)

### Constraints

- Must maintain backward compatibility with existing Lean research tasks
- Must not break existing research report creation
- Must follow exact delegation pattern from researcher.md
- Must preserve all error handling and validation
- Must maintain atomic updates across TODO.md and state.json

### Definition of Done

- [ ] lean-research-agent.md step_6 delegates to status-sync-manager (not direct file updates)
- [ ] lean-research-agent.md step_6 delegates to git-workflow-manager (not manual git commands)
- [ ] Summary artifact requirement removed (only research report created)
- [ ] `/research` on Lean tasks updates status to `[RESEARCHING]` at start (preflight)
- [ ] `/research` on Lean tasks updates status to `[RESEARCHED]` at end (postflight)
- [ ] Artifact link added to TODO.md (research report only)
- [ ] state.json updated with artifact path
- [ ] Git commit created automatically
- [ ] Behavior matches researcher.md exactly
- [ ] No regression in Lean research functionality
- [ ] Test with real Lean task (e.g., task 260) passes

---

## Goals and Non-Goals

### Goals

1. **Fix status synchronization**: Ensure lean-research-agent updates TODO.md and state.json atomically
2. **Enable git commits**: Automatically create git commits for Lean research completion
3. **Align with standard workflow**: Match researcher.md delegation pattern exactly
4. **Remove complexity**: Eliminate summary artifact requirement
5. **Maintain quality**: Preserve research quality and error handling

### Non-Goals

1. **Fix other Lean subagents**: lean-planner and lean-implementation-agent (separate tasks)
2. **Modify status-sync-manager**: Assume it works correctly (proven by researcher.md)
3. **Change research process**: Only fix status updates, not research methodology
4. **Add new features**: Only fix existing broken functionality

---

## Risks and Mitigations

### Risk 1: Breaking Existing Lean Research Tasks

**Likelihood**: Low  
**Impact**: Medium  
**Mitigation**:
- Test with existing Lean task (Task 260)
- Verify backward compatibility
- Keep backup of original lean-research-agent.md
- Use exact pattern from researcher.md (proven to work)

### Risk 2: status-sync-manager Delegation Failure

**Likelihood**: Low  
**Impact**: High  
**Mitigation**:
- Add error handling (log error but continue - artifact exists)
- Verify status-sync-manager is working correctly (proven by researcher.md)
- Test delegation with simple task first
- Follow researcher.md error handling pattern exactly

### Risk 3: git-workflow-manager Delegation Failure

**Likelihood**: Low  
**Impact**: Low (non-critical)  
**Mitigation**:
- Mark git failure as non-critical (don't fail research)
- Log warning for manual recovery
- Document manual commit process
- Follow researcher.md pattern (git failure doesn't fail research)

---

## Implementation Phases

### Phase 1: Replace Direct TODO.md Updates with status-sync-manager Delegation

**Estimated Effort**: 45 minutes  
**Status**: [NOT STARTED]  

**Objective**: Replace direct TODO.md manipulation with status-sync-manager delegation matching researcher.md pattern.

**Tasks**:
1. Read researcher.md lines 335-348 to understand delegation pattern
2. Read lean-research-agent.md lines 651-657 to understand current implementation
3. Replace lines 651-657 with status-sync-manager delegation:
   - Remove direct TODO.md update instructions
   - Add delegation context preparation (task_number, new_status, timestamp, session_id, validated_artifacts)
   - Add status-sync-manager invocation with timeout (60s)
   - Add return validation (status == "completed", files_updated includes ["TODO.md", "state.json"])
   - Add error handling (log error but continue if artifact exists)
4. Update step_6 action description to reflect delegation
5. Verify XML structure is valid

**Acceptance Criteria**:
- [ ] Lines 651-657 replaced with status-sync-manager delegation
- [ ] Delegation context includes all required fields
- [ ] Timeout set to 60s
- [ ] Return validation checks status and files_updated
- [ ] Error handling logs error but continues
- [ ] XML structure valid

**Validation**:
- Read modified lean-research-agent.md and compare with researcher.md
- Verify delegation pattern matches exactly
- Check XML syntax is valid

---

### Phase 2: Replace Direct state.json Updates with status-sync-manager Delegation

**Estimated Effort**: 15 minutes  
**Status**: [NOT STARTED]  

**Objective**: Remove direct state.json manipulation (handled atomically by status-sync-manager).

**Tasks**:
1. Read lean-research-agent.md lines 658-662 to understand current implementation
2. Remove lines 658-662 entirely (state.json handled by status-sync-manager)
3. Update documentation to clarify status-sync-manager handles both files
4. Verify no duplicate state.json update logic remains

**Acceptance Criteria**:
- [ ] Lines 658-662 removed
- [ ] No direct state.json manipulation remains
- [ ] Documentation clarifies status-sync-manager handles both files
- [ ] No duplicate logic

**Validation**:
- Search lean-research-agent.md for "state.json" references
- Verify only status-sync-manager delegation remains
- Check documentation is clear

---

### Phase 3: Add git-workflow-manager Delegation

**Estimated Effort**: 30 minutes  
**Status**: [NOT STARTED]  

**Objective**: Add git-workflow-manager delegation for automatic commit creation.

**Tasks**:
1. Read researcher.md lines 349-368 to understand git-workflow-manager delegation
2. Add git-workflow-manager delegation after status-sync-manager:
   - Prepare delegation context (scope_files, message_template, task_context, session_id)
   - Invoke git-workflow-manager with timeout (120s)
   - Validate return status (completed or failed)
   - Log commit hash if successful
   - Log warning if failed (non-critical)
3. Update step_6 process documentation
4. Add error handling section for git failures

**Acceptance Criteria**:
- [ ] git-workflow-manager delegation added
- [ ] Delegation context includes scope_files (research report, TODO.md, state.json)
- [ ] Timeout set to 120s
- [ ] Return validation checks status
- [ ] Commit hash logged if successful
- [ ] Warning logged if failed (non-critical)
- [ ] Error handling documented

**Validation**:
- Compare with researcher.md git-workflow-manager delegation
- Verify scope_files includes all modified files
- Check error handling is non-critical

---

### Phase 4: Remove Summary Artifact Requirement

**Estimated Effort**: 30 minutes  
**Status**: [NOT STARTED]  

**Objective**: Remove summary artifact validation and linking to match researcher.md behavior.

**Tasks**:
1. Search lean-research-agent.md for all summary artifact references
2. Remove summary artifact validation (lines 647-649):
   - Remove "Verify summary artifact created" check
   - Remove "Verify summary artifact is <100 tokens" check
   - Remove "Verify summary artifact is 3-5 sentences" check
3. Remove summary artifact linking (lines 664, 686-688, 764-766):
   - Remove summary from artifact links in TODO.md
   - Remove summary from state.json artifacts array
   - Remove summary from return format examples
4. Update return format to list only research report
5. Update validation section to check only research report

**Acceptance Criteria**:
- [ ] Summary artifact validation removed (lines 647-649)
- [ ] Summary artifact linking removed (lines 664, 686-688, 764-766)
- [ ] Return format lists only research report
- [ ] Validation checks only research report
- [ ] No summary artifact references remain

**Validation**:
- Search lean-research-agent.md for "summary" keyword
- Verify only JSON return object summary field remains (metadata)
- Compare with researcher.md (single artifact only)

---

### Phase 5: Update step_6 Documentation

**Estimated Effort**: 15 minutes  
**Status**: [NOT STARTED]  

**Objective**: Update step_6 documentation to reflect delegation pattern.

**Tasks**:
1. Rename `<step_6>` to `<step_6_postflight>` for consistency with researcher.md
2. Update action description to mention delegation
3. Update process documentation to reflect new workflow
4. Remove obsolete sections (direct file manipulation)
5. Add git failure handling section
6. Verify documentation is clear and accurate

**Acceptance Criteria**:
- [ ] step_6 renamed to step_6_postflight
- [ ] Action description mentions delegation
- [ ] Process documentation reflects new workflow
- [ ] Obsolete sections removed
- [ ] Git failure handling documented
- [ ] Documentation clear and accurate

**Validation**:
- Read updated documentation
- Compare with researcher.md step_4_postflight
- Verify consistency

---

### Phase 6: Test with Lean Task

**Estimated Effort**: 15 minutes  
**Status**: [NOT STARTED]  

**Objective**: Verify fix works with real Lean research task.

**Tasks**:
1. Identify test task (e.g., task 260 - Proof Search)
2. Run `/research 260` command
3. Verify research report created
4. Verify TODO.md status updated to `[RESEARCHED]`
5. Verify state.json updated with artifact path
6. Verify artifact link added to TODO.md
7. Verify git commit created
8. Verify no regression in research quality
9. Document test results

**Acceptance Criteria**:
- [ ] Research report created successfully
- [ ] TODO.md status updated to `[RESEARCHED]`
- [ ] state.json updated with artifact path
- [ ] Artifact link added to TODO.md (research report only)
- [ ] Git commit created with correct message
- [ ] No regression in research quality
- [ ] Test results documented

**Validation**:
- Check TODO.md for status and artifact link
- Check state.json for artifact path
- Check git log for commit
- Review research report quality

---

## Testing and Validation

### Unit Testing

**Phase 1-2 Testing**:
- Verify status-sync-manager delegation context is correct
- Verify error handling logs errors but continues
- Verify no direct file manipulation remains

**Phase 3 Testing**:
- Verify git-workflow-manager delegation context is correct
- Verify scope_files includes all modified files
- Verify git failure is non-critical

**Phase 4 Testing**:
- Verify no summary artifact validation remains
- Verify return format lists only research report
- Verify no summary artifact references remain

### Integration Testing

**Phase 6 Testing**:
- Run `/research 260` on Lean task
- Verify end-to-end workflow:
  1. Research report created
  2. TODO.md status updated to `[RESEARCHED]`
  3. state.json updated with artifact path
  4. Artifact link added to TODO.md
  5. Git commit created
- Compare behavior with researcher.md (general task)
- Verify identical status update behavior

### Regression Testing

- Test with existing Lean research task (Task 259)
- Verify no breaking changes
- Verify research quality maintained
- Verify error handling works correctly

---

## Artifacts and Outputs

### Modified Files

1. `.opencode/agent/subagents/lean-research-agent.md`
   - Lines 647-649: Summary artifact validation removed
   - Lines 651-662: Direct file manipulation replaced with delegation
   - Lines 664, 686-688, 764-766: Summary artifact references removed
   - step_6 renamed to step_6_postflight
   - Documentation updated

### Created Files

None (only modifying existing file)

### Validation Artifacts

1. Test execution report (Phase 6)
2. Comparison with researcher.md (validation)
3. Git commit for implementation

---

## Rollback/Contingency

### Rollback Plan

If implementation fails or causes regressions:

1. **Immediate Rollback**:
   - Restore backup of original lean-research-agent.md
   - Verify `/research` on Lean tasks works with old version
   - Document rollback reason

2. **Investigation**:
   - Review error logs
   - Compare with researcher.md delegation pattern
   - Identify specific failure point

3. **Retry**:
   - Fix identified issue
   - Test with simple task first
   - Gradually increase complexity

### Contingency Plan

If status-sync-manager delegation fails:
- Log error with details
- Continue with artifact creation (research report exists)
- Document manual recovery steps
- Create follow-up task to fix status-sync-manager

If git-workflow-manager delegation fails:
- Log warning (non-critical)
- Continue with status update (status-sync-manager succeeded)
- Document manual commit steps
- User can commit manually if needed

---

## Success Metrics

### Functional Metrics

- [ ] 100% of Lean research tasks update status to `[RESEARCHED]`
- [ ] 100% of Lean research tasks create git commits
- [ ] 100% of Lean research tasks link artifacts in TODO.md
- [ ] 0% regression in research quality

### Technical Metrics

- [ ] 0 direct file manipulation calls in lean-research-agent.md
- [ ] 100% delegation to status-sync-manager and git-workflow-manager
- [ ] 100% match with researcher.md delegation pattern
- [ ] 0 summary artifact references (except JSON return metadata)

### Quality Metrics

- [ ] Error handling matches researcher.md pattern
- [ ] Documentation is clear and accurate
- [ ] XML structure is valid
- [ ] Code is maintainable and consistent

---

## Dependencies

### Upstream Dependencies

- **Task 290**: Research completed (identifies root cause)
- **Task 289**: Lean subagent step naming fixed (completed)
- **Task 283**: General subagent delegation pattern established (completed)

### Downstream Dependencies

None (this is a leaf task)

### External Dependencies

- **status-sync-manager**: Must be working correctly (proven by researcher.md)
- **git-workflow-manager**: Must be working correctly (proven by researcher.md)
- **researcher.md**: Reference implementation for delegation pattern

---

## Notes

### Research Integration

This plan integrates findings from:
- Task 291 research report (root cause analysis)
- Task 290 research report (symptom identification)
- researcher.md implementation (reference pattern)

### Alignment with Standards

- Follows subagent-return-format.md (summary in JSON, not file)
- Follows artifact-management.md (single artifact for research)
- Follows delegation.md (status-sync-manager and git-workflow-manager)
- Follows status-markers.md (two-phase status updates)

### Future Work

After this task:
- Task 285: Audit and fix lean-planner and lean-implementation-agent
- Ensure all Lean subagents use consistent delegation pattern
- Update documentation to reference Lean subagent examples

---

## Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 001 | 2026-01-04 | Planner | Initial plan created |
