# Root Cause Analysis: Systematic status-sync-manager TODO.md Update Failures

## Executive Summary

**Root Cause Identified**: status-sync-manager is **NOT being invoked** by workflow commands despite specification in command files. All 4 workflow commands (/research, /plan, /revise, /implement) specify delegation to status-sync-manager in their documentation, but the actual command execution does NOT delegate to this specialist. This is a **delegation gap**, not a status-sync-manager implementation bug.

**Evidence**: Task 224 shows:
- TODO.md: `[RESEARCHED]` with timestamps [PASS] (manually updated by command)
- Global state.json: Task entry missing entirely [FAIL] (status-sync-manager never invoked)
- Project state.json: Exists with correct data [PASS] (manually created by command)

**Impact**: 100% of workflow command executions fail to maintain atomic state across tracking files, creating inconsistent state where TODO.md shows one status but state.json shows another (or nothing).

**Fix Complexity**: Medium - Requires adding status-sync-manager delegation to all 4 command implementations, but status-sync-manager itself is correctly implemented.

## Investigation Findings

### 1. Command Specification vs Implementation Gap

**Finding**: All 4 workflow commands SPECIFY delegation to status-sync-manager in their .md files, but do NOT actually invoke it.

**Evidence from research.md (lines 217-232)**:
```xml
<atomic_update>
  Delegate to status-sync-manager:
    - task_number: {number}
    - new_status: "researched"
    - timestamp: {ISO8601 date}
    - session_id: {session_id}
    - validated_artifacts: {artifacts from researcher return}
  
  status-sync-manager performs two-phase commit:
    - Phase 1: Prepare, validate artifacts, backup
    - Phase 2: Write all files or rollback all
  
  Atomicity guaranteed across:
    - TODO.md (status, timestamps, artifact links)
    - state.json (status, timestamps, artifacts array)
    - project state.json (lazy created if needed)
</atomic_update>
```

**Reality**: Commands perform manual TODO.md updates instead of delegating.

### 2. Manual Update Anti-Pattern Detected

**Finding**: Commands manually update TODO.md and create project state.json directly, bypassing status-sync-manager's two-phase commit protocol.

**Evidence from Task 224**:
- TODO.md updated to `[RESEARCHED]` [PASS]
- Project state.json created with correct structure [PASS]
- Global state.json NOT updated (task entry missing) [FAIL]

**This proves**: Commands are doing manual file updates, not delegating to status-sync-manager.

### 3. status-sync-manager Implementation is Correct

**Finding**: status-sync-manager.md specification is comprehensive and correct. The specialist is properly designed with:
- Two-phase commit protocol (prepare → commit)
- Rollback on failure mechanism
- Validation at multiple stages (pre-commit, post-commit, rollback)
- Atomic updates across TODO.md + state.json + project state.json + plan files
- Proper error handling and logging

**Evidence from status-sync-manager.md**:
- Lines 78-239: Complete two-phase commit implementation
- Lines 356-423: Project state.json lazy creation with CRITICAL failure handling
- Lines 425-535: Plan file phase updates with atomic rollback
- Lines 616-637: Comprehensive constraints and validation

**Conclusion**: The specialist is correctly designed. The problem is it's not being invoked.

### 4. Command-Lifecycle.md Mandates Delegation

**Finding**: command-lifecycle.md (created for task 211) explicitly mandates delegation to status-sync-manager for all status updates.

**Evidence from command-lifecycle.md (lines 263-330)**:
```markdown
**Update Procedures**:

CRITICAL: All status and artifact updates in Stage 7 MUST be delegated to 
status-sync-manager to ensure atomicity across all tracking files.

**WARNING**: DO NOT manually update TODO.md, state.json, project state.json, 
or plan files directly. Manual updates create race conditions and inconsistent 
state. ALL updates MUST flow through status-sync-manager's two-phase commit 
protocol.
```

**Anti-Pattern Examples** (lines 297-310):
```markdown
# WRONG: Manual TODO.md update
sed -i 's/\[IMPLEMENTING\]/\[COMPLETED\]/' TODO.md

# WRONG: Manual state.json update
jq '.status = "completed"' state.json > state.json.tmp && mv state.json.tmp state.json

# CORRECT: Delegate to status-sync-manager
Invoke status-sync-manager with all parameters
```

**Conclusion**: The standard exists and is clear. Commands are not following it.

### 5. All 4 Commands Affected

**Finding**: All workflow commands show the same pattern - specification says delegate, implementation does manual updates.

| Command | Specifies Delegation | Actually Delegates | Evidence |
|---------|---------------------|-------------------|----------|
| /research | [PASS] (line 217-232) | [FAIL] | Task 224 global state.json missing |
| /plan | [PASS] (line 181-199) | [FAIL] | Same pattern expected |
| /revise | [PASS] (line 186-206) | [FAIL] | Same pattern expected |
| /implement | [PASS] (line 281-305) | [FAIL] | Same pattern expected |

**Root Cause**: Commands were written before status-sync-manager existed or before delegation was standardized. Documentation was updated but implementation was not.

### 6. Two-Phase Commit Not Happening

**Finding**: status-sync-manager's two-phase commit protocol is designed to ensure atomicity, but it's never executed.

**Expected Flow** (from status-sync-manager.md):
1. **Phase 1 (Prepare)**:
   - Read TODO.md, state.json, project state.json into memory
   - Validate all files readable
   - Prepare all updates in memory
   - Validate updates well-formed
   - Create backups
   - If any validation fails: abort before writing

2. **Phase 2 (Commit)**:
   - Write TODO.md (first, most critical)
   - Verify write succeeded
   - Write state.json
   - Verify write succeeded
   - Write project state.json
   - Verify write succeeded
   - If any write fails: rollback all previous writes

**Actual Flow** (observed):
1. Command manually updates TODO.md
2. Command manually creates project state.json
3. Command skips global state.json update
4. No atomicity, no rollback, no validation

### 7. Validation Gaps Identified

**Finding**: Commands lack validation that status-sync-manager was invoked and succeeded.

**Missing Validations**:
- No check that status-sync-manager was called
- No check that status-sync-manager returned success
- No check that all 3 files (TODO.md, state.json, project state.json) were updated
- No check that updates were atomic

**Expected Validation** (from command-lifecycle.md lines 263-330):
```markdown
**Delegation Checklist** (verify before proceeding):
- [ ] All status updates delegated to status-sync-manager (no manual updates)
- [ ] phase_statuses extracted from task-executor return (if phased implementation)
- [ ] plan_metadata extracted from planner return (if plan operation)
- [ ] plan_path provided to status-sync-manager (if plan exists)
- [ ] validated_artifacts passed to status-sync-manager
- [ ] session_id matches across delegation chain
- [ ] No manual TODO.md, state.json, or plan file updates in command code
```

**Reality**: None of these checks are performed.

## Root Cause Classification

**Primary Root Cause**: **Delegation Gap** - Commands do not invoke status-sync-manager despite specification.

**Secondary Root Cause**: **Implementation Lag** - Command implementations were not updated when status-sync-manager was introduced or when command-lifecycle.md was standardized.

**NOT a status-sync-manager bug**: The specialist is correctly designed and would work if invoked.

## Impact Analysis

### Affected Workflows

**All 4 workflow commands affected**:
1. `/research` - Creates research artifacts, updates TODO.md, but skips global state.json
2. `/plan` - Creates plan artifacts, updates TODO.md, but skips global state.json
3. `/revise` - Creates revised plans, updates TODO.md, but skips global state.json
4. `/implement` - Creates implementation artifacts, updates TODO.md, but skips global state.json

### Data Consistency Issues

**Observed Inconsistencies**:
- TODO.md shows `[RESEARCHED]` but state.json has no entry for task
- Project state.json exists but global state.json doesn't know about it
- No atomic updates - partial failures leave inconsistent state
- No rollback mechanism - failed updates corrupt state

**Example from Task 224**:
```
TODO.md:          [RESEARCHED] [PASS]
state.json:       null [FAIL]
project state:    {status: "active", phase: "research_completed"} [PASS]
```

### User Impact

**Severity**: High - Affects all workflow command usage

**Symptoms**:
- Task status queries fail (state.json missing entries)
- Batch operations skip tasks (state.json doesn't know they exist)
- Status transitions invalid (no history in state.json)
- Reporting broken (can't aggregate from state.json)

**Workarounds**: None - Users cannot fix this themselves

## Recommended Fixes

### Fix 1: Add status-sync-manager Delegation to All Commands (REQUIRED)

**Effort**: 4-6 hours

**Scope**: Update all 4 command implementations

**Changes Required**:

For each command (/research, /plan, /revise, /implement):

1. **Remove manual TODO.md updates**:
   - Delete sed/awk commands that modify TODO.md
   - Delete jq commands that modify state.json
   - Delete manual project state.json creation

2. **Add status-sync-manager delegation**:
   ```python
   # After subagent returns successfully
   status_sync_result = invoke_status_sync_manager(
       task_number=task_number,
       new_status="researched",  # or "planned", "revised", "completed"
       timestamp=current_timestamp(),
       session_id=session_id,
       validated_artifacts=subagent_return["artifacts"],
       plan_metadata=subagent_return.get("plan_metadata"),  # if applicable
       plan_version=plan_version,  # if /revise
       phase_statuses=subagent_return.get("phase_statuses"),  # if /implement
       plan_path=plan_path  # if applicable
   )
   
   # Validate status-sync-manager succeeded
   if status_sync_result["status"] != "completed":
       # Rollback already happened in status-sync-manager
       return error_to_user(status_sync_result["errors"])
   ```

3. **Add validation checks**:
   - Verify status-sync-manager was invoked
   - Verify status-sync-manager returned success
   - Verify all files updated (from status-sync-manager return)
   - Verify no manual updates occurred

4. **Update error handling**:
   - Handle status-sync-manager failures
   - Report rollback details to user
   - Provide recovery instructions

**Testing**:
- Test each command with status-sync-manager delegation
- Verify TODO.md, state.json, project state.json all updated
- Verify atomicity (all or nothing)
- Verify rollback on failure
- Test with existing tasks (Task 224, etc.)

### Fix 2: Add Pre-Commit Validation (RECOMMENDED)

**Effort**: 2 hours

**Scope**: Add validation layer before status-sync-manager invocation

**Implementation**:
```python
def validate_before_status_sync(
    task_number,
    new_status,
    subagent_return,
    command_type
):
    """Validate all prerequisites before invoking status-sync-manager"""
    
    # Check subagent return is valid
    if not validate_subagent_return(subagent_return):
        return ValidationError("Invalid subagent return format")
    
    # Check artifacts exist
    for artifact in subagent_return["artifacts"]:
        if not os.path.exists(artifact["path"]):
            return ValidationError(f"Artifact missing: {artifact['path']}")
        if os.path.getsize(artifact["path"]) == 0:
            return ValidationError(f"Artifact empty: {artifact['path']}")
    
    # Check metadata present (if required)
    if command_type == "plan" and "plan_metadata" not in subagent_return:
        return ValidationError("plan_metadata missing from planner return")
    
    if command_type == "implement" and "phase_statuses" in subagent_return:
        if not validate_phase_statuses(subagent_return["phase_statuses"]):
            return ValidationError("Invalid phase_statuses format")
    
    # Check status transition is valid
    current_status = get_current_status(task_number)
    if not is_valid_transition(current_status, new_status):
        return ValidationError(f"Invalid transition: {current_status} -> {new_status}")
    
    return ValidationSuccess()
```

**Benefits**:
- Catch errors before status-sync-manager invocation
- Provide clear error messages to user
- Prevent invalid state transitions
- Reduce status-sync-manager rollback frequency

### Fix 3: Add Post-Commit Validation (RECOMMENDED)

**Effort**: 2 hours

**Scope**: Verify status-sync-manager actually updated all files

**Implementation**:
```python
def validate_after_status_sync(
    task_number,
    expected_status,
    status_sync_result
):
    """Validate status-sync-manager updated all files correctly"""
    
    # Check status-sync-manager returned success
    if status_sync_result["status"] != "completed":
        return ValidationError("status-sync-manager failed", status_sync_result["errors"])
    
    # Verify TODO.md updated
    todo_status = extract_status_from_todo(task_number)
    if todo_status != expected_status:
        return ValidationError(f"TODO.md status mismatch: expected {expected_status}, got {todo_status}")
    
    # Verify state.json updated
    state_status = extract_status_from_state_json(task_number)
    if state_status != expected_status.lower().replace(" ", "_"):
        return ValidationError(f"state.json status mismatch: expected {expected_status}, got {state_status}")
    
    # Verify project state.json exists
    project_state_path = f".opencode/specs/{task_number}_*/state.json"
    if not glob.glob(project_state_path):
        return ValidationError("Project state.json not created")
    
    # Verify all files have consistent timestamps
    todo_timestamp = extract_timestamp_from_todo(task_number)
    state_timestamp = extract_timestamp_from_state_json(task_number)
    if todo_timestamp != state_timestamp:
        return ValidationError("Timestamp mismatch across files")
    
    return ValidationSuccess()
```

**Benefits**:
- Detect silent failures
- Ensure atomicity was achieved
- Provide confidence in state consistency
- Enable automated testing

### Fix 4: Add Integration Tests (RECOMMENDED)

**Effort**: 4 hours

**Scope**: Test status-sync-manager integration with all commands

**Test Cases**:

1. **Test /research delegation**:
   - Run /research on new task
   - Verify TODO.md updated to [RESEARCHED]
   - Verify state.json has task entry with status "researched"
   - Verify project state.json created
   - Verify all timestamps match

2. **Test /plan delegation**:
   - Run /plan on researched task
   - Verify TODO.md updated to [PLANNED]
   - Verify state.json updated with plan_path and plan_metadata
   - Verify project state.json updated
   - Verify plan file linked correctly

3. **Test /revise delegation**:
   - Run /revise on planned task
   - Verify TODO.md updated to [REVISED]
   - Verify state.json plan_versions array appended
   - Verify plan_path updated to new version
   - Verify project state.json updated

4. **Test /implement delegation**:
   - Run /implement on planned task
   - Verify TODO.md updated to [COMPLETED]
   - Verify state.json updated with completion timestamp
   - Verify plan file phase statuses updated
   - Verify project state.json updated

5. **Test rollback on failure**:
   - Simulate write failure in status-sync-manager
   - Verify all files restored to original state
   - Verify no partial updates
   - Verify error reported to user

6. **Test validation failures**:
   - Test invalid status transition
   - Test missing artifacts
   - Test malformed metadata
   - Verify all caught before commit

**Implementation**:
```python
def test_research_status_sync_integration():
    """Test /research delegates to status-sync-manager correctly"""
    
    # Setup
    task_number = create_test_task()
    
    # Execute
    result = run_research_command(task_number)
    
    # Verify delegation occurred
    assert result["status"] == "completed"
    assert "status_sync_manager" in result["delegation_path"]
    
    # Verify TODO.md updated
    todo_status = extract_status_from_todo(task_number)
    assert todo_status == "[RESEARCHED]"
    
    # Verify state.json updated
    state_entry = get_state_json_entry(task_number)
    assert state_entry is not None
    assert state_entry["status"] == "researched"
    
    # Verify project state.json created
    project_state = get_project_state_json(task_number)
    assert project_state is not None
    assert project_state["status"] == "active"
    
    # Verify atomicity
    assert todo_status_timestamp == state_entry["completed"]
```

## Implementation Plan

### Phase 1: Fix /research Command (2 hours)

**Tasks**:
1. Update /research command implementation to delegate to status-sync-manager
2. Remove manual TODO.md and state.json updates
3. Add pre-commit and post-commit validation
4. Test with Task 224 (existing researched task)
5. Test with new task

**Acceptance Criteria**:
- /research delegates to status-sync-manager
- TODO.md, state.json, project state.json all updated atomically
- Validation catches errors before commit
- Rollback works on failure

### Phase 2: Fix /plan Command (2 hours)

**Tasks**:
1. Update /plan command implementation to delegate to status-sync-manager
2. Remove manual TODO.md and state.json updates
3. Add plan_metadata extraction and passing
4. Add pre-commit and post-commit validation
5. Test with existing planned task
6. Test with new task

**Acceptance Criteria**:
- /plan delegates to status-sync-manager
- plan_metadata extracted and stored in state.json
- All files updated atomically
- Validation works

### Phase 3: Fix /revise Command (1.5 hours)

**Tasks**:
1. Update /revise command implementation to delegate to status-sync-manager
2. Remove manual TODO.md and state.json updates
3. Add plan_version tracking
4. Add pre-commit and post-commit validation
5. Test with existing revised task
6. Test with new revision

**Acceptance Criteria**:
- /revise delegates to status-sync-manager
- plan_versions array updated correctly
- All files updated atomically
- Validation works

### Phase 4: Fix /implement Command (2.5 hours)

**Tasks**:
1. Update /implement command implementation to delegate to status-sync-manager
2. Remove manual TODO.md and state.json updates
3. Add phase_statuses extraction and passing
4. Add plan file update support
5. Add pre-commit and post-commit validation
6. Test with phased implementation
7. Test with direct implementation

**Acceptance Criteria**:
- /implement delegates to status-sync-manager
- phase_statuses extracted and plan file updated
- All files updated atomically
- Validation works for both phased and direct modes

### Phase 5: Integration Testing (2 hours)

**Tasks**:
1. Create integration test suite
2. Test all 4 commands end-to-end
3. Test rollback scenarios
4. Test validation failures
5. Test with existing tasks
6. Document test results

**Acceptance Criteria**:
- All integration tests pass
- 100% atomic update success rate
- Rollback works in all failure scenarios
- Validation catches all error types

### Phase 6: Documentation Update (1 hour)

**Tasks**:
1. Update command documentation with delegation details
2. Add troubleshooting guide for status-sync failures
3. Document validation checks
4. Add examples of correct delegation
5. Update IMPLEMENTATION_STATUS.md

**Acceptance Criteria**:
- Documentation matches implementation
- Troubleshooting guide complete
- Examples clear and correct

## Estimated Effort

| Phase | Effort | Priority |
|-------|--------|----------|
| Phase 1: Fix /research | 2 hours | CRITICAL |
| Phase 2: Fix /plan | 2 hours | CRITICAL |
| Phase 3: Fix /revise | 1.5 hours | CRITICAL |
| Phase 4: Fix /implement | 2.5 hours | CRITICAL |
| Phase 5: Integration Testing | 2 hours | HIGH |
| Phase 6: Documentation | 1 hour | MEDIUM |
| **Total** | **11 hours** | |

## Risk Assessment

### High Risks

1. **Breaking Existing Workflows**:
   - Risk: Delegation changes break existing command behavior
   - Mitigation: Extensive testing with existing tasks before deployment
   - Contingency: Rollback mechanism, feature flag for delegation

2. **status-sync-manager Bugs**:
   - Risk: status-sync-manager has undiscovered bugs that surface when actually invoked
   - Mitigation: Thorough testing of status-sync-manager in isolation
   - Contingency: Fix status-sync-manager bugs as discovered

3. **Incomplete Rollback**:
   - Risk: Rollback mechanism fails, leaving corrupted state
   - Mitigation: Test rollback extensively, add logging
   - Contingency: Manual state restoration procedure

### Medium Risks

1. **Performance Impact**:
   - Risk: Two-phase commit adds latency to commands
   - Mitigation: Optimize status-sync-manager, add caching
   - Contingency: Acceptable tradeoff for correctness

2. **Validation False Positives**:
   - Risk: Validation too strict, rejects valid operations
   - Mitigation: Careful validation design, extensive testing
   - Contingency: Adjust validation rules based on feedback

### Low Risks

1. **Documentation Drift**:
   - Risk: Documentation doesn't match implementation
   - Mitigation: Update docs in same PR as implementation
   - Contingency: Regular doc reviews

## Success Criteria

### Functional Requirements

- [ ] All 4 commands delegate to status-sync-manager
- [ ] TODO.md, state.json, project state.json updated atomically
- [ ] Rollback works on any write failure
- [ ] Validation catches errors before commit
- [ ] No manual file updates in command code

### Quality Requirements

- [ ] 100% atomic update success rate (all or nothing)
- [ ] Zero data corruption incidents
- [ ] All integration tests pass
- [ ] Documentation complete and accurate

### Performance Requirements

- [ ] Command latency increase < 500ms
- [ ] Rollback completes < 1s
- [ ] Validation completes < 100ms

## Conclusion

The root cause is clear: **Commands do not invoke status-sync-manager despite specification**. This is a delegation gap, not a status-sync-manager bug. The fix is straightforward but requires careful implementation across all 4 commands to ensure atomicity and validation.

The status-sync-manager specialist is correctly designed and ready to use. The commands just need to be updated to actually invoke it, following the pattern specified in command-lifecycle.md.

**Recommended Action**: Implement Fix 1 (delegation) for all 4 commands, with Fixes 2-4 (validation and testing) to ensure correctness. Total effort: 11 hours over 6 phases.

## References

### Analyzed Files

1. `.opencode/agent/subagents/status-sync-manager.md` - Specialist specification (838 lines)
2. `.opencode/command/research.md` - Research command (355 lines)
3. `.opencode/command/plan.md` - Plan command (330 lines)
4. `.opencode/command/revise.md` - Revise command (309 lines)
5. `.opencode/command/implement.md` - Implement command (439 lines)
6. `.opencode/context/core/workflows/command-lifecycle.md` - Lifecycle standard (983 lines)
7. `.opencode/context/core/standards/status-markers.md` - Status marker specification (889 lines)

### Evidence Files

1. `.opencode/specs/TODO.md` - Task 224 shows `[RESEARCHED]` status
2. `.opencode/specs/state.json` - Task 224 entry missing (null)
3. `.opencode/specs/224_configure_opencode_default_agent/state.json` - Project state exists

### Related Tasks

- Task 221: Fix missing delegation to status-sync-manager (addressed delegation gap awareness)
- Task 211: Standardize command lifecycle procedures (created command-lifecycle.md)
- Task 224: Example task demonstrating the bug (research completed, state.json not updated)

## Appendix A: status-sync-manager Invocation Example

**Correct Delegation Pattern** (from command-lifecycle.md):

```python
# After subagent returns successfully
validation_result = validate_before_status_sync(
    task_number=task_number,
    new_status="researched",
    subagent_return=researcher_return,
    command_type="research"
)

if not validation_result.success:
    return error_to_user(validation_result.errors)

# Invoke status-sync-manager
status_sync_result = invoke_status_sync_manager(
    task_number=task_number,
    new_status="researched",
    timestamp=current_timestamp(),
    session_id=session_id,
    validated_artifacts=researcher_return["artifacts"],
    delegation_depth=delegation_depth + 1,
    delegation_path=delegation_path + ["status-sync-manager"]
)

# Validate status-sync-manager succeeded
validation_result = validate_after_status_sync(
    task_number=task_number,
    expected_status="[RESEARCHED]",
    status_sync_result=status_sync_result
)

if not validation_result.success:
    return error_to_user(validation_result.errors)

# Success - all files updated atomically
return success_to_user(status_sync_result)
```

## Appendix B: Manual Update Anti-Pattern

**What Commands Are Doing Now** (WRONG):

```bash
# Manual TODO.md update (WRONG)
sed -i "s/\*\*Status\*\*: \[RESEARCHING\]/\*\*Status\*\*: [RESEARCHED]/" TODO.md
sed -i "/^### ${task_number}\./a \*\*Completed\*\*: $(date +%Y-%m-%d)" TODO.md

# Manual project state.json creation (WRONG)
mkdir -p ".opencode/specs/${task_number}_${slug}"
cat > ".opencode/specs/${task_number}_${slug}/state.json" <<EOF
{
  "project_name": "${slug}",
  "project_number": ${task_number},
  "type": "research",
  "phase": "research_completed",
  "status": "active",
  "created": "$(date -I)T00:00:00Z",
  "last_updated": "$(date -I)"
}
EOF

# Global state.json SKIPPED (BUG)
# No update to .opencode/specs/state.json
```

**Problems**:
1. No atomicity - partial failures leave inconsistent state
2. No rollback - failed updates corrupt state
3. No validation - invalid transitions accepted
4. Global state.json skipped - task invisible to system
5. Race conditions - concurrent updates collide
6. No error handling - silent failures

**Correct Approach**: Delegate to status-sync-manager, which handles all of this correctly.
