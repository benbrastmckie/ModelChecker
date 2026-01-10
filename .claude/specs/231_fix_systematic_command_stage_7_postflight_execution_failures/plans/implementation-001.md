# Implementation Plan: Fix Systematic Command Stage 7 (Postflight) Execution Failures

**Project Number**: 231  
**Type**: Bugfix  
**Priority**: Critical  
**Complexity**: Medium  
**Estimated Hours**: 10  
**Phases**: 5

---

## Metadata

- **Created**: 2025-12-29T01:57:10Z
- **Language**: markdown
- **Supersedes**: Tasks 227, 228, 229 (abandoned due to incorrect root cause)
- **Research**: [research-001.md](../reports/research-001.md)

---

## Overview

Fix systematic Stage 7 (Postflight) execution failures across all workflow commands (/plan, /research, /implement, /revise). Research identified 5 critical root causes causing Claude to skip or incompletely execute Stage 7, resulting in successful artifact creation but incomplete TODO.md and state.json updates.

**Root Causes**:
1. **Weak Prompting**: Descriptive language ("should", "can") instead of imperative commands ("MUST", "EXECUTE")
2. **No Validation Checkpoints**: No explicit verification that Stage 7 completed before Stage 8 returns
3. **Missing Error Handling**: Commands proceed to Stage 8 even if Stage 7 fails
4. **Implicit Delegation Syntax**: status-sync-manager invocation described narratively, not as explicit delegation step
5. **No Orchestrator Validation**: Orchestrator lacks stage completion tracking and validation

**Solution**: Implement 5 corresponding fixes strengthening Stage 7 prompting, adding validation checkpoints, implementing error handling, using explicit delegation syntax, and adding orchestrator stage validation.

---

## Research Inputs

### Key Findings from Research

1. **Weak Prompting Examples** (research-001.md lines 660-847):
   - Current: "Verify planner returned validation success" (descriptive)
   - Strong: "EXECUTE: Verify planner returned validation success. ABORT if validation failed." (imperative)
   - Current: "Delegate to status-sync-manager:" (narrative)
   - Strong: "INVOKE status-sync-manager with the following parameters:" (explicit)

2. **Missing Checkpoints** (research-001.md lines 849-900):
   - No checkpoint between Stage 7 and Stage 8
   - Claude can skip Stage 7 and proceed to Stage 8 unchecked
   - Proposed: Explicit checkpoint validation before Stage 8

3. **Missing Error Handling** (research-001.md lines 902-1031):
   - No explicit error handling for status-sync-manager failures
   - No error handling for git-workflow-manager failures
   - No recovery instructions in error messages

4. **Implicit Delegation** (research-001.md lines 1033-1119):
   - Current delegation is narrative description
   - Should use explicit invocation syntax similar to orchestrator
   - Need explicit timeout, return validation, on-disk verification

5. **Orchestrator Gaps** (research-001.md lines 1121-1261):
   - Orchestrator has 13 stages but no command stage tracking
   - Should track command stage progression
   - Should validate Stage 7 completion before accepting return

### Proposed Fixes Summary

- **Fix #1**: Strengthen Stage 7 prompting with imperative commands (research-001.md lines 1265-1366)
- **Fix #2**: Add validation checkpoints (research-001.md lines 1368-1470)
- **Fix #3**: Add comprehensive error handling (research-001.md lines 1472-1603)
- **Fix #4**: Use explicit delegation syntax (research-001.md lines 1605-1747)
- **Fix #5**: Add orchestrator stage validation (research-001.md lines 1749-1900)

### Evidence from Task History

- **Task 224**: Plan created [PASS], TODO.md manual [PASS], state.json [FAIL] (research-001.md lines 600-615)
- **Task 229**: Plan created [PASS], tracking manual intervention required (research-001.md lines 617-628)
- **Pattern**: Artifacts succeed, Stage 7 skipped, tracking incomplete

---

## Success Criteria

1. **Stage 7 Execution Rate**: 100% Stage 7 execution for all 4 commands
2. **Checkpoint Validation**: All checkpoints pass before Stage 8
3. **Error Handling**: All error cases handled with recovery instructions
4. **Delegation Syntax**: Explicit invocation with timeout and validation
5. **Orchestrator Validation**: Stage completion tracked and validated
6. **Test Coverage**: All 4 commands tested with real tasks
7. **No Manual Intervention**: TODO.md and state.json update automatically

---

## Phase 1: Strengthen Stage 7 Prompting in /plan Command [COMPLETED]

- **Completed**: 2025-12-29T02:05:00Z

**Objective**: Replace descriptive language with imperative commands in plan.md Stage 7

**Duration**: 2 hours

**Steps**:

1. **Update validation_delegation section** (plan.md ~line 164):
   - Replace "Verify planner returned validation success" with "EXECUTE: Verify planner returned validation success"
   - Add numbered steps: STEP 1, STEP 2, etc.
   - Add explicit error handling: "IF validation fails: ABORT with error"
   - Add logging: "LOG: Planner validation: {result}"
   - Reference: research-001.md lines 679-716

2. **Update atomic_update section** (plan.md ~line 184):
   - Replace "Delegate to status-sync-manager:" with "INVOKE status-sync-manager subagent"
   - Add step-by-step structure:
     - STEP 1: PREPARE delegation context
     - STEP 2: INVOKE status-sync-manager
     - STEP 3: WAIT for return (max 60s)
     - STEP 4: VALIDATE return
     - STEP 5: VERIFY files on disk
   - Add explicit timeout: 60s
   - Add return validation checks
   - Add on-disk verification (TODO.md, state.json)
   - Reference: research-001.md lines 750-836

3. **Update git_commit section** (plan.md ~line 177):
   - Replace "Commit only if status == 'completed'" with explicit conditional:
     ```xml
     IF status == "completed":
       EXECUTE git commit
     ELSE:
       SKIP git commit
       LOG: "Skipping git commit (status: {status})"
     ```
   - Add git-workflow-manager invocation steps
   - Add timeout: 120s
   - Reference: research-001.md lines 1060-1119

4. **Add comprehensive error handling**:
   - Add <error_handling> block after atomic_update
   - Define error cases:
     - status_sync_manager_failed
     - status_sync_manager_timeout
     - git_commit_failed (non-critical)
     - validation_failed
   - Include recovery instructions in error messages
   - Reference: research-001.md lines 929-1031

5. **Test /plan command**:
   - Create test task: `/task "Test /plan Stage 7 execution"`
   - Run: `/plan {task_number}`
   - Verify:
     - Plan artifact created
     - TODO.md updated to [PLANNED]
     - state.json updated to "planned"
     - Plan link added to TODO.md
     - Git commit created
   - Check logs for "EXECUTE", "INVOKE", "LOG" messages
   - Verify no errors in errors.json

**Acceptance Criteria**:
- [ ] All descriptive language replaced with imperative commands
- [ ] All steps numbered and sequenced
- [ ] All conditionals explicit (IF...THEN...ELSE)
- [ ] All error cases handled with recovery instructions
- [ ] Logging added at key points
- [ ] Test with real task succeeds
- [ ] TODO.md and state.json updated automatically

---

## Phase 2: Add Validation Checkpoints to All Commands [COMPLETED]

- **Completed**: 2025-12-29T02:06:00Z

**Objective**: Add explicit checkpoints preventing Stage 8 execution if Stage 7 incomplete

**Duration**: 2 hours

**Steps**:

1. **Add Stage 7 completion checkpoint to /plan** (plan.md after Stage 7):
   ```xml
   <stage_7_completion_checkpoint>
     VERIFY all Stage 7 steps completed:
       - [ ] Planner return validated
       - [ ] Plan artifact exists on disk
       - [ ] status-sync-manager invoked
       - [ ] status-sync-manager returned "completed"
       - [ ] TODO.md updated on disk (verified)
       - [ ] state.json updated on disk (verified)
       - [ ] git-workflow-manager invoked (if status == "completed")
     
     IF any checkpoint fails:
       - ABORT Stage 8
       - RETURN error to user with checkpoint failure details
       - Include manual recovery instructions
     
     IF all checkpoints pass:
       - LOG: "Stage 7 (Postflight) completed successfully"
       - PROCEED to Stage 8
   </stage_7_completion_checkpoint>
   ```
   - Reference: research-001.md lines 1376-1394

2. **Add Stage 8 prerequisite to /plan** (plan.md Stage 8 start):
   ```xml
   <stage id="8" name="ReturnSuccess">
     <prerequisite>
       REQUIRE: Stage 7 completion checkpoint passed
       IF Stage 7 not completed: ABORT with error
     </prerequisite>
     <!-- Stage 8 content -->
   </stage>
   ```
   - Reference: research-001.md lines 1398-1407

3. **Add intermediate checkpoints within Stage 7**:
   - After validation: `CHECKPOINT: Validation completed`
   - After status-sync-manager: `CHECKPOINT: Atomic update completed`
   - After git commit: `CHECKPOINT: Git commit completed (if applicable)`
   - Each checkpoint lists verification items
   - Each checkpoint specifies abort behavior on failure
   - Reference: research-001.md lines 1418-1445

4. **Apply checkpoint pattern to /research, /implement, /revise**:
   - Copy checkpoint structure from /plan
   - Adjust for command-specific validations
   - /research: 1 artifact (research report)
   - /implement: Multiple artifacts + phase_statuses
   - /revise: Plan artifact + plan_version
   - Reference: research-001.md lines 1415-1470

5. **Test checkpoint enforcement**:
   - Modify /plan to skip status-sync-manager (simulate failure)
   - Run: `/plan {task_number}`
   - Verify:
     - Checkpoint failure detected
     - Stage 8 not executed
     - Error returned with checkpoint details
   - Restore /plan
   - Retry and verify success

**Acceptance Criteria**:
- [ ] Stage 7 completion checkpoint added to all 4 commands
- [ ] Stage 8 prerequisite added to all 4 commands
- [ ] Intermediate checkpoints added within Stage 7
- [ ] Checkpoint failure prevents Stage 8 execution
- [ ] Error messages include checkpoint status
- [ ] Test with simulated failure succeeds
- [ ] Test with normal execution succeeds

---

## Phase 3: Implement Explicit Delegation Syntax [COMPLETED]

- **Completed**: 2025-12-29T02:07:00Z

**Objective**: Replace narrative delegation with explicit invocation syntax

**Duration**: 2.5 hours

**Steps**:

1. **Update status-sync-manager delegation in /plan** (plan.md ~line 184):
   ```xml
   <atomic_update>
     <action>INVOKE status-sync-manager subagent</action>
     
     <step_1_prepare_delegation>
       PREPARE delegation context:
       ```json
       {
         "task_number": {number},
         "new_status": "planned",
         "timestamp": "{ISO8601 date}",
         "session_id": "{session_id}",
         "validated_artifacts": {artifacts from planner return},
         "plan_path": {plan_path from planner return},
         "plan_metadata": {plan_metadata from planner return},
         "delegation_depth": 2,
         "delegation_path": ["orchestrator", "plan", "status-sync-manager"]
       }
       ```
       
       VALIDATE delegation context:
         - VERIFY all required fields present
         - VERIFY task_number is positive integer
         - VERIFY new_status is valid value ("planned")
         - VERIFY timestamp is ISO8601 format
         - IF validation fails: ABORT with error
     </step_1_prepare_delegation>
     
     <step_2_invoke>
       INVOKE status-sync-manager:
         - Subagent type: "status-sync-manager"
         - Delegation context: {prepared context}
         - Timeout: 60s
         - Delegation mechanism: Per subagent-delegation-guide.md
       
       LOG: "Invoking status-sync-manager for task {number}"
     </step_2_invoke>
     
     <step_3_wait>
       WAIT for status-sync-manager return:
         - Maximum wait: 60s
         - IF timeout: ABORT with error "status-sync-manager timeout after 60s"
     </step_3_wait>
     
     <step_4_validate_return>
       VALIDATE status-sync-manager return:
         - VERIFY return format matches subagent-return-format.md
         - VERIFY status field == "completed" (not "failed" or "partial")
         - VERIFY files_updated includes ["TODO.md", "state.json"]
         - VERIFY rollback_performed == false
         - IF validation fails: ABORT with error details
       
       LOG: "status-sync-manager completed: {files_updated}"
     </step_4_validate_return>
     
     <step_5_verify_on_disk>
       VERIFY files updated on disk:
         - READ TODO.md and verify status marker changed to [PLANNED]
         - READ state.json and verify status field == "planned"
         - IF verification fails: ABORT with error
       
       CHECKPOINT: Atomic update completed successfully
         - [ ] status-sync-manager returned "completed"
         - [ ] TODO.md updated on disk
         - [ ] state.json updated on disk
         - [ ] No rollback performed
     </step_5_verify_on_disk>
   </atomic_update>
   ```
   - Reference: research-001.md lines 750-836

2. **Update git-workflow-manager delegation in /plan** (plan.md ~line 177):
   ```xml
   <git_commit>
     <conditional>
       IF status == "completed":
         PROCEED with git commit
       ELSE:
         SKIP git commit
         LOG: "Skipping git commit (status: {status})"
         PROCEED to checkpoint
     </conditional>
     
     <invocation>
       STEP 1: PREPARE git-workflow-manager delegation
         ```json
         {
           "scope_files": [
             {plan_path from planner return},
             ".opencode/specs/TODO.md",
             ".opencode/specs/state.json",
             ".opencode/specs/{task_number}_{slug}/state.json"
           ],
           "message_template": "task {number}: plan created",
           "task_context": {
             "task_number": {number},
             "description": "plan created"
           },
           "session_id": "{session_id}",
           "delegation_depth": 2,
           "delegation_path": ["orchestrator", "plan", "git-workflow-manager"]
         }
         ```
       
       STEP 2: INVOKE git-workflow-manager
         - Subagent type: "git-workflow-manager"
         - Delegation context: {prepared context}
         - Timeout: 120s
       
       STEP 3: WAIT for git-workflow-manager return
       
       STEP 4: VALIDATE return
         - IF status == "completed":
           * EXTRACT commit_hash from commit_info
           * LOG: "Git commit created: {commit_hash}"
         
         - IF status == "failed":
           * LOG error to errors.json (non-critical)
           * INCLUDE warning in Stage 8 return
           * CONTINUE (git failure doesn't fail command)
     </invocation>
   </git_commit>
   ```
   - Reference: research-001.md lines 1060-1119

3. **Apply explicit delegation to /research, /implement, /revise**:
   - Copy delegation structure from /plan
   - Adjust for command-specific parameters:
     - /research: new_status = "researched"
     - /implement: new_status = "completed" or "partial", add phase_statuses
     - /revise: new_status = "revised", add plan_version, revision_reason
   - Reference: research-001.md lines 1658-1747

4. **Test explicit delegation**:
   - Run: `/plan {task_number}`
   - Check logs for explicit invocation messages:
     - "Invoking status-sync-manager for task {number}"
     - "status-sync-manager completed: {files_updated}"
     - "Git commit created: {commit_hash}"
   - Verify delegations executed with correct timeouts
   - Verify return validation occurred
   - Verify on-disk verification occurred

**Acceptance Criteria**:
- [ ] Explicit delegation syntax added to all 4 commands
- [ ] All delegations have numbered steps (STEP 1, STEP 2, ...)
- [ ] All delegations specify explicit timeouts
- [ ] All delegations validate return format
- [ ] All delegations verify files on disk
- [ ] Logging added at key delegation points
- [ ] Test shows explicit invocation in logs
- [ ] Test verifies delegations execute correctly

---

## Phase 4: Add Comprehensive Error Handling [COMPLETED]

- **Completed**: 2025-12-29T02:08:00Z

**Objective**: Handle all failure modes with recovery instructions

**Duration**: 2 hours

**Steps**:

1. **Add error handling block to /plan Stage 7** (plan.md after atomic_update):
   ```xml
   <error_handling>
     <error_case name="validation_failed">
       IF validation fails before delegation:
         STEP 1: ABORT immediately
           - DO NOT invoke status-sync-manager
           - DO NOT invoke git-workflow-manager
         
         STEP 2: LOG error to errors.json
           ```json
           {
             "type": "validation_failed",
             "severity": "high",
             "context": {
               "command": "plan",
               "task_number": {number},
               "session_id": "{session_id}",
               "stage": 7
             },
             "message": "Planner return validation failed: {error}",
             "fix_status": "not_addressed"
           }
           ```
         
         STEP 3: RETURN validation error to user
           ```
           Error: Validation failed
           
           Details: {validation_error}
           
           Recommendation: Fix planner subagent implementation
           ```
     </error_case>
     
     <error_case name="status_sync_manager_failed">
       IF status-sync-manager returns status == "failed":
         STEP 1: EXTRACT error details
           - error_type: {type from errors array}
           - error_message: {message from errors array}
           - rollback_performed: {boolean}
         
         STEP 2: LOG error to errors.json
           ```json
           {
             "type": "status_sync_failed",
             "severity": "high",
             "context": {
               "command": "plan",
               "task_number": {number},
               "session_id": "{session_id}",
               "stage": 7
             },
             "message": "status-sync-manager failed: {error_message}",
             "fix_status": "not_addressed"
           }
           ```
         
         STEP 3: ABORT Stage 7
           - DO NOT proceed to git commit
           - DO NOT proceed to Stage 8
         
         STEP 4: RETURN error to user
           ```
           Error: Failed to update task status
           
           Details: {error_message}
           
           Artifacts created:
           - Plan: {plan_path}
           
           Manual recovery steps:
           1. Verify plan artifact exists: {plan_path}
           2. Manually update TODO.md status to [PLANNED]
           3. Manually update state.json status to "planned"
           4. Manually link plan in TODO.md
           
           Or retry: /plan {task_number}
           ```
     </error_case>
     
     <error_case name="status_sync_manager_timeout">
       IF status-sync-manager times out after 60s:
         STEP 1: LOG timeout
         
         STEP 2: CHECK files on disk
           - IF TODO.md updated: Partial success
           - IF state.json updated: Partial success
           - IF neither updated: Complete failure
         
         STEP 3: RETURN appropriate error
           ```
           Error: Status update timed out
           
           Status: {partial or complete failure}
           
           Files updated:
           - TODO.md: {yes/no}
           - state.json: {yes/no}
           
           Recommendation: Check status-sync-manager implementation
           Retry: /plan {task_number}
           ```
     </error_case>
     
     <error_case name="git_commit_failed">
       IF git-workflow-manager returns status == "failed":
         STEP 1: LOG error (non-critical)
           - Git failure does not fail the command
           - Artifacts and status updates still valid
         
         STEP 2: CONTINUE to Stage 8
           - Include git failure warning in return
         
         STEP 3: RETURN success with warning
           ```
           Warning: Git commit failed
           
           Plan created successfully: {plan_path}
           Task status updated to [PLANNED]
           
           Manual commit required:
             git add {files}
             git commit -m "task {number}: plan created"
           
           Error: {git_error}
           ```
     </error_case>
   </error_handling>
   ```
   - Reference: research-001.md lines 929-1031

2. **Add error handling to /research, /implement, /revise**:
   - Copy error handling structure from /plan
   - Adjust error messages for command context
   - /implement: Add error_case for phase_statuses_missing
   - Reference: research-001.md lines 1533-1602

3. **Test error handling**:
   - Test validation_failed:
     - Modify planner to return invalid format
     - Verify error caught and user notified
   - Test status_sync_manager_failed:
     - Make TODO.md read-only
     - Verify error caught, recovery instructions provided
     - Restore permissions and retry
   - Test git_commit_failed:
     - Simulate git failure
     - Verify command succeeds with warning
     - Verify manual commit instructions provided

**Acceptance Criteria**:
- [ ] Error handling blocks added to all 4 commands
- [ ] All error cases defined and handled
- [ ] All errors logged to errors.json
- [ ] All error messages include recovery instructions
- [ ] Critical errors abort Stage 7 and Stage 8
- [ ] Non-critical errors (git) allow continuation
- [ ] Test with simulated failures succeeds
- [ ] Error messages are actionable

---

## Phase 5: Add Orchestrator Stage Validation [COMPLETED]

- **Completed**: 2025-12-29T02:10:00Z

**Objective**: Orchestrator validates command stage completion before accepting returns

**Duration**: 1.5 hours

**Steps**:

1. **Extend delegation registry schema** (orchestrator.md delegation_registry):
   ```python
   <delegation_registry>
     <schema>
       ```javascript
       {
         "sess_20251226_abc123": {
           "session_id": "sess_20251226_abc123",
           "command": "plan",
           "subagent": "planner",
           "task_number": 224,
           "language": "markdown",
           "start_time": "2025-12-28T10:00:00Z",
           "timeout": 1800,
           "deadline": "2025-12-28T10:30:00Z",
           "status": "running",
           "delegation_depth": 1,
           "delegation_path": ["orchestrator", "plan", "planner"],
           
           // NEW: Command stage tracking
           "is_command": true,
           "command_stages": {
             "current_stage": 4,
             "stages_completed": [1, 2, 3],
             "stage_7_completed": false,
             "stage_7_artifacts": {
               "status_sync_manager_invoked": false,
               "status_sync_manager_completed": false,
               "todo_md_updated": false,
               "state_json_updated": false,
               "git_commit_created": false
             }
           }
         }
       }
       ```
     </schema>
   </delegation_registry>
   ```
   - Reference: research-001.md lines 1755-1790

2. **Add command stage validation to Step 10 ValidateReturn** (orchestrator.md ~line 478):
   ```python
   <step_10 name="ValidateReturn">
     <action>Validate return against standardized format</action>
     
     <!-- Existing validation_against_schema -->
     
     <command_stage_validation>
       IF delegation is command (not subagent):
         EXTRACT command_execution from registry
         
         VERIFY Stage 7 completed:
           - CHECK command_stages["stage_7_completed"] == true
           - CHECK stage_7_artifacts["status_sync_manager_completed"] == true
           - CHECK stage_7_artifacts["todo_md_updated"] == true
           - CHECK stage_7_artifacts["state_json_updated"] == true
         
         IF any check fails:
           ERROR: "Command returned without completing Stage 7"
           
           STEP 1: LOG error
             ```json
             {
               "type": "stage_7_incomplete",
               "severity": "high",
               "context": {
                 "command": {command_name},
                 "task_number": {task_number},
                 "session_id": {session_id},
                 "stage_7_artifacts": {stage_7_artifacts}
               },
               "message": "Command completed without executing Stage 7 (Postflight)",
               "fix_status": "not_addressed"
             }
             ```
           
           STEP 2: VERIFY files on disk
             - CHECK TODO.md modification time > start_time
             - CHECK state.json modification time > start_time
             - IF files not updated: Confirm Stage 7 failure
           
           STEP 3: RETURN error to user
             ```
             Error: Command completed without updating task status
             
             Stage 7 (Postflight) did not execute:
             - status-sync-manager invoked: {status}
             - TODO.md updated: {status}
             - state.json updated: {status}
             
             Artifacts created: {list}
             
             Manual steps required:
             1. Update TODO.md status to [PLANNED]
             2. Update state.json status to "planned"
             3. Link artifacts in TODO.md
             
             Or retry: /{command} {task_number}
             ```
           
           STEP 4: REJECT return
             - DO NOT proceed to Stage 11
             - DO NOT return success to user
     </command_stage_validation>
   </step_10>
   ```
   - Reference: research-001.md lines 1802-1858

3. **Add verify_file_updated helper function** (orchestrator.md helper_functions):
   ```python
   <function name="verify_file_updated">
     <description>Verify file was modified after command start</description>
     <implementation>
       ```python
       import os
       from datetime import datetime
       
       def verify_file_updated(file_path, start_time):
           """
           Verify file was modified after command start time.
           
           Args:
             file_path: Path to file (relative or absolute)
             start_time: Command start time (ISO 8601 string)
           
           Returns:
             True if file modified after start_time, False otherwise
           """
           # Check file exists
           if not os.path.exists(file_path):
               return False
           
           # Get file modification time
           mod_time = os.path.getmtime(file_path)
           mod_datetime = datetime.fromtimestamp(mod_time)
           
           # Parse start time
           start_datetime = datetime.fromisoformat(start_time)
           
           # Compare
           return mod_datetime > start_datetime
       ```
     </implementation>
   </function>
   ```
   - Reference: research-001.md lines 1863-1899

4. **Update command-lifecycle.md with orchestrator validation**:
   - Add section describing orchestrator stage validation
   - Update Stage 7 (Postflight) documentation
   - Add reference to orchestrator validation mechanism
   - Update error handling patterns

5. **Test orchestrator validation**:
   - Modify /plan to skip Stage 7 (set stage_7_completed = false)
   - Run: `/plan {task_number}`
   - Verify:
     - Orchestrator detects Stage 7 incomplete
     - Orchestrator rejects return
     - Error returned to user with details
     - Files verified on disk
   - Restore /plan
   - Retry and verify success

**Acceptance Criteria**:
- [ ] Delegation registry extended with command_stages tracking
- [ ] Step 10 ValidateReturn includes command stage validation
- [ ] verify_file_updated helper function added
- [ ] command-lifecycle.md updated with orchestrator validation
- [ ] Test with Stage 7 skip detected by orchestrator
- [ ] Test with normal execution succeeds
- [ ] Error messages include stage completion details

---

## Validation and Testing

### Comprehensive Test Suite

**Test 1: All Commands Execute Stage 7**
```
Objective: Verify 100% Stage 7 execution rate

For each command (/plan, /research, /implement, /revise):
  1. Create test task: /task "Test {command} Stage 7 execution"
  2. Run command: /{command} {task_number}
  3. Verify:
     - [ ] Artifacts created
     - [ ] TODO.md updated with correct status marker
     - [ ] state.json updated with correct status
     - [ ] Artifact links added to TODO.md
     - [ ] Git commit created
  4. Check logs for Stage 7 execution messages:
     - "EXECUTE: Verify..."
     - "INVOKE status-sync-manager..."
     - "LOG: status-sync-manager completed..."
     - "CHECKPOINT: Atomic update completed"
  5. Verify no errors in errors.json

Expected: All verifications pass for all 4 commands
```

**Test 2: Checkpoint Validation Works**
```
Objective: Verify checkpoints prevent Stage 8 if Stage 7 incomplete

For /plan command:
  1. Modify plan.md to skip status-sync-manager invocation
  2. Run: /plan {task_number}
  3. Verify:
     - [ ] Checkpoint failure detected
     - [ ] Stage 8 not executed
     - [ ] Error returned: "CHECKPOINT: Atomic update completed - FAILED"
     - [ ] Error includes missing steps
  4. Restore plan.md
  5. Retry: /plan {task_number}
  6. Verify retry succeeds

Expected: Checkpoint catches Stage 7 skip, retry succeeds
```

**Test 3: Error Handling Provides Recovery**
```
Objective: Verify error handling includes recovery instructions

For /plan command:
  1. Make TODO.md read-only (chmod 444)
  2. Run: /plan {task_number}
  3. Verify:
     - [ ] Error caught: "status-sync-manager failed"
     - [ ] Error logged to errors.json
     - [ ] Error message includes recovery steps
     - [ ] Error message includes retry command
  4. Restore TODO.md permissions (chmod 644)
  5. Retry: /plan {task_number}
  6. Verify retry succeeds

Expected: Error handled gracefully, recovery instructions provided, retry succeeds
```

**Test 4: Orchestrator Validation Catches Stage 7 Skip**
```
Objective: Verify orchestrator rejects returns without Stage 7 completion

For /plan command:
  1. Ensure orchestrator stage validation enabled (Phase 5)
  2. Modify plan.md to skip Stage 7 but return from Stage 8
  3. Run: /plan {task_number}
  4. Verify:
     - [ ] Orchestrator detects stage_7_completed == false
     - [ ] Orchestrator rejects return
     - [ ] Error returned: "Command completed without executing Stage 7"
     - [ ] Error includes manual recovery steps
  5. Restore plan.md
  6. Retry: /plan {task_number}
  7. Verify retry succeeds

Expected: Orchestrator validation catches Stage 7 skip, retry succeeds
```

**Test 5: Git Commit Failure Non-Critical**
```
Objective: Verify git failure doesn't fail command

For /plan command:
  1. Simulate git failure (invalid git config)
  2. Run: /plan {task_number}
  3. Verify:
     - [ ] Plan artifact created
     - [ ] TODO.md updated to [PLANNED]
     - [ ] state.json updated to "planned"
     - [ ] Warning returned: "Git commit failed"
     - [ ] Manual commit instructions provided
  4. Restore git config
  5. Manually commit as instructed

Expected: Command succeeds despite git failure, warning provided
```

### Integration Testing

After all phases complete:

1. **Real Task Testing**:
   - Create real task: `/task "Implement feature X"`
   - Run full workflow: `/research {n}` → `/plan {n}` → `/implement {n}`
   - Verify all status transitions occur automatically
   - Verify no manual intervention needed
   - Verify git commits created for each stage

2. **Load Testing**:
   - Run all 4 commands concurrently on different tasks
   - Verify no race conditions
   - Verify all status updates atomic
   - Verify all git commits created

3. **Failure Recovery Testing**:
   - Simulate various failure modes
   - Verify error handling works
   - Verify recovery instructions accurate
   - Verify retry succeeds

---

## Rollback Plan

If critical issues occur during implementation:

**Phase 1 Rollback**:
- Revert plan.md to pre-Phase-1 version
- Remove imperative language changes
- Restore descriptive language
- Note: Other 3 commands unaffected

**Phase 2 Rollback**:
- Remove checkpoint sections from all 4 commands
- Remove Stage 8 prerequisites
- Note: Phase 1 changes remain (can keep imperative language)

**Phase 3 Rollback**:
- Revert explicit delegation syntax to narrative
- Remove step-by-step structure
- Note: Checkpoints remain (Phase 2)

**Phase 4 Rollback**:
- Remove error handling blocks
- Revert to original error handling
- Note: Explicit delegation remains (Phase 3)

**Phase 5 Rollback**:
- Remove orchestrator stage validation
- Remove command_stages from registry
- Revert orchestrator.md to pre-Phase-5 version
- Note: Command improvements remain (Phases 1-4)

---

## Dependencies

### Internal Dependencies
- command-lifecycle.md (context reference)
- status-markers.md (status definitions)
- subagent-return-format.md (validation rules)
- subagent-delegation-guide.md (delegation patterns)
- git-commits.md (git workflow)

### External Dependencies
- status-sync-manager subagent (must exist and work)
- git-workflow-manager subagent (must exist and work)

### Blocking Issues
- None identified

---

## Risk Assessment

### High Risk
- **Risk**: Changes break existing workflow execution
- **Mitigation**: Test each phase before proceeding, maintain rollback capability

### Medium Risk
- **Risk**: Checkpoints too strict, cause false positives
- **Mitigation**: Careful checkpoint design, comprehensive testing

### Low Risk
- **Risk**: Orchestrator validation adds overhead
- **Mitigation**: Validation only for commands, minimal overhead

---

## Success Metrics

1. **Execution Rate**: 100% Stage 7 execution across all 4 commands
2. **Automation Rate**: 0% manual intervention for status updates
3. **Error Rate**: 0% "status-sync-manager didn't update TODO.md" errors
4. **Test Coverage**: All 5 test cases pass for all 4 commands
5. **User Experience**: No manual TODO.md/state.json updates needed

---

## Related Documentation

- Research Report: [research-001.md](../reports/research-001.md)
- Command Lifecycle: `.opencode/context/core/workflows/command-lifecycle.md`
- Status Markers: `.opencode/context/core/standards/status-markers.md`
- Subagent Return Format: `.opencode/context/core/standards/subagent-return-format.md`
- Delegation Guide: `.opencode/context/core/workflows/subagent-delegation-guide.md`
- Git Commits: `.opencode/context/core/system/git-commits.md`

---

## Notes

- This plan addresses the CORRECT root cause (Stage 7 execution failures within commands)
- Previous tasks 227, 228, 229 had incorrect root cause (orchestrator bypass)
- Evidence shows commands ARE loaded and executed
- Issue is Claude skipping or incompletely executing Stage 7
- Solution is strengthening prompting, adding validation, and explicit delegation
- Orchestrator validation is additional safety layer, not primary fix
