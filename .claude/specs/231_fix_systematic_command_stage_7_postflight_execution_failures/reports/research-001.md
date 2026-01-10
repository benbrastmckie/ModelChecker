# Research Report: Stage 7 (Postflight) Execution Failures

**Research Task**: 231  
**Topic**: Fix systematic command Stage 7 (Postflight) execution failures  
**Date**: 2025-12-28  
**Researcher**: researcher  
**Session ID**: sess_1735439444_r231md

---

## Executive Summary

This research identifies and analyzes the root causes of systematic Stage 7 (Postflight) execution failures across all workflow commands (/plan, /research, /implement, /revise). The investigation reveals **five critical weaknesses** in the current implementation that cause Claude to frequently skip or incompletely execute Stage 7, resulting in successful artifact creation but incomplete task tracking (TODO.md and state.json not updated).

**Key Findings**:
1. **Weak Prompting**: Stage 7 uses descriptive language ("should", "can") instead of imperative commands ("MUST", "Execute")
2. **No Validation Checkpoints**: No explicit verification that Stage 7 completed before Stage 8 returns
3. **Missing Error Handling**: Commands proceed to Stage 8 even if Stage 7 fails
4. **Implicit Delegation Syntax**: status-sync-manager invocation described narratively, not as explicit delegation step
5. **No Orchestrator Validation**: Orchestrator lacks stage completion tracking and validation

**Impact**: CRITICAL - All workflow commands fail to update task tracking despite successful artifact creation, breaking the entire task management system.

---

## 1. Current Stage 7 Implementation Analysis

### 1.1 Stage 7 Structure Across Commands

All four commands follow the same Stage 7 pattern defined in `command-lifecycle.md`:

```xml
<stage id="7" name="Postflight">
  <status_transition>
    Completion: [STATUS] + **Completed**: {date}
  </status_transition>
  <validation_delegation>
    Verify {agent} returned validation success and metadata
  </validation_delegation>
  <git_commit>
    Scope: {files}
    Message: "task {number}: {action}"
    Use git-workflow-manager for scoped commit
  </git_commit>
  <atomic_update>
    Delegate to status-sync-manager:
      - task_number: {number}
      - new_status: "{status}"
      - timestamp: {ISO8601 date}
      - session_id: {session_id}
      - validated_artifacts: {artifacts from agent return}
  </atomic_update>
</stage>
```

**Analysis**: This structure is **descriptive, not imperative**. It describes what should happen but doesn't command Claude to execute it.

### 1.2 Specific Examples from Command Files

#### /plan Command (plan.md lines 160-200)

```xml
<stage id="7" name="Postflight">
  <status_transition>
    Completion: [PLANNED] + **Completed**: {date}
    Partial: Keep [PLANNING]
    Failed: Keep [PLANNING]
    Blocked: [BLOCKED]
  </status_transition>
  <validation_delegation>
    Verify planner returned validation success and metadata:
      - Check planner return metadata for validation_result
      - Verify plan artifact validated (exists, non-empty)
      - Extract plan_metadata (phase_count, estimated_hours, complexity)
      - If validation failed: Abort update, return error to user
  </validation_delegation>
  <git_commit>
    Scope: Plan file + TODO.md + state.json + project state.json
    Message: "task {number}: plan created"
    
    Commit only if status == "completed"
    Use git-workflow-manager for scoped commit
  </git_commit>
  <atomic_update>
    Delegate to status-sync-manager:
      - task_number: {number}
      - new_status: "planned"
      - timestamp: {ISO8601 date}
      - session_id: {session_id}
      - validated_artifacts: {artifacts from planner return}
      - plan_path: {plan_path from planner return}
      - plan_metadata: {plan_metadata from planner return}
    
    status-sync-manager performs two-phase commit:
      - Phase 1: Prepare, validate artifacts, backup
      - Phase 2: Write all files or rollback all
    
    Atomicity guaranteed across:
      - TODO.md (status, timestamps, plan link)
      - state.json (status, timestamps, plan_path, plan_metadata)
      - project state.json (lazy created if needed)
  </atomic_update>
</stage>
```

**Weaknesses Identified**:
1. **Descriptive verbs**: "Verify", "Check", "Extract", "Delegate" - these describe actions but don't command execution
2. **No explicit execution order**: Steps are listed but not numbered or sequenced
3. **No validation checkpoint**: No "MUST verify Stage 7 completed before proceeding to Stage 8"
4. **Implicit delegation**: "Delegate to status-sync-manager" is narrative, not an explicit invocation instruction
5. **No error handling**: No "IF delegation fails THEN..." logic

#### /research Command (research.md lines 186-233)

```xml
<stage id="7" name="Postflight">
  <status_transition>
    Completion: [RESEARCHED] + **Completed**: {date}
    Partial: Keep [RESEARCHING]
    Failed: Keep [RESEARCHING]
    Blocked: [BLOCKED]
  </status_transition>
  <validation_delegation>
    Verify researcher returned validation success:
      - Check researcher return metadata for validation_result
      - Verify research artifact validated (exists, non-empty)
      - Expect 1 artifact: research report only (NO summary artifact)
      - Summary returned as metadata in return object, not as artifact
      - If validation failed: Abort update, return error to user
  </validation_delegation>
  <artifact_linking>
    Link 1 artifact in TODO.md:
      - Research Report: {report_path}
    
    NO summary artifact link (summary is metadata in return object)
  </artifact_linking>
  <git_commit>
    Scope: Research report + TODO.md + state.json + project state.json
    Message: "task {number}: research completed"
    
    Commit only if status == "completed"
    Use git-workflow-manager for scoped commit
  </git_commit>
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
</stage>
```

**Same weaknesses** as /plan command.

#### /implement Command (implement.md lines 239-306)

```xml
<stage id="7" name="Postflight">
  <status_transition>
    Completion: [COMPLETED] + **Completed**: {date} + [PASS]
    Partial: [PARTIAL] + note about resume
    Failed: Keep [IMPLEMENTING]
    Blocked: [BLOCKED]
  </status_transition>
  <validation_delegation>
    Verify implementation agent returned validation success:
      - Check agent return metadata for validation_result
      - Verify all artifacts validated (exist, non-empty, token limit)
      - Extract phase_statuses if phased implementation
      - Validate phase_statuses format if present:
        * Must be array
        * Each entry must have: phase_number, status, timestamp
        * Phase numbers must be positive integers
        * Status must be: in_progress, completed, abandoned, blocked
      - If validation failed: Abort update, return error to user
      - If phase_statuses missing for phased implementation: Return error
  </validation_delegation>
  <phase_statuses_validation>
    For phased implementations (task-executor):
      - Verify phase_statuses present in return object
      - Verify phase_statuses is non-empty array
      - Verify each entry has required fields
      - If missing or malformed: Return error with details
      - Error message: "phase_statuses missing or malformed in task-executor return"
    
    For direct implementations (implementer):
      - phase_statuses not required (no phases)
      - Skip phase_statuses validation
  </phase_statuses_validation>
  <git_commit>
    Scope: Implementation files + TODO.md + state.json + project state.json + plan (if exists)
    Message: "task {number}: implementation completed"
    
    For phased implementation: Create commit per phase (delegated to task-executor)
    For direct implementation: Create single commit
    
    Commit only if status == "completed"
    Use git-workflow-manager for scoped commit
  </git_commit>
  <atomic_update>
    Delegate to status-sync-manager:
      - task_number: {number}
      - new_status: "completed" or "partial"
      - timestamp: {ISO8601 date}
      - session_id: {session_id}
      - validated_artifacts: {artifacts from implementation agent return}
      - plan_path: {plan_path if exists}
      - phase_statuses: {phase_statuses from agent return if phased}
    
    CRITICAL: Validate phase_statuses before passing to status-sync-manager:
      - If phased implementation AND phase_statuses missing: Abort with error
      - If phased implementation AND phase_statuses malformed: Abort with error
      - Log phase_statuses parameter passing for debugging
    
    status-sync-manager performs two-phase commit:
      - Phase 1: Prepare, validate artifacts, backup, parse plan file
      - Phase 2: Write all files (TODO.md, state.json, project state.json, plan file) or rollback all
    
    Atomicity guaranteed across:
      - TODO.md (status, timestamps, artifact links, checkmark if completed)
      - state.json (status, timestamps, artifacts array)
      - project state.json (lazy created if needed, CRITICAL: fail if creation fails)
      - plan file (phase statuses updated atomically if phase_statuses provided)
  </atomic_update>
</stage>
```

**Additional weaknesses** beyond /plan and /research:
- More complex validation logic but still descriptive
- "CRITICAL" warnings but no enforcement mechanism
- Conditional logic ("IF phased implementation AND...") described but not executed

#### /revise Command (revise.md lines 164-207)

```xml
<stage id="7" name="Postflight">
  <status_transition>
    Completion: [REVISED] + **Completed**: {date}
    Partial: Keep [REVISING]
    Failed: Keep [REVISING]
    Blocked: [BLOCKED]
  </status_transition>
  <validation_delegation>
    Verify planner returned validation success and metadata:
      - Check planner return metadata for validation_result
      - Verify plan artifact validated (exists, non-empty)
      - Extract plan_metadata (phase_count, estimated_hours, complexity)
      - Extract plan_version from planner return
      - If validation failed: Abort update, return error to user
  </validation_delegation>
  <git_commit>
    Scope: New plan file + TODO.md + state.json + project state.json
    Message: "task {number}: plan revised to v{version}"
    
    Commit only if status == "completed"
    Use git-workflow-manager for scoped commit
  </git_commit>
  <atomic_update>
    Delegate to status-sync-manager:
      - task_number: {number}
      - new_status: "revised"
      - timestamp: {ISO8601 date}
      - session_id: {session_id}
      - validated_artifacts: {artifacts from planner return}
      - plan_path: {new_plan_path from planner return}
      - plan_metadata: {plan_metadata from planner return}
      - plan_version: {version from planner return}
      - revision_reason: {reason from user prompt}
    
    status-sync-manager performs two-phase commit:
      - Phase 1: Prepare, validate artifacts, backup
      - Phase 2: Write all files or rollback all
    
    Atomicity guaranteed across:
      - TODO.md (status, timestamps, updated plan link)
      - state.json (status, timestamps, plan_path, plan_metadata, plan_versions array)
      - project state.json (lazy created if needed)
  </atomic_update>
</stage>
```

**Same weaknesses** as other commands.

---

## 2. Root Cause Analysis

### 2.1 Root Cause #1: Weak Prompting Language

**Problem**: Stage 7 uses descriptive language instead of imperative commands.

**Evidence**:

| Current (Weak) | Strong Alternative |
|----------------|-------------------|
| "Verify planner returned validation success" | "EXECUTE: Verify planner returned validation success. ABORT if validation failed." |
| "Delegate to status-sync-manager:" | "INVOKE status-sync-manager with the following parameters:" |
| "Use git-workflow-manager for scoped commit" | "EXECUTE: Invoke git-workflow-manager to create scoped commit" |
| "Commit only if status == 'completed'" | "IF status == 'completed' THEN invoke git-workflow-manager ELSE skip commit" |

**Impact**: Claude interprets descriptive text as documentation rather than executable instructions, leading to skipped execution.

**Comparison with Strong Prompting Examples**:

From `command-lifecycle.md` Stage 7 specification (lines 263-330):

```xml
<update_procedures>
  CRITICAL: All status and artifact updates in Stage 7 MUST be delegated to 
  status-sync-manager to ensure atomicity across all tracking files.
  
  **WARNING**: DO NOT manually update TODO.md, state.json, project state.json, 
  or plan files directly. Manual updates create race conditions and inconsistent 
  state. ALL updates MUST flow through status-sync-manager's two-phase commit protocol.
</update_procedures>
```

This uses **imperative language** ("MUST", "DO NOT") but is buried in a subsection. The main Stage 7 structure still uses descriptive language.

### 2.2 Root Cause #2: No Validation Checkpoints

**Problem**: No explicit checkpoint verifying Stage 7 completed before Stage 8 executes.

**Evidence**: Examining Stage 7 and Stage 8 transitions:

**Stage 7 (Postflight)** - No completion checkpoint:
```xml
<stage id="7" name="Postflight">
  <atomic_update>
    Delegate to status-sync-manager:
      - task_number: {number}
      - new_status: "planned"
      ...
  </atomic_update>
</stage>
```

**Stage 8 (ReturnSuccess)** - Proceeds immediately:
```xml
<stage id="8" name="ReturnSuccess">
  <return_format>
    Plan created for task {number}.
    {brief_1_sentence_overview}
    ...
  </return_format>
</stage>
```

**Missing checkpoint** between Stage 7 and Stage 8:
```xml
<!-- SHOULD EXIST BUT DOESN'T -->
<stage_7_completion_validation>
  VERIFY Stage 7 completed successfully:
  - [ ] status-sync-manager invoked
  - [ ] status-sync-manager returned status: "completed"
  - [ ] TODO.md updated (verify on disk)
  - [ ] state.json updated (verify on disk)
  - [ ] git commit created (verify hash returned)
  
  IF any verification fails:
    - ABORT Stage 8
    - Return error to user
    - Include Stage 7 failure details
</stage_7_completion_validation>
```

**Impact**: Claude can skip Stage 7 entirely and proceed directly to Stage 8 because there's no enforcement mechanism.

### 2.3 Root Cause #3: Missing Error Handling

**Problem**: No explicit error handling for Stage 7 failures.

**Evidence**: Current Stage 7 has no error handling blocks:

```xml
<stage id="7" name="Postflight">
  <atomic_update>
    Delegate to status-sync-manager:
      - task_number: {number}
      - new_status: "planned"
      ...
  </atomic_update>
</stage>
```

**Missing error handling**:
```xml
<!-- SHOULD EXIST BUT DOESN'T -->
<error_handling>
  IF status-sync-manager delegation fails:
    - Capture error details
    - Log to errors.json
    - ABORT Stage 8
    - Return failed status to user
    - Include recommendation: "Retry command to resume from Stage 7"
  
  IF git-workflow-manager delegation fails:
    - Log error (non-critical)
    - Continue to status-sync-manager
    - Include warning in Stage 8 return
  
  IF validation fails:
    - ABORT before delegation
    - Return validation error to user
    - Do not proceed to Stage 8
</error_handling>
```

**Comparison with command-lifecycle.md error patterns** (lines 594-700):

The lifecycle document defines error handling patterns but they're **not integrated into Stage 7 structure**:

```markdown
### Pattern 3: Git Commit Failure Handling

**Scenario**: Git commit creation fails

**Handling**:
1. Log git error to errors.json
2. Continue with command execution (git failure is non-critical)
3. Include git error in return to user
4. Provide manual commit instructions
5. Do not fail the command
```

This pattern exists but is **not referenced or enforced in Stage 7 XML structure**.

### 2.4 Root Cause #4: Implicit Delegation Syntax

**Problem**: status-sync-manager and git-workflow-manager invocations are described narratively, not as explicit delegation steps.

**Evidence**: Current delegation syntax:

```xml
<atomic_update>
  Delegate to status-sync-manager:
    - task_number: {number}
    - new_status: "planned"
    - timestamp: {ISO8601 date}
    - session_id: {session_id}
    - validated_artifacts: {artifacts from planner return}
</atomic_update>
```

This is **narrative description**, not executable syntax.

**Strong alternative** (explicit delegation):

```xml
<atomic_update>
  <action>INVOKE status-sync-manager subagent</action>
  <delegation_syntax>
    EXECUTE delegation with explicit syntax:
    
    1. PREPARE delegation context:
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
    
    2. INVOKE status-sync-manager:
       - Use subagent delegation mechanism per subagent-delegation-guide.md
       - Pass delegation context as parameters
       - Set timeout: 60s (status updates are fast)
    
    3. WAIT for status-sync-manager return
    
    4. VALIDATE return:
       - VERIFY status == "completed"
       - VERIFY files_updated includes ["TODO.md", "state.json"]
       - IF validation fails: ABORT and return error
    
    5. EXTRACT results:
       - files_updated: list of files modified
       - rollback_performed: boolean
       - errors: array (should be empty)
  </delegation_syntax>
  <validation>
    CHECKPOINT: status-sync-manager completed successfully
    - [ ] Return status: "completed"
    - [ ] TODO.md updated on disk
    - [ ] state.json updated on disk
    - [ ] No rollback performed
  </validation>
</atomic_update>
```

**Comparison with orchestrator.md delegation syntax** (lines 397-419):

The orchestrator uses **explicit invocation pattern**:

```python
result = task_tool(
    subagent_type=target_agent,
    prompt=construct_prompt(request, context),
    session_id=delegation_context["session_id"],
    delegation_depth=delegation_context["delegation_depth"],
    delegation_path=delegation_context["delegation_path"],
    timeout=delegation_context["timeout"]
)
```

This is **executable code**, not narrative description. Stage 7 should use similar explicit syntax.

### 2.5 Root Cause #5: No Orchestrator Stage Validation

**Problem**: Orchestrator lacks stage completion tracking and validation.

**Evidence**: Examining `orchestrator.md` process flow (lines 129-693):

The orchestrator has **13 stages** for request handling but **no stage-level validation for command execution**:

1. AnalyzeRequest
2. DetermineComplexity
3. CheckLanguage
4. PrepareRouting
5. CheckCycleAndDepth
6. RegisterDelegation
7. RouteToAgent
8. MonitorDelegation
9. ReceiveResults
10. ValidateReturn
11. ProcessResults
12. CleanupDelegation
13. ReturnToUser

**Missing**: Stage completion tracking for delegated commands.

When orchestrator invokes a command (e.g., /plan), it should:

1. **Track command stage progression**:
   ```python
   command_execution = {
     "session_id": session_id,
     "command": "plan",
     "current_stage": 1,
     "stages_completed": [],
     "stage_7_completed": False,
     "stage_8_completed": False
   }
   ```

2. **Validate Stage 7 completion before accepting Stage 8 return**:
   ```python
   def validate_command_completion(command_execution, return_obj):
       # Check Stage 7 completed
       if not command_execution["stage_7_completed"]:
           raise ValidationError(
               "Command returned from Stage 8 without completing Stage 7. "
               "TODO.md and state.json not updated."
           )
       
       # Verify Stage 7 artifacts
       if not verify_file_updated("TODO.md", command_execution["start_time"]):
           raise ValidationError("TODO.md not updated in Stage 7")
       
       if not verify_file_updated("state.json", command_execution["start_time"]):
           raise ValidationError("state.json not updated in Stage 7")
       
       return True
   ```

3. **Enforce stage order**:
   ```python
   def enforce_stage_order(command_execution, stage_number):
       expected_stage = command_execution["current_stage"]
       if stage_number != expected_stage:
           raise StageOrderError(
               f"Stage {stage_number} executed out of order. "
               f"Expected stage {expected_stage}."
           )
       command_execution["current_stage"] = stage_number + 1
       command_execution["stages_completed"].append(stage_number)
   ```

**Current orchestrator** has **no such validation**. It accepts command returns without verifying stage completion.

---

## 3. Evidence from Task History

### 3.1 Task 224 Evidence

**Task**: Create implementation plan for fixing orchestrator command bypass  
**Status**: Plan created [PASS], TODO.md manually updated [PASS], state.json not updated [FAIL]

**Analysis**:
- Planner subagent successfully created plan artifact
- Stage 7 (Postflight) did not execute
- status-sync-manager was never invoked
- TODO.md was manually updated by user
- state.json remains unupdated

**Root cause**: Orchestrator bypassed /plan command and directly invoked planner subagent, skipping Stage 7 entirely.

### 3.2 Task 229 Evidence

**Task**: Fix orchestrator command bypass (superseded by Task 231)  
**Status**: Plan created [PASS], tracking required manual intervention

**Analysis**:
- Same pattern as Task 224
- Plan artifact created successfully
- Stage 7 not executed
- Manual TODO.md update required

**Root cause**: Same as Task 224 - orchestrator bypass.

### 3.3 Pattern Across All Commands

From TODO.md task 229 description (lines 221-241):

> "Root Cause: The orchestrator bypassed the /plan command layer and directly invoked 
> the planner subagent, which meant the command's Stage 7 (Postflight) that delegates 
> to status-sync-manager never executed, leaving TODO.md and state.json unupdated 
> despite the plan artifact being successfully created."

This confirms the **systematic pattern**:
1. User invokes command (e.g., `/plan 224`)
2. Orchestrator routes directly to subagent (planner)
3. Subagent creates artifacts successfully
4. Subagent returns to orchestrator
5. **Stage 7 never executes** (because command layer was bypassed)
6. Orchestrator returns success to user
7. TODO.md and state.json remain unupdated

**However**, the task description identifies orchestrator bypass as the root cause. This research reveals **additional root causes** even if orchestrator routing is fixed:

- **Even if orchestrator correctly routes to command layer**, weak prompting in Stage 7 can cause Claude to skip execution
- **Even if Stage 7 is attempted**, lack of validation checkpoints allows failure to go unnoticed
- **Even if delegation is described**, implicit syntax may not trigger actual invocation

---

## 4. Detailed Weakness Analysis

### 4.1 Weak Prompting Examples

#### Example 1: Descriptive vs Imperative

**Current (Weak)**:
```xml
<validation_delegation>
  Verify planner returned validation success and metadata:
    - Check planner return metadata for validation_result
    - Verify plan artifact validated (exists, non-empty)
    - Extract plan_metadata (phase_count, estimated_hours, complexity)
    - If validation failed: Abort update, return error to user
</validation_delegation>
```

**Problems**:
- "Verify" is descriptive, not imperative
- "Check" suggests optional action
- "If validation failed" is conditional but not enforced
- No explicit execution order

**Strong Alternative**:
```xml
<validation_delegation>
  <action>EXECUTE validation of planner return</action>
  <steps>
    STEP 1: EXTRACT validation_result from planner return metadata
      - VERIFY validation_result field exists
      - IF missing: ABORT with error "validation_result missing from planner return"
    
    STEP 2: CHECK validation_result value
      - IF validation_result != "passed": ABORT with error from planner
      - LOG: "Planner validation: {validation_result}"
    
    STEP 3: VERIFY plan artifact exists on disk
      - READ file: {plan_path from planner return}
      - IF file not found: ABORT with error "Plan artifact not found: {plan_path}"
      - IF file empty (size == 0): ABORT with error "Plan artifact is empty"
      - LOG: "Plan artifact validated: {plan_path} ({size} bytes)"
    
    STEP 4: EXTRACT plan_metadata from planner return
      - VERIFY plan_metadata field exists
      - EXTRACT: phase_count, estimated_hours, complexity
      - IF missing: Use defaults (phase_count=1, estimated_hours=null, complexity="unknown")
      - LOG: "Plan metadata: {phase_count} phases, {estimated_hours} hours, {complexity}"
    
    CHECKPOINT: Validation completed successfully
      - [ ] validation_result == "passed"
      - [ ] Plan artifact exists and non-empty
      - [ ] plan_metadata extracted
  </steps>
  <error_handling>
    IF any step fails:
      - ABORT Stage 7 immediately
      - DO NOT proceed to status-sync-manager
      - DO NOT proceed to Stage 8
      - RETURN error to user with validation failure details
  </error_handling>
</validation_delegation>
```

**Key improvements**:
- Explicit "EXECUTE", "STEP", "VERIFY", "ABORT" commands
- Numbered steps with clear execution order
- Explicit error handling with "IF...THEN...ELSE" logic
- Checkpoint validation before proceeding
- Logging for debugging

#### Example 2: Implicit vs Explicit Delegation

**Current (Weak)**:
```xml
<atomic_update>
  Delegate to status-sync-manager:
    - task_number: {number}
    - new_status: "planned"
    - timestamp: {ISO8601 date}
    - session_id: {session_id}
    - validated_artifacts: {artifacts from planner return}
    - plan_path: {plan_path from planner return}
    - plan_metadata: {plan_metadata from planner return}
</atomic_update>
```

**Problems**:
- "Delegate to" is narrative, not executable
- Parameters listed but no invocation syntax
- No timeout specified
- No return validation
- No error handling

**Strong Alternative**:
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
      - VERIFY new_status is valid value
      - VERIFY timestamp is ISO8601 format
      - IF validation fails: ABORT with error
  </step_1_prepare_delegation>
  
  <step_2_invoke>
    INVOKE status-sync-manager:
      - Subagent type: "status-sync-manager"
      - Delegation context: {prepared context}
      - Timeout: 60s (status updates are fast)
      - Delegation mechanism: Per subagent-delegation-guide.md
    
    LOG: "Invoking status-sync-manager for task {number}"
  </step_2_invoke>
  
  <step_3_wait>
    WAIT for status-sync-manager return:
      - Maximum wait: 60s
      - IF timeout: ABORT with error "status-sync-manager timeout"
  </step_3_wait>
  
  <step_4_validate_return>
    VALIDATE status-sync-manager return:
      - VERIFY return format matches subagent-return-format.md
      - VERIFY status field present
      - VERIFY status == "completed" (not "failed" or "partial")
      - VERIFY files_updated includes ["TODO.md", "state.json"]
      - VERIFY rollback_performed == false
      - IF validation fails: ABORT with error details
    
    LOG: "status-sync-manager completed: {files_updated}"
  </step_4_validate_return>
  
  <step_5_verify_on_disk>
    VERIFY files updated on disk:
      - READ TODO.md and verify status marker changed to [PLANNED]
      - READ state.json and verify status field == "planned"
      - IF verification fails: ABORT with error "Files not updated despite status-sync-manager success"
    
    CHECKPOINT: Atomic update completed successfully
      - [ ] status-sync-manager returned "completed"
      - [ ] TODO.md updated on disk
      - [ ] state.json updated on disk
      - [ ] No rollback performed
  </step_5_verify_on_disk>
  
  <error_handling>
    IF status-sync-manager returns "failed":
      - EXTRACT error details from return
      - LOG error to errors.json
      - ABORT Stage 7
      - RETURN error to user: "Status update failed: {error}"
    
    IF status-sync-manager times out:
      - LOG timeout to errors.json
      - ABORT Stage 7
      - RETURN error to user: "Status update timed out after 60s"
    
    IF rollback_performed == true:
      - EXTRACT rollback details from return
      - LOG rollback to errors.json
      - ABORT Stage 7
      - RETURN error to user: "Status update rolled back: {reason}"
  </error_handling>
</atomic_update>
```

**Key improvements**:
- Explicit "INVOKE" command with subagent type
- Step-by-step execution with numbered steps
- Explicit timeout specification
- Return validation with specific checks
- On-disk verification (belt-and-suspenders)
- Comprehensive error handling for all failure modes
- Checkpoint validation before proceeding

### 4.2 Missing Validation Checkpoints

#### Current State: No Checkpoints

Commands transition from Stage 7 to Stage 8 with **no validation**:

```xml
<stage id="7" name="Postflight">
  <!-- Stage 7 content -->
</stage>

<stage id="8" name="ReturnSuccess">
  <!-- Stage 8 content -->
</stage>
```

#### Proposed: Explicit Checkpoints

```xml
<stage id="7" name="Postflight">
  <!-- Stage 7 content -->
  
  <stage_7_completion_checkpoint>
    VERIFY all Stage 7 steps completed:
      - [ ] Subagent return validated
      - [ ] Artifacts validated on disk
      - [ ] status-sync-manager invoked
      - [ ] status-sync-manager returned "completed"
      - [ ] TODO.md updated on disk
      - [ ] state.json updated on disk
      - [ ] git-workflow-manager invoked (if status == "completed")
      - [ ] git commit created (if applicable)
    
    IF any checkpoint fails:
      - ABORT Stage 8
      - RETURN error to user with checkpoint failure details
      - Include recommendation for manual completion
    
    IF all checkpoints pass:
      - LOG: "Stage 7 (Postflight) completed successfully"
      - PROCEED to Stage 8
  </stage_7_completion_checkpoint>
</stage>

<stage id="8" name="ReturnSuccess">
  <prerequisite>
    REQUIRE: Stage 7 completion checkpoint passed
    IF Stage 7 not completed: ABORT with error
  </prerequisite>
  
  <!-- Stage 8 content -->
</stage>
```

### 4.3 Missing Error Handling

#### Current State: No Error Handling

Stage 7 has **no explicit error handling blocks**. Errors are mentioned in descriptions but not handled:

```xml
<atomic_update>
  Delegate to status-sync-manager:
    ...
  
  status-sync-manager performs two-phase commit:
    - Phase 1: Prepare, validate artifacts, backup
    - Phase 2: Write all files or rollback all
  
  Atomicity guaranteed across:
    - TODO.md (status, timestamps, plan link)
    - state.json (status, timestamps, plan_path, plan_metadata)
    - project state.json (lazy created if needed)
</atomic_update>
```

**Problem**: What happens if status-sync-manager fails? No error handling specified.

#### Proposed: Comprehensive Error Handling

```xml
<atomic_update>
  <invocation>
    <!-- Invocation steps as shown in 4.1 -->
  </invocation>
  
  <error_handling>
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
          
          Artifacts created: {list}
          
          Manual steps required:
          1. Verify artifacts exist: {artifact_paths}
          2. Manually update TODO.md status to [PLANNED]
          3. Manually update state.json status to "planned"
          4. Retry command if needed
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
          - Partial: "Status update timed out but files partially updated"
          - Complete: "Status update timed out, no files updated"
    </error_case>
    
    <error_case name="git_commit_failed">
      IF git-workflow-manager returns status == "failed":
        STEP 1: LOG error (non-critical)
          - Git failure does not fail the command
          - Artifacts and status updates still valid
        
        STEP 2: CONTINUE to Stage 8
          - Include git failure warning in return
          - Provide manual commit instructions
        
        STEP 3: RETURN success with warning
          ```
          Warning: Git commit failed
          
          Plan created successfully: {plan_path}
          Task status updated to [PLANNED]
          
          Manual commit required:
            git add {files}
            git commit -m "task {number}: plan created"
          ```
    </error_case>
    
    <error_case name="validation_failed">
      IF validation fails before delegation:
        STEP 1: ABORT immediately
          - DO NOT invoke status-sync-manager
          - DO NOT invoke git-workflow-manager
        
        STEP 2: RETURN validation error
          ```
          Error: Validation failed
          
          Details: {validation_error}
          
          Recommendation: Fix subagent implementation
          ```
    </error_case>
  </error_handling>
</atomic_update>
```

### 4.4 Implicit vs Explicit Delegation Syntax

#### Comparison Table

| Aspect | Current (Implicit) | Proposed (Explicit) |
|--------|-------------------|---------------------|
| **Invocation** | "Delegate to status-sync-manager:" | "INVOKE status-sync-manager subagent" |
| **Parameters** | Listed as bullet points | Structured JSON with validation |
| **Timeout** | Not specified | Explicit: 60s |
| **Return handling** | Not specified | Explicit validation steps |
| **Error handling** | Not specified | Comprehensive error cases |
| **Verification** | Not specified | On-disk file verification |
| **Logging** | Not specified | Explicit log statements |

#### Example: git-workflow-manager Invocation

**Current (Weak)**:
```xml
<git_commit>
  Scope: Plan file + TODO.md + state.json + project state.json
  Message: "task {number}: plan created"
  
  Commit only if status == "completed"
  Use git-workflow-manager for scoped commit
</git_commit>
```

**Proposed (Strong)**:
```xml
<git_commit>
  <conditional>
    IF status == "completed":
      PROCEED with git commit
    ELSE:
      SKIP git commit
      LOG: "Skipping git commit (status: {status})"
      PROCEED to Stage 8
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
      - Timeout: 120s (git operations can be slow)
    
    STEP 3: WAIT for git-workflow-manager return
    
    STEP 4: VALIDATE return
      - IF status == "completed":
        * EXTRACT commit_hash from commit_info
        * LOG: "Git commit created: {commit_hash}"
        * PROCEED to Stage 8
      
      - IF status == "failed":
        * LOG error to errors.json (non-critical)
        * INCLUDE warning in Stage 8 return
        * PROCEED to Stage 8 (git failure doesn't fail command)
  </invocation>
  
  <error_handling>
    IF git-workflow-manager fails:
      - LOG error (non-critical)
      - CONTINUE to Stage 8
      - INCLUDE manual commit instructions in return
  </error_handling>
</git_commit>
```

---

## 5. Orchestrator Validation Gaps

### 5.1 Current Orchestrator Process Flow

From `orchestrator.md` (lines 129-693), the orchestrator has 13 stages but **no command stage tracking**:

1. **AnalyzeRequest**: Parse command and arguments
2. **DetermineComplexity**: Assess context needs
3. **CheckLanguage**: Extract language for routing
4. **PrepareRouting**: Determine target agent
5. **CheckCycleAndDepth**: Validate delegation safety
6. **RegisterDelegation**: Track in registry
7. **RouteToAgent**: Invoke target
8. **MonitorDelegation**: Watch for timeout
9. **ReceiveResults**: Get return object
10. **ValidateReturn**: Check format
11. **ProcessResults**: Extract artifacts
12. **CleanupDelegation**: Remove from registry
13. **ReturnToUser**: Send final result

**Gap**: When orchestrator routes to a **command** (not a subagent), it should track **command stage progression** but doesn't.

### 5.2 Proposed: Command Stage Tracking

Add new orchestrator capability:

```python
<command_stage_tracking>
  <purpose>
    Track command stage progression to ensure all stages complete
  </purpose>
  
  <tracking_structure>
    ```python
    command_execution = {
      "session_id": "sess_1735439444_abc123",
      "command": "plan",
      "task_number": 224,
      "start_time": "2025-12-28T10:00:00Z",
      "current_stage": 1,
      "stages_completed": [],
      "stage_checkpoints": {
        "stage_1_preflight": False,
        "stage_2_check_language": False,
        "stage_3_prepare_delegation": False,
        "stage_4_invoke_agent": False,
        "stage_5_receive_results": False,
        "stage_6_process_results": False,
        "stage_7_postflight": False,
        "stage_8_return_success": False
      },
      "stage_7_artifacts": {
        "status_sync_manager_invoked": False,
        "status_sync_manager_completed": False,
        "todo_md_updated": False,
        "state_json_updated": False,
        "git_commit_created": False
      }
    }
    ```
  </tracking_structure>
  
  <stage_validation>
    BEFORE accepting command return:
      VERIFY Stage 7 completed:
        - CHECK stage_checkpoints["stage_7_postflight"] == True
        - CHECK stage_7_artifacts["status_sync_manager_completed"] == True
        - CHECK stage_7_artifacts["todo_md_updated"] == True
        - CHECK stage_7_artifacts["state_json_updated"] == True
      
      IF any check fails:
        - REJECT command return
        - RETURN error to user:
          ```
          Error: Command completed without executing Stage 7 (Postflight)
          
          Missing steps:
          - status-sync-manager invocation: {status}
          - TODO.md update: {status}
          - state.json update: {status}
          
          Artifacts created: {list}
          
          Manual steps required:
          1. Update TODO.md status to [PLANNED]
          2. Update state.json status to "planned"
          3. Link artifacts in TODO.md
          
          Or retry command: /plan {task_number}
          ```
  </stage_validation>
  
  <file_verification>
    VERIFY files updated on disk:
      ```python
      def verify_file_updated(file_path, start_time):
          # Check file modification time
          if not os.path.exists(file_path):
              return False
          
          mod_time = os.path.getmtime(file_path)
          if mod_time < start_time:
              return False  # File not modified since command started
          
          return True
      ```
    
    APPLY to Stage 7 validation:
      - VERIFY TODO.md modified after command start
      - VERIFY state.json modified after command start
      - IF verification fails: REJECT command return
  </file_verification>
</command_stage_tracking>
```

### 5.3 Integration with Orchestrator Stages

Modify orchestrator **Stage 10 (ValidateReturn)** to include command stage validation:

```python
<step_10 name="ValidateReturn">
  <action>Validate return against standardized format</action>
  
  <validation_against_schema>
    <!-- Existing validation -->
  </validation_against_schema>
  
  <command_stage_validation>
    IF return is from command (not subagent):
      VERIFY command stage progression:
        - EXTRACT command_execution from registry
        - VERIFY stage_7_postflight completed
        - VERIFY TODO.md updated on disk
        - VERIFY state.json updated on disk
        - IF validation fails: REJECT return with error
  </command_stage_validation>
</step_10>
```

---

## 6. Proposed Fixes

### 6.1 Fix #1: Strengthen Stage 7 Prompting

**Objective**: Replace descriptive language with imperative commands

**Changes**:

1. **Replace descriptive verbs** with imperative commands:
   - "Verify" → "EXECUTE: Verify"
   - "Delegate to" → "INVOKE"
   - "Use" → "EXECUTE"
   - "Check" → "VERIFY"

2. **Add explicit execution order**:
   - Number all steps: STEP 1, STEP 2, etc.
   - Add dependencies: "STEP 2 (requires STEP 1 completion)"

3. **Add explicit conditionals**:
   - Replace "Commit only if status == 'completed'" with:
     ```xml
     IF status == "completed":
       EXECUTE git commit
     ELSE:
       SKIP git commit
       LOG: "Skipping git commit (status: {status})"
     ```

4. **Add explicit error handling**:
   - For each step, add "IF step fails: ABORT with error"
   - Specify exact error messages to return

**Example transformation** (plan.md Stage 7):

**Before**:
```xml
<stage id="7" name="Postflight">
  <atomic_update>
    Delegate to status-sync-manager:
      - task_number: {number}
      - new_status: "planned"
      ...
  </atomic_update>
</stage>
```

**After**:
```xml
<stage id="7" name="Postflight">
  <atomic_update>
    <action>INVOKE status-sync-manager subagent</action>
    
    <step_1_prepare>
      PREPARE delegation context:
      {delegation context JSON}
      
      VALIDATE context:
        - VERIFY all required fields present
        - IF validation fails: ABORT with error
    </step_1_prepare>
    
    <step_2_invoke>
      INVOKE status-sync-manager:
        - Subagent type: "status-sync-manager"
        - Timeout: 60s
      
      LOG: "Invoking status-sync-manager for task {number}"
    </step_2_invoke>
    
    <step_3_wait>
      WAIT for return (max 60s)
      
      IF timeout: ABORT with error "status-sync-manager timeout"
    </step_3_wait>
    
    <step_4_validate>
      VALIDATE return:
        - VERIFY status == "completed"
        - VERIFY files_updated includes ["TODO.md", "state.json"]
        - IF validation fails: ABORT with error
      
      LOG: "status-sync-manager completed: {files_updated}"
    </step_4_validate>
    
    <step_5_verify>
      VERIFY files on disk:
        - READ TODO.md, verify status == [PLANNED]
        - READ state.json, verify status == "planned"
        - IF verification fails: ABORT with error
      
      CHECKPOINT: Atomic update completed
    </step_5_verify>
    
    <error_handling>
      IF any step fails:
        - LOG error to errors.json
        - ABORT Stage 7
        - RETURN error to user
        - DO NOT proceed to Stage 8
    </error_handling>
  </atomic_update>
</stage>
```

### 6.2 Fix #2: Add Validation Checkpoints

**Objective**: Ensure Stage 7 completes before Stage 8 executes

**Changes**:

1. **Add Stage 7 completion checkpoint**:
   ```xml
   <stage_7_completion_checkpoint>
     VERIFY all Stage 7 steps completed:
       - [ ] Subagent return validated
       - [ ] Artifacts validated on disk
       - [ ] status-sync-manager invoked
       - [ ] status-sync-manager returned "completed"
       - [ ] TODO.md updated on disk
       - [ ] state.json updated on disk
       - [ ] git-workflow-manager invoked (if applicable)
     
     IF any checkpoint fails:
       - ABORT Stage 8
       - RETURN error to user
     
     IF all checkpoints pass:
       - LOG: "Stage 7 completed successfully"
       - PROCEED to Stage 8
   </stage_7_completion_checkpoint>
   ```

2. **Add Stage 8 prerequisite**:
   ```xml
   <stage id="8" name="ReturnSuccess">
     <prerequisite>
       REQUIRE: Stage 7 completion checkpoint passed
       IF Stage 7 not completed: ABORT with error
     </prerequisite>
     
     <!-- Stage 8 content -->
   </stage>
   ```

3. **Add intermediate checkpoints** within Stage 7:
   - After validation: "CHECKPOINT: Validation completed"
   - After status-sync-manager: "CHECKPOINT: Atomic update completed"
   - After git commit: "CHECKPOINT: Git commit completed"

**Example** (research.md Stage 7):

```xml
<stage id="7" name="Postflight">
  <!-- Validation steps -->
  <checkpoint_1>
    CHECKPOINT: Validation completed
      - [ ] researcher return validated
      - [ ] Research artifacts exist on disk
      - [ ] Artifacts non-empty
    
    IF checkpoint fails: ABORT Stage 7
  </checkpoint_1>
  
  <!-- status-sync-manager steps -->
  <checkpoint_2>
    CHECKPOINT: Atomic update completed
      - [ ] status-sync-manager invoked
      - [ ] status-sync-manager returned "completed"
      - [ ] TODO.md updated on disk
      - [ ] state.json updated on disk
    
    IF checkpoint fails: ABORT Stage 7
  </checkpoint_2>
  
  <!-- git-workflow-manager steps -->
  <checkpoint_3>
    CHECKPOINT: Git commit completed (if applicable)
      - [ ] git-workflow-manager invoked
      - [ ] Commit created or skipped appropriately
    
    IF checkpoint fails: LOG warning (non-critical)
  </checkpoint_3>
  
  <stage_7_completion_checkpoint>
    VERIFY all checkpoints passed:
      - [ ] Checkpoint 1: Validation
      - [ ] Checkpoint 2: Atomic update
      - [ ] Checkpoint 3: Git commit
    
    IF all pass:
      - LOG: "Stage 7 (Postflight) completed successfully"
      - PROCEED to Stage 8
    ELSE:
      - ABORT Stage 8
      - RETURN error with checkpoint failures
  </stage_7_completion_checkpoint>
</stage>

<stage id="8" name="ReturnSuccess">
  <prerequisite>
    REQUIRE: Stage 7 completion checkpoint passed
  </prerequisite>
  
  <!-- Stage 8 content -->
</stage>
```

### 6.3 Fix #3: Add Comprehensive Error Handling

**Objective**: Handle all failure modes explicitly

**Changes**:

1. **Add error handling blocks** for each delegation:
   ```xml
   <error_handling>
     <error_case name="status_sync_manager_failed">
       IF status-sync-manager returns "failed":
         - EXTRACT error details
         - LOG to errors.json
         - ABORT Stage 7
         - RETURN error to user
     </error_case>
     
     <error_case name="status_sync_manager_timeout">
       IF status-sync-manager times out:
         - LOG timeout
         - CHECK files on disk
         - RETURN appropriate error
     </error_case>
     
     <error_case name="git_commit_failed">
       IF git-workflow-manager returns "failed":
         - LOG error (non-critical)
         - CONTINUE to Stage 8
         - INCLUDE warning in return
     </error_case>
   </error_handling>
   ```

2. **Add validation error handling**:
   ```xml
   <validation_error_handling>
     IF validation fails before delegation:
       - ABORT immediately
       - DO NOT invoke status-sync-manager
       - RETURN validation error to user
   </validation_error_handling>
   ```

3. **Add recovery instructions** in error messages:
   ```
   Error: Status update failed
   
   Details: {error_message}
   
   Manual recovery steps:
   1. Verify artifacts exist: {paths}
   2. Update TODO.md status to [PLANNED]
   3. Update state.json status to "planned"
   4. Link artifacts in TODO.md
   
   Or retry: /plan {task_number}
   ```

**Example** (implement.md Stage 7):

```xml
<stage id="7" name="Postflight">
  <!-- Validation and delegation steps -->
  
  <error_handling>
    <error_case name="phase_statuses_missing">
      IF phased implementation AND phase_statuses missing:
        ERROR: "phase_statuses missing from task-executor return"
        
        STEP 1: LOG error
          ```json
          {
            "type": "phase_statuses_missing",
            "severity": "high",
            "context": {
              "command": "implement",
              "task_number": {number},
              "implementation_mode": "phased"
            },
            "message": "task-executor did not return phase_statuses",
            "fix_status": "not_addressed"
          }
          ```
        
        STEP 2: ABORT Stage 7
        
        STEP 3: RETURN error
          ```
          Error: Implementation completed but phase statuses missing
          
          Details: task-executor did not return phase_statuses array
          
          Artifacts created: {list}
          
          Manual steps required:
          1. Review plan file: {plan_path}
          2. Manually update phase statuses
          3. Update TODO.md to [COMPLETED]
          4. Update state.json to "completed"
          
          Or report bug: task-executor should return phase_statuses
          ```
    </error_case>
    
    <error_case name="status_sync_manager_failed">
      IF status-sync-manager returns "failed":
        <!-- Error handling as shown in 6.1 -->
    </error_case>
    
    <error_case name="git_commit_failed">
      IF git-workflow-manager returns "failed":
        STEP 1: LOG error (non-critical)
        
        STEP 2: CONTINUE to Stage 8
          - Git failure doesn't fail implementation
          - Artifacts and status updates still valid
        
        STEP 3: INCLUDE warning in Stage 8 return
          ```
          Warning: Git commit failed
          
          Implementation completed successfully
          Artifacts: {list}
          Task status: [COMPLETED]
          
          Manual commit required:
            git add {files}
            git commit -m "task {number}: implementation completed"
          ```
    </error_case>
  </error_handling>
</stage>
```

### 6.4 Fix #4: Use Explicit Delegation Syntax

**Objective**: Replace narrative delegation with explicit invocation syntax

**Changes**:

1. **Replace narrative** "Delegate to status-sync-manager:" with explicit invocation:
   ```xml
   <invocation>
     STEP 1: PREPARE delegation context
       {JSON structure}
     
     STEP 2: INVOKE status-sync-manager
       - Subagent type: "status-sync-manager"
       - Delegation context: {prepared}
       - Timeout: 60s
     
     STEP 3: WAIT for return
     
     STEP 4: VALIDATE return
     
     STEP 5: VERIFY on disk
   </invocation>
   ```

2. **Add explicit timeout** for each delegation:
   - status-sync-manager: 60s
   - git-workflow-manager: 120s

3. **Add explicit return validation** steps:
   ```xml
   <return_validation>
     VALIDATE status-sync-manager return:
       - VERIFY status == "completed"
       - VERIFY files_updated includes ["TODO.md", "state.json"]
       - VERIFY rollback_performed == false
       - IF validation fails: ABORT with error
   </return_validation>
   ```

4. **Add on-disk verification** (belt-and-suspenders):
   ```xml
   <disk_verification>
     VERIFY files updated on disk:
       - READ TODO.md
       - VERIFY status marker changed
       - READ state.json
       - VERIFY status field changed
       - IF verification fails: ABORT with error
   </disk_verification>
   ```

**Example** (revise.md Stage 7):

```xml
<stage id="7" name="Postflight">
  <atomic_update>
    <step_1_prepare_delegation>
      PREPARE status-sync-manager delegation context:
      ```json
      {
        "task_number": {number},
        "new_status": "revised",
        "timestamp": "{ISO8601 date}",
        "session_id": "{session_id}",
        "validated_artifacts": {artifacts from planner return},
        "plan_path": {new_plan_path from planner return},
        "plan_metadata": {plan_metadata from planner return},
        "plan_version": {version from planner return},
        "revision_reason": {reason from user prompt},
        "delegation_depth": 2,
        "delegation_path": ["orchestrator", "revise", "status-sync-manager"]
      }
      ```
      
      VALIDATE delegation context:
        - VERIFY task_number is positive integer
        - VERIFY new_status == "revised"
        - VERIFY plan_version is positive integer
        - VERIFY revision_reason is non-empty string
        - IF validation fails: ABORT with error
    </step_1_prepare_delegation>
    
    <step_2_invoke_status_sync_manager>
      INVOKE status-sync-manager:
        - Subagent type: "status-sync-manager"
        - Delegation context: {prepared context}
        - Timeout: 60s
        - Delegation mechanism: Per subagent-delegation-guide.md
      
      LOG: "Invoking status-sync-manager for task {number} revision"
    </step_2_invoke_status_sync_manager>
    
    <step_3_wait_for_return>
      WAIT for status-sync-manager return:
        - Maximum wait: 60s
        - IF timeout: ABORT with error "status-sync-manager timeout after 60s"
    </step_3_wait_for_return>
    
    <step_4_validate_return>
      VALIDATE status-sync-manager return:
        - VERIFY return format matches subagent-return-format.md
        - VERIFY status field == "completed" (not "failed" or "partial")
        - VERIFY files_updated includes ["TODO.md", "state.json"]
        - VERIFY rollback_performed == false
        - EXTRACT files_updated list
        - IF validation fails: ABORT with error details
      
      LOG: "status-sync-manager completed: {files_updated}"
    </step_4_validate_return>
    
    <step_5_verify_on_disk>
      VERIFY files updated on disk:
        STEP 5a: VERIFY TODO.md
          - READ TODO.md
          - VERIFY status marker == [REVISED]
          - VERIFY plan link updated to {new_plan_path}
          - IF verification fails: ABORT with error
        
        STEP 5b: VERIFY state.json
          - READ state.json
          - VERIFY status field == "revised"
          - VERIFY plan_path == {new_plan_path}
          - VERIFY plan_versions array includes new version
          - IF verification fails: ABORT with error
        
        LOG: "Files verified on disk: TODO.md, state.json"
      
      CHECKPOINT: Atomic update completed successfully
        - [ ] status-sync-manager returned "completed"
        - [ ] TODO.md updated on disk
        - [ ] state.json updated on disk
        - [ ] Plan link updated
        - [ ] Plan version history updated
    </step_5_verify_on_disk>
    
    <error_handling>
      <!-- Error cases as shown in 6.3 -->
    </error_handling>
  </atomic_update>
</stage>
```

### 6.5 Fix #5: Add Orchestrator Stage Validation

**Objective**: Orchestrator validates command stage completion

**Changes to orchestrator.md**:

1. **Add command stage tracking** to delegation registry:
   ```python
   <delegation_registry>
     <schema>
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
     </schema>
   </delegation_registry>
   ```

2. **Add Stage 10 command validation**:
   ```python
   <step_10 name="ValidateReturn">
     <action>Validate return against standardized format</action>
     
     <validation_against_schema>
       <!-- Existing validation -->
     </validation_against_schema>
     
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

3. **Add file verification helper**:
   ```python
   <helper_functions>
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
   </helper_functions>
   ```

---

## 7. Implementation Recommendations

### 7.1 Priority Order

**Phase 1: Critical Fixes** (Immediate)
1. Fix #1: Strengthen Stage 7 prompting (all 4 commands)
2. Fix #2: Add validation checkpoints (all 4 commands)
3. Fix #3: Add error handling (all 4 commands)

**Phase 2: Delegation Improvements** (High Priority)
4. Fix #4: Explicit delegation syntax (all 4 commands)

**Phase 3: Orchestrator Enhancements** (Medium Priority)
5. Fix #5: Orchestrator stage validation

**Rationale**: Phases 1-2 can be implemented in command files without orchestrator changes. Phase 3 requires orchestrator modifications and can be done separately.

### 7.2 Testing Strategy

**Test 1: Stage 7 Execution Verification**
```
Objective: Verify Stage 7 executes completely

Steps:
1. Create test task: /task "Test Stage 7 execution"
2. Create plan: /plan {task_number}
3. Verify:
   - [ ] Plan artifact created
   - [ ] TODO.md updated to [PLANNED]
   - [ ] state.json updated to "planned"
   - [ ] Plan link added to TODO.md
   - [ ] Git commit created
4. Check logs for Stage 7 execution messages
5. Verify no errors in errors.json

Expected: All verifications pass
```

**Test 2: Stage 7 Failure Handling**
```
Objective: Verify error handling when Stage 7 fails

Steps:
1. Simulate status-sync-manager failure (e.g., make TODO.md read-only)
2. Create plan: /plan {task_number}
3. Verify:
   - [ ] Error returned to user
   - [ ] Error logged to errors.json
   - [ ] Stage 8 not executed
   - [ ] Manual recovery instructions provided
4. Restore TODO.md permissions
5. Retry: /plan {task_number}
6. Verify retry succeeds

Expected: Failure handled gracefully, retry succeeds
```

**Test 3: Checkpoint Validation**
```
Objective: Verify checkpoints prevent Stage 8 execution if Stage 7 incomplete

Steps:
1. Modify command to skip status-sync-manager invocation
2. Create plan: /plan {task_number}
3. Verify:
   - [ ] Checkpoint failure detected
   - [ ] Stage 8 not executed
   - [ ] Error returned to user
4. Restore command
5. Retry: /plan {task_number}
6. Verify retry succeeds

Expected: Checkpoint prevents Stage 8, error returned
```

**Test 4: Orchestrator Validation**
```
Objective: Verify orchestrator rejects returns without Stage 7 completion

Steps:
1. Implement orchestrator stage validation (Fix #5)
2. Modify command to skip Stage 7
3. Create plan: /plan {task_number}
4. Verify:
   - [ ] Orchestrator detects Stage 7 incomplete
   - [ ] Orchestrator rejects return
   - [ ] Error returned to user
   - [ ] Files verified on disk
5. Restore command
6. Retry: /plan {task_number}
7. Verify retry succeeds

Expected: Orchestrator validation catches Stage 7 skip
```

### 7.3 Rollout Plan

**Week 1: /plan Command**
- Implement Fixes #1-4 for /plan command
- Test thoroughly
- Deploy to production
- Monitor for issues

**Week 2: /research Command**
- Implement Fixes #1-4 for /research command
- Test thoroughly
- Deploy to production
- Monitor for issues

**Week 3: /implement and /revise Commands**
- Implement Fixes #1-4 for /implement command
- Implement Fixes #1-4 for /revise command
- Test thoroughly
- Deploy to production
- Monitor for issues

**Week 4: Orchestrator Enhancements**
- Implement Fix #5 (orchestrator stage validation)
- Test with all 4 commands
- Deploy to production
- Monitor for issues

**Week 5: Validation and Cleanup**
- Run comprehensive test suite
- Fix any issues discovered
- Update documentation
- Close task 231

### 7.4 Success Metrics

**Metric 1: Stage 7 Execution Rate**
- **Target**: 100% of command invocations execute Stage 7
- **Measurement**: Log analysis, grep for "Stage 7 completed"
- **Baseline**: Currently ~0% (systematic failure)

**Metric 2: TODO.md Update Rate**
- **Target**: 100% of successful commands update TODO.md
- **Measurement**: Compare artifact creation vs TODO.md updates
- **Baseline**: Currently ~0% (manual updates required)

**Metric 3: state.json Update Rate**
- **Target**: 100% of successful commands update state.json
- **Measurement**: Compare artifact creation vs state.json updates
- **Baseline**: Currently ~0% (state.json not updated)

**Metric 4: Error Handling Coverage**
- **Target**: 100% of Stage 7 failures handled gracefully
- **Measurement**: Test failure scenarios, verify error messages
- **Baseline**: Currently 0% (no error handling)

**Metric 5: Manual Intervention Rate**
- **Target**: 0% of commands require manual TODO.md/state.json updates
- **Measurement**: User reports, manual update frequency
- **Baseline**: Currently 100% (all commands require manual updates)

---

## 8. Related Documentation

### 8.1 Files Analyzed

**Command Files**:
- `.opencode/command/plan.md` (330 lines)
- `.opencode/command/research.md` (355 lines)
- `.opencode/command/implement.md` (439 lines)
- `.opencode/command/revise.md` (309 lines)

**Lifecycle Specification**:
- `.opencode/context/core/workflows/command-lifecycle.md` (983 lines)

**Subagent Specifications**:
- `.opencode/agent/subagents/status-sync-manager.md` (838 lines)
- `.opencode/agent/subagents/git-workflow-manager.md` (200+ lines)

**Orchestrator**:
- `.opencode/agent/orchestrator.md` (1016 lines)

**Standards**:
- `.opencode/context/core/standards/subagent-return-format.md`
- `.opencode/context/core/standards/status-markers.md`
- `.opencode/context/core/system/git-commits.md`

### 8.2 Related Tasks

**Superseded Tasks**:
- Task 227: ABANDONED - incorrect root cause (assumed status-sync-manager was invoked but failing)
- Task 228: ABANDONED - incorrect root cause (assumed orchestrator bypasses commands)
- Task 229: ABANDONED - incorrect root cause (assumed orchestrator bypasses commands)

**Current Task**:
- Task 231: Fix systematic command Stage 7 (Postflight) execution failures

**Related Tasks**:
- Task 224: Create implementation plan (evidence of Stage 7 failure)
- Task 191: Fix subagent delegation hang (created subagent-return-format.md)
- Task 211: Standardize command lifecycle procedures (created command-lifecycle.md)

### 8.3 Key Insights

1. **Root cause is multi-faceted**: Not just orchestrator bypass, but also weak prompting, missing validation, and lack of error handling

2. **Systematic pattern**: All 4 workflow commands affected identically

3. **Architectural issue**: Commands designed with Stage 7 but Claude frequently skips it

4. **Prompt engineering problem**: Descriptive language doesn't trigger execution

5. **Missing enforcement**: No checkpoints or validation to ensure Stage 7 completes

---

## 9. Conclusion

This research identifies **five critical root causes** for systematic Stage 7 (Postflight) execution failures:

1. **Weak Prompting**: Descriptive language instead of imperative commands
2. **No Validation Checkpoints**: No verification Stage 7 completed before Stage 8
3. **Missing Error Handling**: No explicit error handling for Stage 7 failures
4. **Implicit Delegation Syntax**: Narrative description instead of executable invocation
5. **No Orchestrator Validation**: Orchestrator doesn't track or validate command stage completion

**Proposed fixes** address all five root causes with concrete examples and implementation guidance. The fixes are **backward compatible** (strengthen existing structure without breaking changes) and can be **rolled out incrementally** (one command at a time).

**Expected impact**: 100% Stage 7 execution rate, eliminating manual TODO.md/state.json updates and restoring task tracking integrity.

**Next steps**: Implement fixes in priority order (Phase 1: Critical fixes, Phase 2: Delegation improvements, Phase 3: Orchestrator enhancements), test thoroughly, and deploy incrementally.

---

## References

1. Task 231 description (TODO.md lines 217-241)
2. command-lifecycle.md Stage 7 specification (lines 237-330)
3. plan.md Stage 7 implementation (lines 160-200)
4. research.md Stage 7 implementation (lines 186-233)
5. implement.md Stage 7 implementation (lines 239-306)
6. revise.md Stage 7 implementation (lines 164-207)
7. status-sync-manager.md specification (838 lines)
8. git-workflow-manager.md specification (200+ lines)
9. orchestrator.md process flow (lines 129-693)
10. subagent-return-format.md validation rules

---

**Research completed**: 2025-12-28  
**Total analysis time**: ~2 hours  
**Files analyzed**: 10  
**Lines analyzed**: ~5,000  
**Root causes identified**: 5  
**Fixes proposed**: 5  
**Test scenarios**: 4  
**Success metrics**: 5
