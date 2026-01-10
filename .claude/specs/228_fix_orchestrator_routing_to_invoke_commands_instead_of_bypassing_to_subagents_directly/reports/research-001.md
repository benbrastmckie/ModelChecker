# Research Report: Orchestrator Routing Architecture Issue

**Task**: 228  
**Date**: 2025-12-28  
**Researcher**: researcher  
**Session**: sess_1766969076_gq4jvx

---

## Executive Summary

This research identifies a critical architectural flaw in the orchestrator's routing logic where it bypasses the command layer and directly invokes subagents, causing workflow commands to skip essential postflight stages (Stage 7) that update TODO.md and state.json via status-sync-manager. The root cause is in orchestrator.md Step 7 (RouteToAgent) which routes directly to subagents instead of invoking command files that contain the complete 8-stage workflow specification.

**Key Finding**: The orchestrator's Step 7 invokes subagents directly (e.g., "planner", "researcher") instead of invoking commands (e.g., "/plan", "/research"). This architectural bypass prevents command-level postflight logic from executing, leaving task tracking files unupdated despite successful artifact creation.

**Impact**: ALL workflow commands (/plan, /research, /implement, /revise) fail to update TODO.md and state.json because their Stage 7 postflight procedures never execute.

---

## 1. Root Cause Analysis

### 1.1 Current Routing Architecture (Broken)

**Orchestrator Step 7 (RouteToAgent)** - Lines 398-419 in orchestrator.md:

```python
<step_7 name="RouteToAgent">
  <action>Invoke target agent with delegation context</action>
  
  <invocation_pattern>
    ```python
    result = task_tool(
        subagent_type=target_agent,  # PROBLEM: Routes to subagent directly
        prompt=construct_prompt(request, context),
        session_id=delegation_context["session_id"],
        delegation_depth=delegation_context["delegation_depth"],
        delegation_path=delegation_context["delegation_path"],
        timeout=delegation_context["timeout"]
    )
    ```
  </invocation_pattern>
```

**Problem**: `subagent_type=target_agent` routes directly to subagents ("planner", "researcher", "task-executor") instead of routing to commands ("/plan", "/research", "/implement").

### 1.2 Delegation Chain Comparison

**Current (Broken)**:
```
User → Orchestrator Step 7 → Subagent (planner/researcher/implementer)
                                ↓
                          Artifact created
                                ↓
                          Return to orchestrator
                                ↓
                          (No postflight - TODO.md/state.json not updated)
```

**Expected (Correct)**:
```
User → Orchestrator Step 7 → Command (/plan, /research, /implement)
                                ↓
                          Command Stage 1-3: Preflight
                                ↓
                          Command Stage 4: Invoke subagent
                                ↓
                          Subagent creates artifact
                                ↓
                          Command Stage 5-6: Receive/Process results
                                ↓
                          Command Stage 7: Postflight (status-sync-manager)
                                ↓
                          TODO.md + state.json updated atomically
                                ↓
                          Command Stage 8: Return to orchestrator
```

### 1.3 Evidence from Command Files

**plan.md** (Lines 160-200) specifies Stage 7 Postflight:

```xml
<stage id="7" name="Postflight">
  <status_transition>
    Completion: [PLANNED] + **Completed**: {date}
  </status_transition>
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
</stage>
```

**This stage never executes** when orchestrator routes directly to planner subagent.

### 1.4 Command-Lifecycle.md 8-Stage Pattern

All workflow commands follow the standardized 8-stage pattern (command-lifecycle.md):

1. **Preflight**: Parse arguments, validate task, update status to in-progress
2. **CheckLanguage/DetermineRouting**: Extract language, determine target agent
3. **PrepareDelegation**: Generate session_id, prepare delegation context
4. **InvokeAgent**: Delegate to subagent
5. **ReceiveResults**: Wait for and validate subagent return
6. **ProcessResults**: Extract artifacts, summary, errors
7. **Postflight**: Update TODO.md/state.json via status-sync-manager, create git commit
8. **ReturnSuccess**: Return brief summary to user

**Stage 7 is CRITICAL** - it delegates to status-sync-manager for atomic updates across:
- TODO.md (status markers, timestamps, artifact links)
- state.json (status, timestamps, artifacts array, plan_metadata)
- project state.json (lazy created on first artifact write)
- plan file (phase statuses if applicable)

When orchestrator bypasses commands and routes directly to subagents, **Stages 1-3 and 5-8 never execute**, only Stage 4 (the subagent invocation) happens.

---

## 2. Affected Commands Analysis

### 2.1 /plan Command

**Command File**: .opencode/command/plan.md  
**Current Routing**: Orchestrator Step 4 → `agent = "planner"` → Orchestrator Step 7 → Direct to planner subagent  
**Expected Routing**: Orchestrator → /plan command → planner subagent → /plan postflight → status-sync-manager

**Missing Stages**:
- Stage 1: Preflight (argument parsing, status update to [PLANNING])
- Stage 2: HarvestResearch (extract research links from TODO.md)
- Stage 7: Postflight (update to [PLANNED], link plan artifact, git commit)
- Stage 8: ReturnSuccess (brief summary to user)

**Impact**: Plan artifact created successfully, but TODO.md remains [NOT STARTED] or [RESEARCHED], no plan link added, state.json not updated, no git commit.

### 2.2 /research Command

**Command File**: .opencode/command/research.md  
**Current Routing**: Orchestrator Step 4 → `agent = "researcher"` or `"lean-research-agent"` → Direct to subagent  
**Expected Routing**: Orchestrator → /research command → researcher/lean-research-agent → /research postflight → status-sync-manager

**Missing Stages**:
- Stage 1: Preflight (argument parsing, status update to [RESEARCHING])
- Stage 2: CheckLanguage (extract language for routing validation)
- Stage 7: Postflight (update to [RESEARCHED], link research artifacts, git commit)
- Stage 8: ReturnSuccess (brief summary to user)

**Impact**: Research artifacts created, but TODO.md remains [NOT STARTED], no research links added, state.json not updated, no git commit.

### 2.3 /implement Command

**Command File**: .opencode/command/implement.md  
**Current Routing**: Orchestrator Step 4 → `agent = "task-executor"` or `"implementer"` or `"lean-implementation-agent"` → Direct to subagent  
**Expected Routing**: Orchestrator → /implement command → appropriate subagent → /implement postflight → status-sync-manager

**Missing Stages**:
- Stage 1: Preflight (argument parsing, status update to [IMPLEMENTING], resume logic)
- Stage 2: DetermineRouting (extract language and plan status for routing)
- Stage 7: Postflight (update to [COMPLETED], link implementation artifacts, update plan phases, git commit)
- Stage 8: ReturnSuccess (brief summary to user)

**Impact**: Implementation artifacts created, but TODO.md remains [PLANNED]/[REVISED], no completion marker, no checkmark, state.json not updated, plan phases not updated, no git commit.

### 2.4 /revise Command

**Command File**: .opencode/command/revise.md  
**Current Routing**: Orchestrator Step 4 → `agent = "planner"` (with revision context) → Direct to planner  
**Expected Routing**: Orchestrator → /revise command → planner → /revise postflight → status-sync-manager

**Missing Stages**:
- Stage 1: Preflight (argument parsing, status update to [REVISING])
- Stage 7: Postflight (update to [REVISED], link new plan version, update plan_versions array, git commit)
- Stage 8: ReturnSuccess (brief summary to user)

**Impact**: Revised plan artifact created, but TODO.md remains [PLANNED], no new plan link, plan_versions array not updated in state.json, no git commit.

---

## 3. Orchestrator Routing Logic Analysis

### 3.1 Step 4 (PrepareRouting) - Lines 219-332

**Current Implementation**:

```xml
<routing_logic>
  <plan_command>
    Target: planner (language-agnostic)
    Log: "Routing /plan (task ${task_number}) to planner"
  </plan_command>
  
  <research_command>
    Use explicit IF/ELSE logic:
    ```
    IF language == "lean":
      agent = "lean-research-agent"
      Log: "Routing /research (task ${task_number}, Language: lean) to lean-research-agent"
    ELSE:
      agent = "researcher"
      Log: "Routing /research (task ${task_number}, Language: ${language}) to researcher"
    ```
  </research_command>
  
  <implement_command>
    Use explicit IF/ELSE logic for all 4 cases:
    ```
    IF language == "lean" AND has_plan == true:
      agent = "lean-implementation-agent"
      mode = "phased"
    ELSE IF language == "lean" AND has_plan == false:
      agent = "lean-implementation-agent"
      mode = "simple"
    ELSE IF language != "lean" AND has_plan == true:
      agent = "task-executor"
      mode = "phased"
    ELSE IF language != "lean" AND has_plan == false:
      agent = "implementer"
      mode = "direct"
    ```
  </implement_command>
</routing_logic>
```

**Problem**: Step 4 determines the **subagent** to invoke, not the **command** to invoke. This is correct for the command layer to use, but incorrect for the orchestrator to use directly.

### 3.2 Step 7 (RouteToAgent) - Lines 398-419

**Current Implementation**:

```xml
<step_7 name="RouteToAgent">
  <action>Invoke target agent with delegation context</action>
  
  <invocation_pattern>
    ```python
    result = task_tool(
        subagent_type=target_agent,  # Uses agent from Step 4
        prompt=construct_prompt(request, context),
        session_id=delegation_context["session_id"],
        delegation_depth=delegation_context["delegation_depth"],
        delegation_path=delegation_context["delegation_path"],
        timeout=delegation_context["timeout"]
    )
    ```
  </invocation_pattern>
</step_7>
```

**Problem**: `subagent_type=target_agent` invokes the subagent directly. Should invoke the command instead.

### 3.3 Correct Routing Pattern

**Orchestrator should route to commands, not subagents**:

```python
# WRONG (current):
result = task_tool(
    subagent_type="planner",  # Direct to subagent
    ...
)

# CORRECT (needed):
result = invoke_command(
    command="/plan",  # Invoke command
    arguments="224",  # Pass task number
    ...
)
```

The command file then handles:
1. Argument parsing
2. Language extraction
3. Subagent routing (using the logic currently in orchestrator Step 4)
4. Subagent invocation
5. Result processing
6. Postflight (status-sync-manager delegation)
7. Return to orchestrator

---

## 4. Command vs Subagent Delegation Patterns

### 4.1 Command Invocation Pattern

**What Commands Are**:
- Complete workflow specifications with 8 stages
- Contain argument parsing logic (`<argument_parsing>` section)
- Contain routing logic (which subagent to invoke based on language/plan)
- Contain postflight logic (status-sync-manager delegation)
- Contain git commit logic
- Return brief summaries to orchestrator (<100 tokens)

**Command Files**:
- .opencode/command/plan.md
- .opencode/command/research.md
- .opencode/command/implement.md
- .opencode/command/revise.md
- .opencode/command/review.md
- .opencode/command/task.md
- .opencode/command/todo.md
- .opencode/command/errors.md

**Command Invocation** (how orchestrator should work):
```
User: /plan 224
  ↓
Orchestrator: Invoke /plan command with arguments="224"
  ↓
/plan command: Execute 8-stage workflow
  ↓
/plan Stage 4: Invoke planner subagent
  ↓
planner: Create plan artifact, return standardized format
  ↓
/plan Stage 7: Delegate to status-sync-manager
  ↓
status-sync-manager: Update TODO.md + state.json atomically
  ↓
/plan Stage 8: Return brief summary to orchestrator
  ↓
Orchestrator: Return to user
```

### 4.2 Subagent Invocation Pattern

**What Subagents Are**:
- Specialized workers that perform specific tasks
- Receive inputs with delegation context
- Execute task (may delegate to specialists)
- Create artifacts
- Return standardized format (status, summary, artifacts, metadata, errors)
- Do NOT update TODO.md or state.json (that's the command's job)

**Subagent Files**:
- .opencode/agent/subagents/planner.md
- .opencode/agent/subagents/researcher.md
- .opencode/agent/subagents/lean-research-agent.md
- .opencode/agent/subagents/lean-implementation-agent.md
- .opencode/agent/subagents/task-executor.md
- .opencode/agent/subagents/implementer.md
- .opencode/agent/subagents/status-sync-manager.md
- .opencode/agent/subagents/git-workflow-manager.md

**Subagent Invocation** (how commands work internally):
```
Command Stage 4: Invoke subagent
  ↓
Subagent: Receive delegation context
  ↓
Subagent: Execute task, create artifacts
  ↓
Subagent: Validate artifacts
  ↓
Subagent: Return standardized format
  ↓
Command Stage 5: Receive and validate return
  ↓
Command Stage 6: Process results
  ↓
Command Stage 7: Postflight (status updates)
```

### 4.3 Key Difference

**Commands** = Complete workflows with status tracking  
**Subagents** = Task executors that create artifacts

**Orchestrator should invoke commands, not subagents.**

---

## 5. Command-Lifecycle.md Integration

### 5.1 8-Stage Pattern Overview

From command-lifecycle.md (lines 40-442):

```
Stage 1: Preflight
  - Parse arguments, validate task, update status to in-progress

Stage 2: CheckLanguage / DetermineRouting
  - Extract language field, determine target agent

Stage 3: PrepareDelegation
  - Generate session_id, prepare delegation context

Stage 4: InvokeAgent
  - Delegate to subagent with session tracking

Stage 5: ReceiveResults
  - Wait for and validate subagent return

Stage 6: ProcessResults
  - Extract artifacts, summary, errors

Stage 7: Postflight
  - Update status via status-sync-manager
  - Link artifacts in TODO.md
  - Create git commit

Stage 8: ReturnSuccess
  - Return brief summary to user
```

### 5.2 Stage 7 Postflight Critical Importance

From command-lifecycle.md (lines 234-330):

```xml
<stage id="7" name="Postflight">
  <purpose>Update status, link artifacts, create git commit</purpose>
  
  <update_procedures>
    CRITICAL: All status and artifact updates in Stage 7 MUST be delegated 
    to status-sync-manager to ensure atomicity across all tracking files.
    
    WARNING: DO NOT manually update TODO.md, state.json, project state.json, 
    or plan files directly. Manual updates create race conditions and 
    inconsistent state. ALL updates MUST flow through status-sync-manager's 
    two-phase commit protocol.
  </update_procedures>
  
  <delegation_mandatory>
    Delegate to status-sync-manager:
      - task_number: {number}
      - new_status: {status from subagent return}
      - timestamp: {ISO8601 date}
      - session_id: {session_id}
      - validated_artifacts: {artifacts from subagent return}
      - plan_metadata: {metadata from planner if applicable}
      - plan_version: {version from revise if applicable}
      - phase_statuses: {statuses from implement if applicable}
      - plan_path: {path to plan file if applicable}
  </delegation_mandatory>
  
  <atomicity_guarantees>
    status-sync-manager ensures atomic updates across:
    - TODO.md (status markers, timestamps, artifact links)
    - state.json (status, timestamps, artifacts array, plan_metadata, plan_versions)
    - project state.json (lazy created on first artifact write)
    - plan file (phase statuses if phase_statuses provided)
    
    Either all files update successfully or all are rolled back to original state.
  </atomicity_guarantees>
</stage>
```

**This entire stage is skipped when orchestrator bypasses commands.**

### 5.3 Command-Specific Variations

From command-lifecycle.md Variation Table 1 (lines 484-492):

| Command | In-Progress Marker | Completion Marker |
|---------|-------------------|-------------------|
| /research | [RESEARCHING] | [RESEARCHED] |
| /plan | [PLANNING] | [PLANNED] |
| /revise | [REVISING] | [REVISED] |
| /implement | [IMPLEMENTING] | [COMPLETED] |

**None of these status transitions occur when orchestrator bypasses commands.**

---

## 6. Architectural Solution

### 6.1 Required Changes to Orchestrator

**File**: .opencode/agent/orchestrator.md

**Change 1: Modify Step 4 (PrepareRouting)** - Lines 219-332

Replace subagent routing with command routing:

```xml
<routing_logic>
  <task_command>
    Target: /task command
    Arguments: {task_description}
    Log: "Routing user request to /task command"
  </task_command>
  
  <research_command>
    Target: /research command
    Arguments: {task_number} {optional_prompt}
    Log: "Routing user request to /research command (task ${task_number})"
  </research_command>
  
  <plan_command>
    Target: /plan command
    Arguments: {task_number} {optional_prompt}
    Log: "Routing user request to /plan command (task ${task_number})"
  </plan_command>
  
  <implement_command>
    Target: /implement command
    Arguments: {task_number_or_range} {optional_prompt}
    Log: "Routing user request to /implement command (task ${task_number})"
  </implement_command>
  
  <revise_command>
    Target: /revise command
    Arguments: {task_number} {revision_context}
    Log: "Routing user request to /revise command (task ${task_number})"
  </revise_command>
  
  <review_command>
    Target: /review command
    Arguments: {optional_scope}
    Log: "Routing user request to /review command"
  </review_command>
  
  <todo_command>
    Target: /todo command
    Arguments: {optional_flags}
    Log: "Routing user request to /todo command"
  </todo_command>
  
  <errors_command>
    Target: /errors command
    Arguments: {optional_filters}
    Log: "Routing user request to /errors command"
  </errors_command>
</routing_logic>
```

**Change 2: Modify Step 7 (RouteToAgent)** - Lines 398-419

Replace direct subagent invocation with command invocation:

```xml
<step_7 name="RouteToCommand">
  <action>Invoke target command with arguments</action>
  
  <invocation_pattern>
    ```python
    # Load command file
    command_file = load_command_file(target_command)
    
    # Substitute $ARGUMENTS in command file
    command_file = substitute_arguments(command_file, arguments)
    
    # Execute command workflow
    result = execute_command(
        command_file=command_file,
        session_id=delegation_context["session_id"],
        delegation_depth=0,  # Orchestrator → Command is depth 0
        delegation_path=["orchestrator"],
        timeout=delegation_context["timeout"]
    )
    ```
  </invocation_pattern>
  
  <command_execution>
    Command file executes its 8-stage workflow:
    1. Preflight: Parse arguments, validate, update status
    2. CheckLanguage/DetermineRouting: Extract language, determine subagent
    3. PrepareDelegation: Generate session_id, prepare context
    4. InvokeAgent: Delegate to subagent (depth 1)
    5. ReceiveResults: Wait for and validate subagent return
    6. ProcessResults: Extract artifacts, summary, errors
    7. Postflight: Delegate to status-sync-manager, create git commit
    8. ReturnSuccess: Return brief summary to orchestrator
  </command_execution>
  
  <output>Command execution result (brief summary + artifacts)</output>
</step_7>
```

**Change 3: Remove Language Extraction from Orchestrator**

The orchestrator's Step 3 (CheckLanguage) should be removed or simplified. Language extraction should happen in the command layer (Stage 2 of command-lifecycle.md), not in the orchestrator.

**Rationale**: Commands know which language field to extract and how to route based on it. Orchestrator doesn't need this information - it just needs to route to the correct command.

### 6.2 Command Layer Responsibilities

Commands already have the correct structure (no changes needed):

1. **Argument Parsing** (Stage 1): Extract task_number, prompt, flags from $ARGUMENTS
2. **Language Extraction** (Stage 2): Extract Language field from TODO.md using bash
3. **Routing Decision** (Stage 2): Determine which subagent to invoke based on language/plan
4. **Subagent Invocation** (Stage 4): Delegate to appropriate subagent
5. **Result Processing** (Stages 5-6): Validate and extract artifacts
6. **Postflight** (Stage 7): Delegate to status-sync-manager for atomic updates
7. **Return** (Stage 8): Return brief summary to orchestrator

### 6.3 Delegation Depth Adjustment

**Current**:
```
Orchestrator (depth 0) → Subagent (depth 1) → Specialist (depth 2)
```

**Corrected**:
```
Orchestrator (depth 0) → Command (depth 0) → Subagent (depth 1) → Specialist (depth 2)
```

**Rationale**: Orchestrator → Command is not counted as delegation depth because commands are part of the orchestrator's workflow execution layer, not separate agents. The delegation depth counter starts when commands invoke subagents.

---

## 7. Testing Strategy

### 7.1 Test Case 1: /plan Command

**Setup**:
- Task 224 exists in TODO.md with status [RESEARCHED]
- Research artifacts linked in TODO.md

**Execute**:
```
/plan 224
```

**Expected Behavior**:
1. Orchestrator routes to /plan command (not planner subagent)
2. /plan Stage 1: Updates TODO.md to [PLANNING]
3. /plan Stage 2: Harvests research links from TODO.md
4. /plan Stage 4: Invokes planner subagent
5. planner: Creates plan artifact, returns standardized format
6. /plan Stage 7: Delegates to status-sync-manager
7. status-sync-manager: Updates TODO.md to [PLANNED], adds plan link, updates state.json
8. /plan Stage 7: Creates git commit
9. /plan Stage 8: Returns brief summary to orchestrator
10. Orchestrator: Returns to user

**Validation**:
- [ ] TODO.md shows `- **Status**: [PLANNED]`
- [ ] TODO.md shows `- **Plan**: [path/to/plan]`
- [ ] state.json shows `"status": "planned"`
- [ ] state.json shows `"plan_path": "path/to/plan"`
- [ ] state.json shows `"plan_metadata": {...}`
- [ ] Git commit created with message "task 224: plan created"
- [ ] User receives brief summary (<100 tokens)

### 7.2 Test Case 2: /research Command

**Setup**:
- Task 225 exists in TODO.md with status [NOT STARTED]
- Language field set to "lean"

**Execute**:
```
/research 225
```

**Expected Behavior**:
1. Orchestrator routes to /research command (not researcher subagent)
2. /research Stage 1: Updates TODO.md to [RESEARCHING]
3. /research Stage 2: Extracts Language="lean", routes to lean-research-agent
4. /research Stage 4: Invokes lean-research-agent
5. lean-research-agent: Creates research artifact, returns standardized format
6. /research Stage 7: Delegates to status-sync-manager
7. status-sync-manager: Updates TODO.md to [RESEARCHED], adds research link, updates state.json
8. /research Stage 7: Creates git commit
9. /research Stage 8: Returns brief summary to orchestrator
10. Orchestrator: Returns to user

**Validation**:
- [ ] TODO.md shows `- **Status**: [RESEARCHED]`
- [ ] TODO.md shows `- **Research Artifacts**: [path/to/research]`
- [ ] state.json shows `"status": "researched"`
- [ ] Git commit created with message "task 225: research completed"
- [ ] User receives brief summary (<100 tokens)

### 7.3 Test Case 3: /implement Command

**Setup**:
- Task 226 exists in TODO.md with status [PLANNED]
- Plan artifact linked in TODO.md
- Language field set to "markdown"

**Execute**:
```
/implement 226
```

**Expected Behavior**:
1. Orchestrator routes to /implement command (not task-executor)
2. /implement Stage 1: Updates TODO.md to [IMPLEMENTING]
3. /implement Stage 2: Extracts Language="markdown", has_plan=true, routes to task-executor
4. /implement Stage 4: Invokes task-executor
5. task-executor: Executes phases, creates implementation artifacts, returns standardized format with phase_statuses
6. /implement Stage 7: Delegates to status-sync-manager with phase_statuses
7. status-sync-manager: Updates TODO.md to [COMPLETED], adds checkmark, updates state.json, updates plan phases
8. /implement Stage 7: Creates git commit
9. /implement Stage 8: Returns brief summary to orchestrator
10. Orchestrator: Returns to user

**Validation**:
- [ ] TODO.md shows `- **Status**: [COMPLETED]` with checkmark
- [ ] TODO.md shows `- **Implementation**: [paths]`
- [ ] state.json shows `"status": "completed"`
- [ ] Plan file shows phase statuses updated to [COMPLETED]
- [ ] Git commit created with message "task 226: implementation completed"
- [ ] User receives brief summary (<100 tokens)

---

## 8. Impact Analysis

### 8.1 Affected Workflows

**ALL workflow commands affected**:
- /plan (100% broken - no TODO.md/state.json updates)
- /research (100% broken - no TODO.md/state.json updates)
- /implement (100% broken - no TODO.md/state.json updates, no plan phase updates)
- /revise (100% broken - no TODO.md/state.json updates, no plan version tracking)

**Unaffected commands**:
- /task (doesn't use command layer, direct orchestrator execution)
- /todo (doesn't use command layer, direct orchestrator execution)
- /review (may be affected, needs investigation)
- /errors (may be affected, needs investigation)

### 8.2 Severity Assessment

**Severity**: CRITICAL

**Rationale**:
1. **Complete workflow failure**: All 4 primary workflow commands fail to update task tracking
2. **Data integrity violation**: Artifacts created but tracking files not updated (inconsistent state)
3. **Workflow dependency breakage**: Tasks appear NOT STARTED when actually RESEARCHED/PLANNED
4. **Git history loss**: No automatic commits, manual intervention required
5. **User confusion**: Success messages shown but TODO.md unchanged

### 8.3 Relationship to Other Tasks

**Task 227**: Fix systematic status-sync-manager TODO.md update failures

Task 227 assumes status-sync-manager is being invoked but failing. This research reveals status-sync-manager is **never invoked** because orchestrator bypasses the command layer that would invoke it.

**Resolution**: Task 228 (this task) must be completed FIRST. Once orchestrator routes to commands instead of subagents, command Stage 7 will invoke status-sync-manager, and then Task 227 can investigate any remaining update failures.

**Task 221**: (Referenced in Task 227 description) Addressed missing delegation

Task 221 likely added delegation specifications to command files but didn't fix the orchestrator routing to actually use those commands.

---

## 9. Implementation Recommendations

### 9.1 Phased Approach

**Phase 1: Orchestrator Routing Fix** (2-3 hours)
- Modify orchestrator.md Step 4 to route to commands instead of subagents
- Modify orchestrator.md Step 7 to invoke commands instead of subagents
- Remove or simplify orchestrator.md Step 3 (language extraction - commands handle this)
- Update delegation depth counting (Orchestrator → Command = depth 0)

**Phase 2: Testing and Validation** (1-2 hours)
- Test /plan command with real task
- Test /research command with real task (both lean and general)
- Test /implement command with real task (with and without plan)
- Test /revise command with real task
- Verify TODO.md and state.json updates occur
- Verify git commits created
- Verify brief summaries returned to user

**Phase 3: Documentation Update** (0.5-1 hour)
- Update ARCHITECTURE.md with corrected delegation flow
- Update orchestrator.md with command invocation pattern
- Add troubleshooting guide for routing issues

### 9.2 Rollback Plan

If command invocation fails:
1. Revert orchestrator.md to previous version
2. Investigate command file issues
3. Fix command files if needed
4. Retry orchestrator changes

### 9.3 Monitoring

After deployment:
- Monitor TODO.md updates after each workflow command
- Monitor state.json updates after each workflow command
- Monitor git commits after each workflow command
- Check for any delegation hangs or timeouts
- Verify brief summaries returned (<100 tokens)

---

## 10. Conclusion

The root cause of /plan (and all workflow commands) failing to update TODO.md and state.json is the orchestrator's architectural flaw of routing directly to subagents instead of invoking commands. Commands contain the complete 8-stage workflow including critical Stage 7 (Postflight) that delegates to status-sync-manager for atomic updates.

**Fix**: Modify orchestrator.md Step 4 and Step 7 to route to commands (/plan, /research, /implement, /revise) instead of subagents (planner, researcher, task-executor, implementer). Commands will then execute their full lifecycle including postflight status updates.

**Priority**: CRITICAL - This is a foundational architectural issue affecting all workflow commands. Must be fixed before Task 227 (status-sync-manager investigation) can proceed.

**Effort**: 3-4 hours (2-3 hours implementation, 1-2 hours testing)

---

## References

1. .opencode/agent/orchestrator.md (Lines 1-700+)
2. .opencode/context/core/workflows/command-lifecycle.md (Lines 1-983)
3. .opencode/command/plan.md (Lines 1-330)
4. .opencode/command/research.md (Lines 1-355)
5. .opencode/command/implement.md (Lines 1-439)
6. .opencode/context/core/workflows/subagent-delegation-guide.md (Lines 1-649)
7. .opencode/ARCHITECTURE.md (Lines 1-816)
8. .opencode/agent/subagents/planner.md (Lines 1-385)
9. .opencode/specs/TODO.md Task 228 (Lines 101-130)
10. .opencode/specs/TODO.md Task 227 (Lines 61-99)
