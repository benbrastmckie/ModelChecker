# Orchestrator-Command Integration Architecture Review

**Task**: 229  
**Date**: 2025-12-28  
**Researcher**: researcher  
**Session**: sess_229_research_001

---

## Executive Summary

This research identifies a **critical architectural flaw** where orchestrator.md routes directly to subagents instead of to commands, bypassing the entire command lifecycle (8 stages), causing context bloat in the orchestrator, missing preflight/postflight procedures, and systematic status update failures. The fix is straightforward but foundational: orchestrator must route to commands, not subagents.

**Root Cause**: Orchestrator Step 7 (RouteToAgent) invokes subagents directly (e.g., `subagent_type="planner"`) instead of invoking commands (e.g., `command="/plan"`). This architectural bypass prevents command-level workflow execution.

**Impact**: 
- **100% workflow failure**: All 4 workflow commands (/plan, /research, /implement, /revise) skip postflight Stage 7 → no TODO.md/state.json updates
- **60-70% context bloat**: Orchestrator loads context meant for commands (language routing, validation logic, domain context)
- **Architecture violation**: Subagents exposed as primary delegation targets instead of implementation tools

**Expected Outcomes After Fix**:
1. 60-70% reduction in orchestrator context window
2. 100% workflow completion (preflight + postflight)
3. Clear architectural layers (orchestrator → command → subagent)
4. Context loaded exactly where needed
5. All status updates via status-sync-manager
6. Proper git commit integration

---

## 1. Current Architecture Analysis

### 1.1 Actual Routing Flow (Broken)

**Current Flow**:
```
User: /plan 224
  ↓
Orchestrator Step 1: AnalyzeRequest
  - Loads: .opencode/command/plan.md
  - Substitutes: $ARGUMENTS = "224"
  - Reads argument_parsing section
  ↓
Orchestrator Step 2: DetermineComplexity
  - Assesses: Level 2 (Filtered)
  ↓
Orchestrator Step 3: CheckLanguage
  - Extracts: Language field from TODO.md using bash
  - Logs: "Task 224 language: markdown"
  ↓
Orchestrator Step 4: PrepareRouting
  - Determines: agent = "planner" (WRONG - should be command="/plan")
  - Logs: "Routing /plan (task 224) to planner"
  ↓
Orchestrator Step 7: RouteToAgent
  - Invokes: task_tool(subagent_type="planner", ...) (BYPASSES COMMAND)
  ↓
planner subagent:
  - Creates plan artifact
  - Returns standardized format
  ↓
Orchestrator Step 9-13: ReceiveResults, ValidateReturn, ProcessResults, ReturnToUser
  - Validates return
  - Returns to user
  ↓
RESULT: Plan artifact created [PASS], TODO.md NOT updated [FAIL], state.json NOT updated [FAIL]
```

**Problem**: Orchestrator routes directly to planner subagent, bypassing /plan command's 8-stage workflow.

### 1.2 Expected Routing Flow (Correct)

**Expected Flow**:
```
User: /plan 224
  ↓
Orchestrator Step 1: AnalyzeRequest
  - Identifies: command = "/plan"
  - Extracts: arguments = "224"
  ↓
Orchestrator Step 7: RouteToCommand (RENAMED from RouteToAgent)
  - Invokes: execute_command(command="/plan", arguments="224")
  ↓
/plan command Stage 1: Preflight
  - Parses: task_number = 224
  - Updates: TODO.md to [PLANNING]
  - Updates: state.json status = "planning"
  ↓
/plan command Stage 2: HarvestResearch
  - Extracts: research links from TODO.md
  - Loads: research artifacts for context
  ↓
/plan command Stage 3: PrepareDelegation
  - Generates: session_id
  - Prepares: delegation context
  ↓
/plan command Stage 4: InvokeAgent
  - Invokes: planner subagent (depth 1)
  ↓
planner subagent:
  - Creates plan artifact
  - Returns standardized format
  ↓
/plan command Stage 5: ReceiveResults
  - Validates: return format
  ↓
/plan command Stage 6: ProcessResults
  - Extracts: artifacts, plan_metadata
  ↓
/plan command Stage 7: Postflight (CRITICAL - CURRENTLY SKIPPED)
  - Delegates: to status-sync-manager
  - Updates: TODO.md to [PLANNED], adds plan link
  - Updates: state.json with plan_path, plan_metadata
  - Creates: git commit "task 224: plan created"
  ↓
/plan command Stage 8: ReturnSuccess
  - Returns: brief summary to orchestrator
  ↓
Orchestrator: Returns to user
  ↓
RESULT: Plan artifact created [PASS], TODO.md updated [PASS], state.json updated [PASS], git commit [PASS]
```

**Solution**: Orchestrator routes to /plan command, which executes full 8-stage workflow including postflight.

### 1.3 Evidence from Orchestrator.md

**Step 4 (PrepareRouting)** - Lines 219-332:

```xml
<routing_logic>
  <plan_command>
    Target: planner (language-agnostic)
    Log: "Routing /plan (task ${task_number}) to planner"
  </plan_command>
  
  <research_command>
    IF language == "lean":
      agent = "lean-research-agent"
    ELSE:
      agent = "researcher"
  </research_command>
  
  <implement_command>
    IF language == "lean" AND has_plan == true:
      agent = "lean-implementation-agent"
      mode = "phased"
    ELSE IF language != "lean" AND has_plan == true:
      agent = "task-executor"
      mode = "phased"
    ...
  </implement_command>
</routing_logic>
```

**Problem**: Routes to **subagents** (planner, researcher, task-executor), not **commands** (/plan, /research, /implement).

**Step 7 (RouteToAgent)** - Lines 398-419:

```xml
<step_7 name="RouteToAgent">
  <action>Invoke target agent with delegation context</action>
  
  <invocation_pattern>
    result = task_tool(
        subagent_type=target_agent,  # PROBLEM: Direct to subagent
        prompt=construct_prompt(request, context),
        session_id=delegation_context["session_id"],
        delegation_depth=delegation_context["delegation_depth"],
        delegation_path=delegation_context["delegation_path"],
        timeout=delegation_context["timeout"]
    )
  </invocation_pattern>
</step_7>
```

**Problem**: `subagent_type=target_agent` invokes subagent directly, bypassing command layer.

---

## 2. Context Bloat Investigation

### 2.1 Orchestrator Context Loading

**Current Context Loaded** (orchestrator.md lines 32-36):

```xml
<context_loaded>
  @.opencode/context/core/standards/subagent-return-format.md
  @.opencode/context/core/workflows/subagent-delegation-guide.md
  @.opencode/context/core/standards/status-markers.md
</context_loaded>
```

**Plus Dynamic Context** (lines 16-30):

```xml
<context_loading>
  <level_1 coverage="80%">
    Common standards (return format, status markers)
    Common workflows (delegation guide)
  </level_1>
  
  <level_2 coverage="20%">
    Level 1 + Project-specific context based on language
    - lean: Load .opencode/context/project/lean4/
    - markdown: Load .opencode/context/project/repo/
  </level_2>
  
  <level_3 coverage="rare">
    All context loaded for complex requests
  </level_3>
</context_loading>
```

**Plus Routing Logic** (lines 219-332):
- Language extraction logic (belongs in commands)
- Plan detection logic (belongs in commands)
- Subagent routing rules (belongs in commands)
- Validation logic (belongs in commands)

**Estimated Total**: ~15,000-20,000 tokens for Level 2 operations

### 2.2 Command Context Loading

**Example: plan.md** (lines 11-18):

```
Context Loaded:
@.opencode/context/core/workflows/command-lifecycle.md
@.opencode/specs/TODO.md
@.opencode/specs/state.json
@.opencode/context/core/standards/status-markers.md
@.opencode/context/core/standards/subagent-return-format.md
@.opencode/context/core/workflows/subagent-delegation-guide.md
@.opencode/context/core/system/git-commits.md
```

**Plus Command-Specific Context**:
- context_level: 2 (Filtered)
- language: markdown (from frontmatter)
- Domain context for planning

**Estimated Total**: ~10,000-12,000 tokens

### 2.3 Context Duplication Analysis

**Duplicated Context** (loaded by both orchestrator AND commands):

| Context File | Orchestrator | Commands | Size (est.) | Duplication |
|--------------|--------------|----------|-------------|-------------|
| subagent-return-format.md | [PASS] | [PASS] | ~2,000 tokens | 100% |
| subagent-delegation-guide.md | [PASS] | [PASS] | ~3,500 tokens | 100% |
| status-markers.md | [PASS] | [PASS] | ~4,000 tokens | 100% |
| **Total Duplication** | | | **~9,500 tokens** | |

**Orchestrator-Only Context** (should NOT be in orchestrator):

| Context | Current | Should Be | Size (est.) | Bloat |
|---------|---------|-----------|-------------|-------|
| Language routing logic | Orchestrator | Commands | ~1,000 tokens | 100% |
| Plan detection logic | Orchestrator | Commands | ~500 tokens | 100% |
| Subagent routing rules | Orchestrator | Commands | ~2,000 tokens | 100% |
| Project-specific context (Level 2) | Orchestrator | Commands | ~8,000 tokens | 100% |
| **Total Bloat** | | | **~11,500 tokens** | |

**Total Context Waste**: ~21,000 tokens (9,500 duplication + 11,500 bloat)

### 2.4 Optimal Context Distribution

**Orchestrator Should Load** (~5,000 tokens):
- Delegation registry management
- Return format validation (subagent-return-format.md)
- Delegation safety (subagent-delegation-guide.md)
- Command routing map (simple: /plan → plan.md, /research → research.md)
- Timeout configuration

**Commands Should Load** (~10,000-12,000 tokens):
- Command lifecycle pattern (command-lifecycle.md)
- TODO.md and state.json (task context)
- Status markers (status-markers.md)
- Git commit patterns (git-commits.md)
- Language-specific routing logic
- Domain-specific context (filtered by context_level)

**Subagents Should Load** (~5,000-8,000 tokens):
- Task-specific context from command
- Domain knowledge for their specialty
- Return format standard (for validation)

**Expected Reduction**: 60-70% reduction in orchestrator context (21,000 → 5,000 tokens)

---

## 3. Workflow Execution Gaps

### 3.1 Command Lifecycle Stages

**8-Stage Pattern** (command-lifecycle.md):

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

Stage 7: Postflight (CRITICAL - CURRENTLY SKIPPED)
  - Update status via status-sync-manager
  - Link artifacts in TODO.md
  - Create git commit

Stage 8: ReturnSuccess
  - Return brief summary to user
```

### 3.2 Stages Executed vs Skipped

**Current Execution** (orchestrator routes to subagent):

| Stage | Executed? | By Whom | Impact |
|-------|-----------|---------|--------|
| 1. Preflight | [FAIL] | N/A | No status update to [PLANNING]/[RESEARCHING]/[IMPLEMENTING] |
| 2. CheckLanguage | [WARN] | Orchestrator | Wrong layer - belongs in command |
| 3. PrepareDelegation | [WARN] | Orchestrator | Wrong layer - belongs in command |
| 4. InvokeAgent | [PASS] | Orchestrator | Subagent invoked (but bypasses command) |
| 5. ReceiveResults | [PASS] | Orchestrator | Return validated |
| 6. ProcessResults | [WARN] | Orchestrator | Partial - no artifact linking |
| 7. Postflight | [FAIL] | N/A | **NO TODO.md/state.json updates, NO git commits** |
| 8. ReturnSuccess | [WARN] | Orchestrator | Returns to user but incomplete |

**Expected Execution** (orchestrator routes to command):

| Stage | Executed? | By Whom | Impact |
|-------|-----------|---------|--------|
| 1. Preflight | [PASS] | Command | Status updated to in-progress |
| 2. CheckLanguage | [PASS] | Command | Language extracted, routing determined |
| 3. PrepareDelegation | [PASS] | Command | Session ID generated, context prepared |
| 4. InvokeAgent | [PASS] | Command | Subagent invoked (depth 1) |
| 5. ReceiveResults | [PASS] | Command | Return validated |
| 6. ProcessResults | [PASS] | Command | Artifacts extracted, linked |
| 7. Postflight | [PASS] | Command | **TODO.md/state.json updated, git commits created** |
| 8. ReturnSuccess | [PASS] | Command | Brief summary returned to orchestrator |

### 3.3 Preflight Procedures Bypassed

**Missing Preflight Actions**:

1. **Argument Parsing** (Stage 1):
   - Task number extraction
   - Optional prompt extraction
   - Flag parsing (--divide for /research)
   - Range parsing (105-107 for /implement)

2. **Task Validation** (Stage 1):
   - Task exists in TODO.md
   - Task not [COMPLETED] or [ABANDONED]
   - Language field present
   - Command-specific validations (plan exists for /revise, etc.)

3. **Status Update to In-Progress** (Stage 1):
   - TODO.md: [NOT STARTED] → [PLANNING]/[RESEARCHING]/[IMPLEMENTING]
   - state.json: status = "planning"/"researching"/"implementing"
   - Timestamp: **Started**: {date}

**Impact**: Tasks remain in initial state during execution, no in-progress tracking.

### 3.4 Postflight Procedures Bypassed

**Missing Postflight Actions** (Stage 7):

1. **status-sync-manager Delegation**:
   - Atomic updates across TODO.md, state.json, project state.json
   - Two-phase commit (prepare → commit or rollback)
   - Validation before commit
   - Rollback on failure

2. **TODO.md Updates**:
   - Status marker: [PLANNING] → [PLANNED], [RESEARCHING] → [RESEARCHED], etc.
   - Timestamp: **Completed**: {date}
   - Artifact links: Plan, Research, Implementation
   - Checkmark for [COMPLETED] tasks

3. **state.json Updates**:
   - Status field: "planning" → "planned"
   - Timestamps: completed = "{ISO8601}"
   - Artifacts array: [{type, path, summary}, ...]
   - Metadata: plan_metadata, plan_versions, phase_statuses

4. **project state.json Updates**:
   - Lazy creation on first artifact write
   - Status, phase, timestamps
   - Artifacts tracking

5. **Plan File Updates** (for /implement):
   - Phase statuses: [NOT STARTED] → [IN PROGRESS] → [COMPLETED]
   - Phase timestamps: Started, Completed

6. **Git Commits**:
   - Scope: Artifacts + TODO.md + state.json + plan (if exists)
   - Message: "task {number}: {action}"
   - Targeted commits per git-commits.md

**Impact**: 
- Artifacts created but not tracked in TODO.md/state.json
- No git history for workflow progress
- Inconsistent state across tracking files
- No atomic updates (partial failures corrupt state)

### 3.5 status-sync-manager Invocation Failure

**Expected Invocation** (command Stage 7):

```python
# After subagent returns successfully
status_sync_result = invoke_status_sync_manager(
    task_number=task_number,
    new_status="planned",  # or "researched", "completed", "revised"
    timestamp=current_timestamp(),
    session_id=session_id,
    validated_artifacts=subagent_return["artifacts"],
    plan_metadata=subagent_return.get("plan_metadata"),  # if /plan
    plan_version=plan_version,  # if /revise
    phase_statuses=subagent_return.get("phase_statuses"),  # if /implement
    plan_path=plan_path  # if applicable
)

# Validate status-sync-manager succeeded
if status_sync_result["status"] != "completed":
    # Rollback already happened in status-sync-manager
    return error_to_user(status_sync_result["errors"])
```

**Actual Invocation**: **NEVER HAPPENS** - orchestrator bypasses command Stage 7 entirely.

**Evidence**: Task 227 research shows global state.json missing task entries despite TODO.md showing [RESEARCHED] status. This proves status-sync-manager is not being invoked.

### 3.6 Git Commit Integration Failure

**Expected Git Commits** (command Stage 7):

| Command | Commit Scope | Message Format |
|---------|-------------|----------------|
| /research | Research artifacts + TODO.md + state.json | "task {number}: research completed" |
| /plan | Plan file + TODO.md + state.json | "task {number}: plan created" |
| /revise | New plan file + TODO.md + state.json | "task {number}: plan revised to v{version}" |
| /implement | Implementation files + TODO.md + state.json + plan | "task {number}: implementation completed" |

**Actual Git Commits**: **NONE** - commands never reach Stage 7 to create commits.

**Impact**: 
- No automatic git history for workflow progress
- Manual commits required (error-prone)
- Difficult to track when artifacts were created
- No atomic commits with status updates

---

## 4. Architectural Issues

### 4.1 Subagents Exposed as Primary Delegation Targets

**Current Architecture** (WRONG):

```
User → Orchestrator → Subagent (planner, researcher, task-executor)
```

**Problem**: Subagents are exposed as primary delegation targets, violating architectural layering.

**What Subagents Are**:
- Specialized workers that perform specific tasks
- Receive inputs with delegation context
- Execute task (may delegate to specialists)
- Create artifacts
- Return standardized format
- **Do NOT update TODO.md or state.json** (that's the command's job)

**What Subagents Are NOT**:
- Entry points for user workflows
- Responsible for status tracking
- Responsible for git commits
- Responsible for argument parsing
- Responsible for preflight/postflight procedures

### 4.2 Commands Bypassed as Workflow Orchestrators

**Expected Architecture** (CORRECT):

```
User → Orchestrator → Command → Subagent
```

**What Commands Are**:
- Complete workflow specifications with 8 stages
- Contain argument parsing logic
- Contain routing logic (which subagent to invoke)
- Contain preflight logic (validation, status updates)
- Contain postflight logic (status-sync-manager delegation, git commits)
- Return brief summaries to orchestrator (<100 tokens)

**What Commands Are NOT**:
- Just documentation files
- Passive specifications
- Optional layers

**Commands ARE the workflow orchestrators**. Orchestrator is the **routing layer**, not the **workflow execution layer**.

### 4.3 Correct Delegation Chain

**Current (Broken)**:
```
Orchestrator (depth 0) → Subagent (depth 1) → Specialist (depth 2)
```

**Corrected**:
```
Orchestrator (depth 0) → Command (depth 0) → Subagent (depth 1) → Specialist (depth 2)
```

**Rationale**: Orchestrator → Command is not counted as delegation depth because commands are part of the orchestrator's workflow execution layer, not separate agents. Delegation depth starts when commands invoke subagents.

### 4.4 Relationship to Tasks 227 and 228

**Task 227**: Fix systematic status-sync-manager TODO.md update failures

**Finding**: Task 227 assumes status-sync-manager is being invoked but failing. Research reveals status-sync-manager is **never invoked** because orchestrator bypasses commands.

**Resolution**: Task 229 (this task) must be completed FIRST. Once orchestrator routes to commands, command Stage 7 will invoke status-sync-manager, and then Task 227 can investigate any remaining update failures.

**Task 228**: Fix orchestrator routing to invoke commands instead of bypassing to subagents directly

**Finding**: Task 228 identified the exact same root cause as Task 229. These are duplicate tasks addressing the same architectural flaw.

**Resolution**: Task 229 is the comprehensive architectural review. Task 228 can be marked as duplicate or merged into Task 229.

---

## 5. Integration Patterns

### 5.1 How Orchestrator Should Invoke Commands

**Current (Broken)**:

```python
# Step 4: PrepareRouting
target_agent = "planner"  # WRONG - routes to subagent

# Step 7: RouteToAgent
result = task_tool(
    subagent_type=target_agent,  # WRONG - bypasses command
    prompt=construct_prompt(request, context),
    session_id=delegation_context["session_id"],
    ...
)
```

**Corrected**:

```python
# Step 4: PrepareRouting
target_command = "/plan"  # CORRECT - routes to command
arguments = "224"  # Task number

# Step 7: RouteToCommand (RENAMED)
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

**Key Changes**:
1. Route to **command** ("/plan") not **subagent** ("planner")
2. Load command file from .opencode/command/{command}.md
3. Substitute $ARGUMENTS with user-provided arguments
4. Execute command's 8-stage workflow
5. Command handles subagent invocation internally (Stage 4)

### 5.2 How Commands Should Invoke Subagents

**Commands Already Correct** (no changes needed):

```xml
<stage id="4" name="InvokeAgent">
  <action>Invoke target agent with delegation context</action>
  <process>
    1. Route to appropriate subagent (determined in Stage 2)
    2. Pass delegation context
    3. Pass task-specific parameters
    4. Set timeout from Stage 3
    5. Begin monitoring
  </process>
  <invocation>
    task_tool(
      subagent_type="planner",  # Determined in Stage 2
      prompt="Create plan for task {task_number}",
      session_id=delegation_context["session_id"],
      delegation_depth=1,  # Command → Subagent is depth 1
      delegation_path=["orchestrator", "plan", "planner"],
      timeout=1800
    )
  </invocation>
</stage>
```

**Commands handle**:
- Language extraction (Stage 2)
- Routing decision (Stage 2)
- Subagent invocation (Stage 4)
- Result validation (Stage 5)
- Postflight procedures (Stage 7)

### 5.3 Metadata Flow Through Delegation Chain

**Delegation Context** (passed from orchestrator to command):

```json
{
  "session_id": "sess_20251228_abc123",
  "delegation_depth": 0,
  "delegation_path": ["orchestrator"],
  "timeout": 1800,
  "caller": "orchestrator",
  "task_context": {
    "task_number": 224,
    "command": "/plan",
    "arguments": "224"
  }
}
```

**Command Updates Context** (passed to subagent):

```json
{
  "session_id": "sess_20251228_abc123",
  "delegation_depth": 1,
  "delegation_path": ["orchestrator", "plan", "planner"],
  "timeout": 1800,
  "caller": "plan",
  "task_context": {
    "task_number": 224,
    "description": "Configure OpenCode default agent",
    "language": "markdown",
    "research_inputs": [
      ".opencode/specs/224_.../reports/research-001.md"
    ]
  }
}
```

**Subagent Returns Metadata** (back to command):

```json
{
  "status": "completed",
  "summary": "Plan created for task 224...",
  "artifacts": [
    {
      "type": "plan",
      "path": ".opencode/specs/224_.../plans/implementation-001.md",
      "summary": "4-phase implementation plan"
    }
  ],
  "metadata": {
    "session_id": "sess_20251228_abc123",
    "duration_seconds": 450,
    "agent_type": "planner",
    "delegation_depth": 1,
    "delegation_path": ["orchestrator", "plan", "planner"],
    "plan_metadata": {
      "phase_count": 4,
      "estimated_hours": 12,
      "complexity": "medium"
    }
  },
  "errors": [],
  "next_steps": "Run /implement 224 to execute plan"
}
```

**Command Returns to Orchestrator**:

```json
{
  "status": "completed",
  "summary": "Plan created for task 224. 4 phases, 12 hours estimated.",
  "artifacts": [
    {
      "type": "plan",
      "path": ".opencode/specs/224_.../plans/implementation-001.md",
      "summary": "4-phase implementation plan"
    }
  ],
  "metadata": {
    "session_id": "sess_20251228_abc123",
    "duration_seconds": 480,
    "agent_type": "plan",
    "delegation_depth": 0,
    "delegation_path": ["orchestrator", "plan"]
  },
  "errors": [],
  "next_steps": "Run /implement 224 to execute plan"
}
```

### 5.4 Context Loading at the Right Layer

**Orchestrator Context** (~5,000 tokens):
```
@.opencode/context/core/standards/subagent-return-format.md
@.opencode/context/core/workflows/subagent-delegation-guide.md
@.opencode/context/core/standards/status-markers.md (for validation only)
```

**Command Context** (~10,000-12,000 tokens):
```
@.opencode/context/core/workflows/command-lifecycle.md
@.opencode/specs/TODO.md
@.opencode/specs/state.json
@.opencode/context/core/standards/status-markers.md
@.opencode/context/core/standards/subagent-return-format.md
@.opencode/context/core/workflows/subagent-delegation-guide.md
@.opencode/context/core/system/git-commits.md
@.opencode/context/project/{language}/ (filtered by context_level)
```

**Subagent Context** (~5,000-8,000 tokens):
```
@.opencode/context/core/standards/subagent-return-format.md (for validation)
Task-specific context from command
Domain knowledge for specialty
```

**Key Principle**: Load context at the layer that uses it. Don't load project-specific context in orchestrator if commands will load it anyway.

---

## 6. Recommendations

### 6.1 Refactoring Steps

**Phase 1: Orchestrator Routing Fix** (2-3 hours)

**Step 1.1**: Modify orchestrator.md Step 4 (PrepareRouting)

**Current** (lines 219-332):
```xml
<routing_logic>
  <plan_command>
    Target: planner (language-agnostic)
    Log: "Routing /plan (task ${task_number}) to planner"
  </plan_command>
</routing_logic>
```

**Change To**:
```xml
<routing_logic>
  <plan_command>
    Target: /plan command
    Arguments: {task_number} {optional_prompt}
    Log: "Routing user request to /plan command (task ${task_number})"
  </plan_command>
  
  <research_command>
    Target: /research command
    Arguments: {task_number} {optional_prompt}
    Log: "Routing user request to /research command (task ${task_number})"
  </research_command>
  
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
</routing_logic>
```

**Step 1.2**: Modify orchestrator.md Step 7 (RouteToAgent → RouteToCommand)

**Current** (lines 398-419):
```xml
<step_7 name="RouteToAgent">
  <action>Invoke target agent with delegation context</action>
  
  <invocation_pattern>
    result = task_tool(
        subagent_type=target_agent,
        prompt=construct_prompt(request, context),
        ...
    )
  </invocation_pattern>
</step_7>
```

**Change To**:
```xml
<step_7 name="RouteToCommand">
  <action>Invoke target command with arguments</action>
  
  <invocation_pattern>
    # Load command file
    command_file = load_command_file(target_command)
    
    # Substitute $ARGUMENTS in command file
    command_file = substitute_arguments(command_file, arguments)
    
    # Execute command workflow
    result = execute_command(
        command_file=command_file,
        session_id=delegation_context["session_id"],
        delegation_depth=0,
        delegation_path=["orchestrator"],
        timeout=delegation_context["timeout"]
    )
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
</step_7>
```

**Step 1.3**: Remove or simplify orchestrator.md Step 3 (CheckLanguage)

**Current** (lines 181-217):
```xml
<step_3 name="CheckLanguage">
  <action>Determine language for routing decisions</action>
  <process>
    1. Extract Language field from TODO.md using bash
    2. Validate extraction succeeded
    3. Log extracted language
    4. Store language for use in Stage 4
  </process>
</step_3>
```

**Change To**:
```xml
<step_3 name="PrepareCommandContext">
  <action>Prepare context for command invocation</action>
  <process>
    1. Extract task number from arguments (if applicable)
    2. Prepare command invocation context
    3. No language extraction (commands handle this)
  </process>
  <rationale>
    Language extraction belongs in command layer (Stage 2 of command-lifecycle.md).
    Commands know which language field to extract and how to route based on it.
    Orchestrator doesn't need this information - it just routes to the correct command.
  </rationale>
</step_3>
```

**Step 1.4**: Reduce orchestrator context loading

**Current** (lines 16-36):
```xml
<context_loading>
  <level_2 coverage="20%">
    Level 1 + Project-specific context based on language
    - lean: Load .opencode/context/project/lean4/
    - markdown: Load .opencode/context/project/repo/
  </level_2>
</context_loading>
```

**Change To**:
```xml
<context_loading>
  <level_1 coverage="100%">
    Minimal context for routing and delegation safety:
    - Common standards (return format, delegation guide, status markers)
    - Command routing map
    - Timeout configuration
  </level_1>
  
  <no_project_context>
    Project-specific context loaded by commands, not orchestrator.
    Commands specify context_level in frontmatter.
  </no_project_context>
</context_loading>
```

**Phase 2: Testing and Validation** (1-2 hours)

**Test 1**: /plan command
- Execute: `/plan 224`
- Verify: TODO.md updated to [PLANNED]
- Verify: state.json updated with plan_path, plan_metadata
- Verify: Git commit created
- Verify: Brief summary returned

**Test 2**: /research command (Lean)
- Execute: `/research 225` (Language: lean)
- Verify: Routes to lean-research-agent (not researcher)
- Verify: TODO.md updated to [RESEARCHED]
- Verify: state.json updated
- Verify: Git commit created

**Test 3**: /implement command (with plan)
- Execute: `/implement 226` (has plan)
- Verify: Routes to task-executor (not implementer)
- Verify: TODO.md updated to [COMPLETED] with checkmark
- Verify: state.json updated
- Verify: Plan phases updated
- Verify: Git commit created

**Test 4**: /revise command
- Execute: `/revise 227`
- Verify: TODO.md updated to [REVISED]
- Verify: state.json plan_versions array updated
- Verify: New plan version created
- Verify: Git commit created

**Phase 3: Documentation Update** (0.5-1 hour)

**Update Files**:
1. orchestrator.md - Reflect command routing pattern
2. ARCHITECTURE.md - Update delegation flow diagrams
3. command-lifecycle.md - Add orchestrator integration section
4. IMPLEMENTATION_STATUS.md - Mark task 229 completed

### 6.2 Expected Outcomes

**Outcome 1**: 60-70% reduction in orchestrator context window
- Before: ~21,000 tokens (duplication + bloat)
- After: ~5,000 tokens (core delegation only)
- Reduction: ~16,000 tokens (76%)

**Outcome 2**: 100% workflow completion
- Before: 0% of commands execute postflight Stage 7
- After: 100% of commands execute full 8-stage lifecycle
- Impact: All TODO.md/state.json updates occur

**Outcome 3**: Clear architectural layers
- Before: Orchestrator → Subagent (bypasses commands)
- After: Orchestrator → Command → Subagent (correct layering)
- Impact: Each layer has clear responsibilities

**Outcome 4**: Context loaded exactly where needed
- Before: Orchestrator loads project context, commands load it again
- After: Orchestrator loads core context, commands load project context
- Impact: No duplication, optimal context distribution

**Outcome 5**: All status updates via status-sync-manager
- Before: status-sync-manager never invoked
- After: status-sync-manager invoked by all commands in Stage 7
- Impact: Atomic updates, rollback on failure, consistent state

**Outcome 6**: Proper git commit integration
- Before: No automatic git commits
- After: Git commits created by all commands in Stage 7
- Impact: Full git history for workflow progress

**Outcome 7**: Resolves tasks 227 and 228
- Task 227: status-sync-manager will be invoked (can investigate any remaining failures)
- Task 228: Orchestrator routes to commands (architectural fix complete)

### 6.3 Implementation Complexity Estimate

**Complexity**: Medium

**Effort Breakdown**:

| Phase | Tasks | Effort | Priority |
|-------|-------|--------|----------|
| Phase 1: Orchestrator Routing Fix | 4 steps | 2-3 hours | CRITICAL |
| Phase 2: Testing and Validation | 4 tests | 1-2 hours | CRITICAL |
| Phase 3: Documentation Update | 4 files | 0.5-1 hour | HIGH |
| **Total** | | **3.5-6 hours** | |

**Risk Level**: Medium
- Breaking change to core routing logic
- Affects all workflow commands
- Requires careful testing
- Rollback plan needed

**Mitigation**:
- Test each command individually
- Verify with existing tasks (224, 225, 226, 227)
- Monitor TODO.md and state.json updates
- Check git commits created
- Rollback orchestrator.md if issues found

---

## 7. Conclusion

The orchestrator-command integration suffers from a critical architectural flaw where the orchestrator routes directly to subagents instead of to commands, bypassing the entire command lifecycle and causing:

1. **Context bloat**: 60-70% unnecessary context in orchestrator (~21,000 tokens)
2. **Workflow failure**: 100% of commands skip postflight Stage 7 (no TODO.md/state.json updates)
3. **Architecture violation**: Subagents exposed as primary delegation targets
4. **Missing features**: No status-sync-manager invocation, no git commits, no atomic updates

**Fix**: Modify orchestrator Step 4 and Step 7 to route to commands (/plan, /research, /implement, /revise) instead of subagents (planner, researcher, task-executor, implementer). Commands will execute their full 8-stage lifecycle including critical postflight procedures.

**Priority**: CRITICAL - This is a foundational architectural issue affecting all workflow commands and blocking tasks 227 and 228.

**Effort**: 3.5-6 hours (2-3 hours implementation, 1-2 hours testing, 0.5-1 hour documentation)

**Expected Outcomes**: 60-70% context reduction, 100% workflow completion, clear architectural layers, all status updates via status-sync-manager, proper git commit integration.

---

## References

### Analyzed Files

1. `.opencode/agent/orchestrator.md` (1,016 lines) - Current routing logic
2. `.opencode/command/research.md` (355 lines) - Research command workflow
3. `.opencode/command/plan.md` (330 lines) - Plan command workflow
4. `.opencode/command/implement.md` (439 lines) - Implement command workflow
5. `.opencode/command/revise.md` (309 lines) - Revise command workflow
6. `.opencode/command/review.md` (673 lines) - Review command workflow
7. `.opencode/context/core/workflows/command-lifecycle.md` (983 lines) - 8-stage pattern
8. `.opencode/context/core/workflows/subagent-delegation-guide.md` (649 lines) - Delegation safety
9. `.opencode/context/core/standards/subagent-return-format.md` (356 lines) - Return format

### Related Tasks

- **Task 227**: Fix systematic status-sync-manager TODO.md update failures
  - Finding: status-sync-manager never invoked (orchestrator bypasses commands)
  - Resolution: Fix task 229 first, then investigate remaining failures
  
- **Task 228**: Fix orchestrator routing to invoke commands instead of bypassing to subagents directly
  - Finding: Duplicate of task 229 (same root cause)
  - Resolution: Merge into task 229 or mark as duplicate

### Evidence

1. **Orchestrator.md Step 4** (lines 219-332): Routes to subagents, not commands
2. **Orchestrator.md Step 7** (lines 398-419): Invokes subagents directly
3. **Command files**: All specify 8-stage workflow with postflight Stage 7
4. **Task 227 research**: Global state.json missing task entries (status-sync-manager not invoked)
5. **Task 228 research**: Identified same architectural flaw
