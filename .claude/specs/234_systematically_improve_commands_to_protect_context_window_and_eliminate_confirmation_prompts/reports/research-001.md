# Research Report: Command Context Window Protection and Confirmation Prompt Elimination

**Task**: 234  
**Created**: 2025-12-28  
**Researcher**: researcher  
**Session**: sess_20251229_r234a1

---

## Executive Summary

This research systematically analyzes all workflow commands to identify confirmation prompts, context loading patterns, and routing logic inefficiencies. The analysis reveals that **all four primary workflow commands (/research, /plan, /implement, /revise) already follow immediate delegation patterns with NO user confirmation prompts**. However, the /todo command contains a legitimate confirmation prompt for archiving >5 tasks. The primary issue is **context loading location** - commands load extensive context in their frontmatter (lines 11-18) which is loaded by the orchestrator during routing, consuming 60-70% of the context window before delegation occurs.

**Key Findings**:
1. **No confirmation prompts in workflow commands** - All commands delegate immediately
2. **Context loaded too early** - 7-8 context files loaded in command frontmatter (orchestrator stage)
3. **Routing needs only 3 pieces of info** - task_number, language, plan_existence
4. **Safety preserved** - Validation checks occur without prompting user
5. **Lightweight routing pattern exists** - Extract task number, read Language field via bash grep, check plan existence, route to agent

**Impact**: Commands are already designed correctly for immediate delegation. The fix is to **move context loading from command frontmatter to command execution stage** (after orchestrator routing completes).

---

## Research Question 1: Which commands currently prompt for user confirmation instead of immediate delegation?

### Analysis Methodology

Searched all command files for confirmation patterns:
- "Would you like"
- "Do you want"
- "Choose"
- "Select"
- "Confirm"
- "Proceed"

### Findings

**Workflow Commands (NO confirmation prompts)**:

1. **/research** (641 lines)
   - **No confirmation prompts found**
   - Immediate delegation pattern: Stage 1 (Preflight) → Stage 2 (CheckLanguage) → Stage 3 (PrepareDelegation) → Stage 4 (InvokeAgent)
   - Routing logic (lines 126-161): Extract language → Route to lean-research-agent (lean) or researcher (general)
   - No user interaction required

2. **/plan** (616 lines)
   - **No confirmation prompts found**
   - Immediate delegation pattern: Stage 1 (Preflight) → Stage 2 (HarvestResearch) → Stage 3 (PrepareDelegation) → Stage 4 (InvokeAgent)
   - Routing logic: Always routes to planner (language-agnostic)
   - Warning if plan exists (line 105): "Warn if plan already exists (suggest /revise instead)" - but this is a warning, NOT a confirmation prompt

3. **/implement** (766 lines)
   - **No confirmation prompts found**
   - Immediate delegation pattern: Stage 1 (Preflight) → Stage 2 (DetermineRouting) → Stage 3 (PrepareDelegation) → Stage 4 (InvokeAgent)
   - Routing logic (lines 155-212): Extract language + check plan existence → Route to lean-implementation-agent, task-executor, or implementer
   - No user interaction required

4. **/revise** (610 lines)
   - **No confirmation prompts found**
   - Immediate delegation pattern: Stage 1 (Preflight) → Stage 2 (DeterminePlanVersion) → Stage 3 (PrepareDelegation) → Stage 4 (InvokeAgent)
   - Routing logic: Always routes to planner with revision context
   - Error if no plan exists (line 92): "Error: Task {task_number} has no plan. Use /plan instead." - but this is an error, NOT a confirmation prompt

**Non-Workflow Commands**:

5. **/todo** (540 lines)
   - **LEGITIMATE confirmation prompt found** (lines 68-91)
   - Stage 2 "ConfirmArchival": Confirms archival with user if >5 tasks
   - Threshold: 5 tasks
   - If archiving >5 tasks: Display list, request confirmation, abort if declined
   - If archiving ≤5 tasks: Proceed automatically
   - **Justification**: This is a LEGITIMATE safety prompt for bulk operations. Archiving is destructive (moves directories), so user confirmation for large batches is appropriate.

6. **/task** (298 lines)
   - **No confirmation prompts found**
   - Direct execution (no delegation)

7. **/review** (672 lines)
   - **No confirmation prompts found**
   - Immediate delegation to reviewer

8. **/errors** (398 lines)
   - **No confirmation prompts found**
   - Immediate delegation to error-diagnostics-agent

### Conclusion for Question 1

**All four primary workflow commands (/research, /plan, /implement, /revise) already follow immediate delegation patterns with NO user confirmation prompts.** The only confirmation prompt exists in /todo for archiving >5 tasks, which is a legitimate safety mechanism for destructive bulk operations.

The task description mentions "/implement command consumed 67% of tokens with the primary agent and then asked 'Would you like me to: 1. Delegate to /implement 210...'" - **this prompt does NOT exist in the current implement.md specification**. This suggests the issue was either:
1. Fixed in a previous iteration
2. Caused by Claude deviating from the specification
3. Caused by context loading bloat making Claude think it needed to prompt

---

## Research Question 2: Where is context being loaded too early (orchestrator vs command layer)?

### Analysis Methodology

Examined "Context Loaded:" sections in all command files and orchestrator.md to identify when and where context files are loaded.

### Findings

**Orchestrator Context Loading** (orchestrator.md lines 32-36):

```
<context_loaded>
  @.opencode/context/core/standards/subagent-return-format.md
  @.opencode/context/core/workflows/subagent-delegation-guide.md
  @.opencode/context/core/standards/status-markers.md
</context_loaded>
```

**Orchestrator loads only 3 files** - this is appropriate for routing decisions.

**Command Context Loading** (ALL commands load 7-8 files in frontmatter):

1. **/research** (lines 11-18):
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
**7 files loaded**

2. **/plan** (lines 11-18):
```
Context Loaded:
@.opencode/context/core/workflows/command-lifecycle.md
@.opencode/specs/.opencode/specs/TODO.md  # NOTE: Duplicate path error
@.opencode/specs/state.json
@.opencode/context/core/standards/status-markers.md
@.opencode/context/core/standards/subagent-return-format.md
@.opencode/context/core/workflows/subagent-delegation-guide.md
@.opencode/context/core/system/git-commits.md
```
**7 files loaded** (with path error)

3. **/implement** (lines 11-18):
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
**7 files loaded**

4. **/revise** (lines 11-18):
```
Context Loaded:
@.opencode/context/core/workflows/command-lifecycle.md
@.opencode/specs/.opencode/specs/TODO.md  # NOTE: Duplicate path error
@.opencode/specs/state.json
@.opencode/context/core/standards/status-markers.md
@.opencode/context/core/standards/subagent-return-format.md
@.opencode/context/core/workflows/subagent-delegation-guide.md
@.opencode/context/core/system/git-commits.md
```
**7 files loaded** (with path error)

5. **/todo** (lines 9-16):
```
Context Loaded:
@.opencode/context/core/workflows/command-lifecycle.md
@.opencode/specs/TODO.md
@.opencode/specs/state.json
@.opencode/specs/archive/state.json
@.opencode/context/core/standards/status-markers.md
@.opencode/context/core/standards/subagent-return-format.md
@.opencode/context/core/system/git-commits.md
```
**7 files loaded**

### Context Loading Timeline

**Current (Problematic) Flow**:

1. **User invokes command**: `/implement 210`
2. **Orchestrator loads command file**: `.opencode/command/implement.md`
3. **Command frontmatter loads 7 files** (lines 11-18):
   - command-lifecycle.md (~1067 lines)
   - TODO.md (~2000+ lines)
   - state.json (~500 lines)
   - status-markers.md (~300 lines)
   - subagent-return-format.md (~400 lines)
   - subagent-delegation-guide.md (~500 lines)
   - git-commits.md (~300 lines)
   - **Total: ~5000+ lines loaded in orchestrator context**
4. **Orchestrator executes command Stage 1-3** (routing logic)
5. **Orchestrator delegates to subagent** (Stage 4)
6. **Subagent loads its own context** and executes

**Problem**: Steps 3-4 load massive context (5000+ lines) in the orchestrator just to make a routing decision that only needs 3 pieces of information (task_number, language, plan_existence).

**Desired (Efficient) Flow**:

1. **User invokes command**: `/implement 210`
2. **Orchestrator loads minimal routing context**:
   - Extract task_number from arguments
   - Read Language field from TODO.md (bash grep)
   - Check plan existence (bash grep for "Plan:" link)
   - **Total: ~50 lines read, 3 bash commands**
3. **Orchestrator routes to appropriate subagent**
4. **Command loads full context AFTER routing** (in subagent or command execution stage)
5. **Subagent executes with full context**

### Conclusion for Question 2

**Context is loaded far too early** - all 7-8 context files are loaded in command frontmatter (lines 11-18), which is loaded by the orchestrator during routing. This consumes 60-70% of the orchestrator's context window before delegation occurs.

**Root Cause**: The "Context Loaded:" section in command frontmatter is interpreted by OpenCode as "load these files immediately when this command file is loaded", which happens during orchestrator routing (Step 2 of orchestrator flow).

**Fix**: Move context loading from frontmatter to command execution stage. The orchestrator should only load the command file structure (argument parsing, routing logic) without loading the referenced context files. Context files should be loaded AFTER delegation, either by the subagent or by the command execution layer.

---

## Research Question 3: What routing information is truly needed vs nice-to-have for orchestrator decisions?

### Analysis Methodology

Examined routing logic in all commands (Stage 2 "CheckLanguage" or "DetermineRouting") to identify what information is actually used to make routing decisions.

### Findings

**Routing Decision Inputs** (by command):

1. **/research** (lines 126-161):
   - **Required**: task_number, language
   - **Routing logic**: `IF language == "lean" → lean-research-agent ELSE → researcher`
   - **Information sources**:
     - task_number: Extracted from $ARGUMENTS (Stage 1)
     - language: Extracted via bash grep from TODO.md (Stage 2, line 134-138)
   - **Nice-to-have**: None
   - **Unused context**: command-lifecycle.md, state.json, status-markers.md, subagent-return-format.md, subagent-delegation-guide.md, git-commits.md

2. **/plan** (lines 114-132):
   - **Required**: task_number
   - **Routing logic**: Always routes to planner (language-agnostic)
   - **Information sources**:
     - task_number: Extracted from $ARGUMENTS (Stage 1)
   - **Nice-to-have**: research_inputs (harvested from TODO.md in Stage 2, lines 114-132)
   - **Unused context**: command-lifecycle.md, state.json, status-markers.md, subagent-return-format.md, subagent-delegation-guide.md, git-commits.md

3. **/implement** (lines 155-212):
   - **Required**: task_number, language, has_plan
   - **Routing logic**:
     ```
     IF language == "lean" AND has_plan == true → lean-implementation-agent (phased)
     ELSE IF language == "lean" AND has_plan == false → lean-implementation-agent (simple)
     ELSE IF language != "lean" AND has_plan == true → task-executor (phased)
     ELSE IF language != "lean" AND has_plan == false → implementer (direct)
     ```
   - **Information sources**:
     - task_number: Extracted from $ARGUMENTS (Stage 1)
     - language: Extracted via bash grep from TODO.md (Stage 2, line 163-168)
     - has_plan: Checked via bash grep for "Plan:" link in TODO.md (Stage 2, line 170-172)
   - **Nice-to-have**: None
   - **Unused context**: command-lifecycle.md, state.json, status-markers.md, subagent-return-format.md, subagent-delegation-guide.md, git-commits.md

4. **/revise** (lines 118-131):
   - **Required**: task_number, existing_plan_path, new_version
   - **Routing logic**: Always routes to planner with revision context
   - **Information sources**:
     - task_number: Extracted from $ARGUMENTS (Stage 1)
     - existing_plan_path: Extracted from TODO.md (Stage 2, line 120)
     - new_version: Calculated by parsing current plan version (Stage 2, line 122)
   - **Nice-to-have**: None
   - **Unused context**: command-lifecycle.md, state.json, status-markers.md, subagent-return-format.md, subagent-delegation-guide.md, git-commits.md

### Routing Information Matrix

| Command | Required Info | Source | Extraction Method | Nice-to-Have | Unused Context Files |
|---------|--------------|--------|-------------------|--------------|---------------------|
| /research | task_number, language | $ARGUMENTS, TODO.md | Parse args, bash grep | None | 6 files (lifecycle, state, status, return, delegation, git) |
| /plan | task_number | $ARGUMENTS | Parse args | research_inputs | 6 files (lifecycle, state, status, return, delegation, git) |
| /implement | task_number, language, has_plan | $ARGUMENTS, TODO.md | Parse args, bash grep (2x) | None | 6 files (lifecycle, state, status, return, delegation, git) |
| /revise | task_number, existing_plan_path, new_version | $ARGUMENTS, TODO.md | Parse args, bash grep, parse version | None | 6 files (lifecycle, state, status, return, delegation, git) |

### Conclusion for Question 3

**Routing decisions require only 3-4 pieces of information**:
1. **task_number** (from $ARGUMENTS)
2. **language** (from TODO.md via bash grep)
3. **has_plan** (from TODO.md via bash grep for "Plan:" link) - only for /implement
4. **existing_plan_path** (from TODO.md via bash grep) - only for /revise

**All other context files are unused during routing**:
- command-lifecycle.md (1067 lines) - Used for execution, NOT routing
- state.json (500 lines) - Used for status updates, NOT routing
- status-markers.md (300 lines) - Used for status transitions, NOT routing
- subagent-return-format.md (400 lines) - Used for validation, NOT routing
- subagent-delegation-guide.md (500 lines) - Used for delegation mechanics, NOT routing
- git-commits.md (300 lines) - Used for git operations, NOT routing

**Total wasted context during routing**: ~3000+ lines loaded but unused for routing decisions.

**Lightweight routing pattern**:
```
1. Parse task_number from $ARGUMENTS
2. Bash grep TODO.md for Language field (1 line)
3. Bash grep TODO.md for "Plan:" link (1 line) - if needed
4. Route to appropriate agent based on 2-3 values
5. Delegate with minimal context
```

**Estimated context usage**:
- Current: 5000+ lines (60-70% of orchestrator context)
- Lightweight: 50-100 lines (<10% of orchestrator context)
- **Savings**: 90% reduction in routing context

---

## Research Question 4: How can we ensure immediate delegation while preserving safety and correctness?

### Analysis Methodology

Examined validation logic in all commands to identify safety checks that occur before delegation. Analyzed whether these checks require user confirmation or can be automated.

### Findings

**Safety Checks by Command** (all occur in Stage 1 "Preflight"):

1. **/research** (lines 108-124):
   - Task number exists in TODO.md
   - Task not [COMPLETED] or [ABANDONED]
   - Language field present (default to "general" if missing)
   - Check for --divide flag (optional feature)
   - **User confirmation required**: NO
   - **Automated validation**: YES - All checks are automated, errors abort with clear message

2. **/plan** (lines 97-112):
   - Task number exists in TODO.md
   - Task not [COMPLETED] or [ABANDONED]
   - **Warn if plan already exists** (line 105): "Warn if plan already exists (suggest /revise instead)"
   - **User confirmation required**: NO - This is a warning, not a blocking prompt
   - **Automated validation**: YES - All checks are automated, warning suggests alternative command

3. **/implement** (lines 125-153):
   - Task number(s) exist in TODO.md (supports ranges like 105-107)
   - Tasks not [COMPLETED] or [ABANDONED]
   - If range: all tasks in range must be valid
   - Language field must be present
   - Check for plan existence and phase statuses
   - **User confirmation required**: NO
   - **Automated validation**: YES - All checks are automated, errors abort with clear message

4. **/revise** (lines 99-109):
   - Task number exists in TODO.md
   - **Task must have existing plan link** (line 106)
   - **Plan file must exist on disk** (line 107)
   - Calculate next plan version number
   - **User confirmation required**: NO
   - **Automated validation**: YES - All checks are automated, error if no plan exists (suggests /plan instead)

### Safety Patterns

**Pattern 1: Validation Without Confirmation**

All commands use this pattern:
```
1. Check preconditions (task exists, not completed, etc.)
2. If validation fails:
   a. Log error with details
   b. Return error to user with clear message
   c. Suggest corrective action
   d. Abort command
3. If validation passes:
   a. Proceed to delegation immediately
   b. No user confirmation required
```

**Example** (/implement lines 108-119):
```xml
<error_handling>
  If task_number missing:
    Return: "Error: Task number required. Usage: /implement TASK_NUMBER [PROMPT]"
  If task_number not integer or range:
    Return: "Error: Task must be integer or range (N-M). Got: {input}"
  If task not found in .opencode/specs/TODO.md:
    Return: "Error: Task {task_number} not found in .opencode/specs/TODO.md"
  If range invalid (start >= end):
    Return: "Error: Invalid range {start}-{end}. Start must be less than end."
  If some tasks in range missing:
    Return: "Warning: Tasks {missing_list} not found. Continuing with {found_list}"
</error_handling>
```

**Pattern 2: Warnings Without Blocking**

/plan uses this pattern (line 105):
```xml
<validation>
  - Task number must exist in .opencode/specs/TODO.md
  - Task must not be [COMPLETED] or [ABANDONED]
  - Warn if plan already exists (suggest /revise instead)
</validation>
```

This is a **warning**, not a blocking prompt. The command suggests an alternative but doesn't require user confirmation.

**Pattern 3: Legitimate Confirmation for Destructive Operations**

/todo uses this pattern (lines 68-91):
```xml
<stage id="2" name="ConfirmArchival">
  <action>Confirm archival with user if threshold exceeded</action>
  <process>
    1. Count tasks to archive
    2. If count > 5:
       a. Display list of tasks to archive
       b. Request user confirmation
       c. Wait for confirmation (yes/no)
       d. Abort if user declines
    3. If count <= 5:
       a. Proceed without confirmation
  </process>
</stage>
```

This is **legitimate** because:
- Archival is destructive (moves directories)
- Bulk operations (>5 tasks) have higher risk
- User should review list before proceeding
- Small operations (≤5 tasks) proceed automatically

### Safety Mechanisms That Don't Require Confirmation

1. **Validation Checks** (automated):
   - Task existence verification
   - Status verification (not completed/abandoned)
   - Language field extraction with fallback
   - Plan existence verification
   - Range validation

2. **Error Handling** (automated):
   - Clear error messages
   - Corrective action suggestions
   - Graceful degradation (e.g., language defaults to "general")
   - Partial success handling (e.g., some tasks in range missing)

3. **Warnings** (non-blocking):
   - Plan already exists (suggest /revise)
   - Tool unavailability (proceed with degraded mode)
   - Git commit failures (log error, continue)

4. **Atomic Operations** (safety via status-sync-manager):
   - Two-phase commit for status updates
   - Rollback on failure
   - Validation before commit
   - No partial state corruption

### Conclusion for Question 4

**Immediate delegation can be ensured while preserving safety through automated validation checks, clear error messages, and atomic operations.** User confirmation is NOT required for safety in workflow commands because:

1. **Validation is automated** - All precondition checks can be performed without user input
2. **Errors are clear** - Failed validations return actionable error messages
3. **Operations are atomic** - Status updates use two-phase commit with rollback
4. **Warnings don't block** - Suggestions (like "use /revise instead") are informational, not blocking
5. **Destructive operations have thresholds** - /todo only prompts for >5 tasks, small batches proceed automatically

**Safety is preserved by**:
- Validating inputs before delegation
- Using atomic operations for state changes
- Providing clear error messages with corrective actions
- Implementing graceful degradation for tool unavailability
- Logging all errors for debugging

**User confirmation should only be required for**:
- Destructive bulk operations (>threshold)
- Ambiguous user intent (e.g., multiple valid interpretations)
- Operations requiring external approval (e.g., production deployments)

None of the workflow commands (/research, /plan, /implement, /revise) fall into these categories, so immediate delegation is safe and correct.

---

## Research Question 5: What are the patterns for lightweight routing vs full workflow execution?

### Analysis Methodology

Analyzed orchestrator.md and command files to identify the distinction between routing logic (orchestrator) and workflow execution logic (command/subagent).

### Findings

**Orchestrator Routing Pattern** (orchestrator.md lines 149-351):

**Step 1: AnalyzeRequest** (lines 153-180):
```
1. Extract command type (task, research, plan, implement, etc.)
2. Load command file from .opencode/command/{command}.md
3. Command file contains $ARGUMENTS which OpenCode substitutes with actual user arguments
4. Read argument_parsing section from command file for validation rules
5. Workflow Stage 1 in command file will parse and validate $ARGUMENTS
6. If command has no arguments, proceed directly to workflow execution
```

**Step 3: CheckLanguage** (lines 200-236):
```
1. If task number present: Read task from .opencode/specs/TODO.md using explicit bash command:
   grep -A 20 "^### ${task_number}\." .opencode/specs/TODO.md | grep "Language" | sed 's/\*\*Language\*\*: //'
2. Validate extraction succeeded (non-empty result)
3. If extraction fails or no language specified: default to "general" and log warning
4. Log extracted language: "Task ${task_number} language: ${language}"
5. Store language for use in Stage 4
```

**Step 4: PrepareRouting** (lines 238-351):
```
Routing logic by command:

/research:
  IF language == "lean":
    agent = "lean-research-agent"
  ELSE:
    agent = "researcher"

/plan:
  agent = "planner" (language-agnostic)

/implement:
  Check for plan existence in .opencode/specs/TODO.md (look for "Plan:" link)
  
  IF language == "lean" AND has_plan == true:
    agent = "lean-implementation-agent", mode = "phased"
  ELSE IF language == "lean" AND has_plan == false:
    agent = "lean-implementation-agent", mode = "simple"
  ELSE IF language != "lean" AND has_plan == true:
    agent = "task-executor", mode = "phased"
  ELSE IF language != "lean" AND has_plan == false:
    agent = "implementer", mode = "direct"

/revise:
  agent = "planner" (with revision context)
```

**Routing Validation** (lines 322-331):
```
After determining agent, MUST validate:
- For /research with language=="lean": agent MUST be "lean-research-agent"
- For /research with language!="lean": agent MUST be "researcher"
- For /implement with language=="lean": agent MUST be "lean-implementation-agent"
- For /implement with language!="lean" and has_plan: agent MUST be "task-executor"
- For /implement with language!="lean" and no plan: agent MUST be "implementer"
- If validation fails: ABORT with error
```

**Command Workflow Execution Pattern** (command-lifecycle.md lines 40-527):

Commands follow 8-stage pattern:
1. **Preflight** - Parse arguments, validate task, update status
2. **CheckLanguage/DetermineRouting** - Extract language, determine agent
3. **PrepareDelegation** - Prepare delegation context
4. **InvokeAgent** - Delegate to subagent
5. **ReceiveResults** - Validate agent return
6. **ProcessResults** - Extract artifacts and summary
7. **Postflight** - Update status, link artifacts, create git commit
8. **ReturnSuccess** - Return brief summary to user

**Stages 1-3 are routing** (lightweight, minimal context)
**Stages 4-8 are execution** (full context, actual work)

### Lightweight Routing Pattern

**Characteristics**:
- Minimal context loading (orchestrator's 3 files only)
- Bash-based information extraction (grep, sed)
- Simple conditional logic (IF/ELSE)
- No file modifications
- No artifact creation
- Fast execution (<1 second)

**Example** (/implement routing):
```bash
# Extract task number from arguments
task_number=$(echo "$ARGUMENTS" | awk '{print $1}')

# Extract language from TODO.md
language=$(grep -A 20 "^### ${task_number}\." .opencode/specs/TODO.md | grep "Language" | sed 's/\*\*Language\*\*: //')

# Check plan existence
has_plan=$(grep -A 20 "^### ${task_number}\." .opencode/specs/TODO.md | grep -q "Plan:" && echo "true" || echo "false")

# Route based on language and plan
if [ "$language" = "lean" ] && [ "$has_plan" = "true" ]; then
  agent="lean-implementation-agent"
  mode="phased"
elif [ "$language" = "lean" ] && [ "$has_plan" = "false" ]; then
  agent="lean-implementation-agent"
  mode="simple"
elif [ "$language" != "lean" ] && [ "$has_plan" = "true" ]; then
  agent="task-executor"
  mode="phased"
else
  agent="implementer"
  mode="direct"
fi

# Delegate to agent
delegate_to_agent "$agent" "$task_number" "$language" "$mode"
```

**Context usage**: ~50-100 lines read (task entry from TODO.md)

### Full Workflow Execution Pattern

**Characteristics**:
- Full context loading (command's 7 files + subagent's context)
- Complex validation logic
- File modifications (status updates, artifact creation)
- Artifact creation and linking
- Git commits
- Status synchronization
- Longer execution (seconds to minutes)

**Example** (/implement execution in lean-implementation-agent):
```
1. Load Lean context from .opencode/context/project/lean4/
2. Read task requirements from TODO.md or plan file
3. Implement Lean code (theorems, proofs, tactics)
4. Check compilation using lean-lsp-mcp tools (iterative, max 5 iterations)
5. Write final Lean files and implementation summary
6. Return standardized result with artifacts
```

**Context usage**: ~5000+ lines loaded (command context + Lean domain context)

### Pattern Comparison

| Aspect | Lightweight Routing | Full Workflow Execution |
|--------|-------------------|------------------------|
| **Stage** | Orchestrator Steps 1-4 | Command Stages 4-8 |
| **Context** | 3 files (~1000 lines) | 7+ files (~5000+ lines) |
| **Operations** | Read-only (grep, parse) | Read-write (create, modify, commit) |
| **Execution Time** | <1 second | Seconds to minutes |
| **Delegation** | Determines target agent | Performs actual work |
| **Validation** | Precondition checks | Artifact validation |
| **Artifacts** | None | Created and linked |
| **Status Updates** | None | Atomic updates via status-sync-manager |
| **Git Operations** | None | Commits created |
| **Error Handling** | Abort with error message | Retry, partial success, rollback |

### Conclusion for Question 5

**Lightweight routing pattern**:
1. Load minimal context (orchestrator's 3 files)
2. Extract routing information via bash (task_number, language, has_plan)
3. Apply simple conditional logic to determine target agent
4. Delegate to agent with minimal context
5. **Total context: <10% of orchestrator budget**

**Full workflow execution pattern**:
1. Load full context (command's 7 files + subagent's domain context)
2. Execute complex validation and processing logic
3. Create artifacts and update status
4. Perform git operations
5. Return standardized results
6. **Total context: >90% of agent budget**

**Key Insight**: The orchestrator should ONLY perform routing (lightweight pattern). All workflow execution (full pattern) should occur in the command/subagent layer AFTER delegation. This ensures the orchestrator's context budget is preserved for routing decisions, not consumed by workflow execution details.

**Current Problem**: Commands load full context in frontmatter (lines 11-18), which is loaded during orchestrator routing (Step 2). This violates the separation between routing and execution.

**Fix**: Move context loading from command frontmatter to command execution stage (after delegation). The orchestrator loads only the command structure (argument parsing, routing logic) without loading referenced context files.

---

## Specific Examples of Problematic Patterns

### Example 1: /implement Context Loading

**Current** (implement.md lines 11-18):
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

**Problem**: All 7 files loaded during orchestrator routing (Step 2), consuming ~5000 lines of context.

**Used for routing**: NONE - Routing only needs task_number, language, has_plan

**Used for execution**: ALL - All 7 files are used in Stages 4-8 (execution)

**Fix**: Move context loading to Stage 4 (after delegation):
```
Context Loaded (Routing Stage):
# None - orchestrator loads only command structure

Context Loaded (Execution Stage):
@.opencode/context/core/workflows/command-lifecycle.md
@.opencode/specs/TODO.md
@.opencode/specs/state.json
@.opencode/context/core/standards/status-markers.md
@.opencode/context/core/standards/subagent-return-format.md
@.opencode/context/core/workflows/subagent-delegation-guide.md
@.opencode/context/core/system/git-commits.md
```

### Example 2: /plan Duplicate Path Error

**Current** (plan.md line 13):
```
@.opencode/specs/.opencode/specs/TODO.md
```

**Problem**: Duplicate path prefix (`.opencode/specs/.opencode/specs/`) - likely a copy-paste error

**Fix**: Correct path to:
```
@.opencode/specs/TODO.md
```

### Example 3: Orchestrator Context Loading

**Current** (orchestrator.md lines 32-36):
```
<context_loaded>
  @.opencode/context/core/standards/subagent-return-format.md
  @.opencode/context/core/workflows/subagent-delegation-guide.md
  @.opencode/context/core/standards/status-markers.md
</context_loaded>
```

**Analysis**: This is CORRECT - orchestrator loads only 3 files needed for routing and delegation management.

**No changes needed** for orchestrator context loading.

---

## Recommendations

### Recommendation 1: Move Context Loading from Command Frontmatter to Execution Stage

**Priority**: CRITICAL  
**Effort**: 2-3 hours  
**Impact**: 90% reduction in orchestrator routing context usage

**Changes Required**:

1. **Remove "Context Loaded:" from command frontmatter** (lines 11-18 in all commands)
2. **Add context loading to Stage 4 (InvokeAgent)** or delegate to subagent
3. **Update command-lifecycle.md** to document context loading stage

**Implementation**:

For each command (/research, /plan, /implement, /revise):

**Before** (frontmatter):
```markdown
---
name: implement
agent: orchestrator
description: "Execute implementation with resume support and [COMPLETED] status"
context_level: 2
language: varies
---

**Task Input (required):** $ARGUMENTS

Context Loaded:
@.opencode/context/core/workflows/command-lifecycle.md
@.opencode/specs/TODO.md
@.opencode/specs/state.json
@.opencode/context/core/standards/status-markers.md
@.opencode/context/core/standards/subagent-return-format.md
@.opencode/context/core/workflows/subagent-delegation-guide.md
@.opencode/context/core/system/git-commits.md
```

**After** (frontmatter):
```markdown
---
name: implement
agent: orchestrator
description: "Execute implementation with resume support and [COMPLETED] status"
context_level: 2
language: varies
---

**Task Input (required):** $ARGUMENTS

# Context loaded in Stage 4 (after routing)
```

**After** (Stage 4 in command workflow):
```xml
<stage id="4" name="InvokeAgent">
  <action>Load full context and delegate to subagent</action>
  <context_loading>
    Load context files for execution:
    - .opencode/context/core/workflows/command-lifecycle.md
    - .opencode/specs/TODO.md
    - .opencode/specs/state.json
    - .opencode/context/core/standards/status-markers.md
    - .opencode/context/core/standards/subagent-return-format.md
    - .opencode/context/core/workflows/subagent-delegation-guide.md
    - .opencode/context/core/system/git-commits.md
  </context_loading>
  <delegation>
    Invoke target agent with full context and delegation parameters
  </delegation>
</stage>
```

**Verification**:
- Orchestrator routing context usage: <10% (target achieved)
- Command execution context usage: >90% (appropriate)
- All commands still function correctly
- No regression in safety or correctness

### Recommendation 2: Fix Duplicate Path Errors in /plan and /revise

**Priority**: HIGH  
**Effort**: 5 minutes  
**Impact**: Prevents potential file loading errors

**Changes Required**:

1. **plan.md line 13**: Change `@.opencode/specs/.opencode/specs/TODO.md` to `@.opencode/specs/TODO.md`
2. **revise.md line 13**: Change `@.opencode/specs/.opencode/specs/TODO.md` to `@.opencode/specs/TODO.md`

### Recommendation 3: Document Lightweight Routing Pattern

**Priority**: MEDIUM  
**Effort**: 1 hour  
**Impact**: Ensures future commands follow efficient routing pattern

**Changes Required**:

1. **Create new document**: `.opencode/context/common/patterns/lightweight-routing-pattern.md`
2. **Document pattern**:
   - Routing vs execution separation
   - Minimal context loading for routing
   - Bash-based information extraction
   - Simple conditional logic
   - Delegation with minimal context
3. **Reference from orchestrator.md** and command-lifecycle.md

**Content Outline**:
```markdown
# Lightweight Routing Pattern

## Purpose
Minimize orchestrator context usage during routing decisions

## Pattern
1. Extract routing information via bash (task_number, language, has_plan)
2. Apply simple conditional logic
3. Delegate to agent
4. Load full context AFTER delegation

## Context Budget
- Routing: <10% of orchestrator context
- Execution: >90% of agent context

## Examples
[Include examples from this research]
```

### Recommendation 4: Preserve /todo Confirmation Prompt

**Priority**: LOW  
**Effort**: 0 hours (no changes)  
**Impact**: Maintains safety for destructive bulk operations

**Justification**:

The /todo command's confirmation prompt (lines 68-91) is LEGITIMATE and should be preserved:
- Archival is destructive (moves directories)
- Bulk operations (>5 tasks) have higher risk
- User should review list before proceeding
- Small operations (≤5 tasks) proceed automatically

**No changes required** for /todo confirmation logic.

### Recommendation 5: Add Orchestrator Stage 7 Validation Checkpoint

**Priority**: MEDIUM  
**Effort**: 2-3 hours  
**Impact**: Prevents commands from returning without completing status updates

**Background**: Task 231 identified systematic Stage 7 (Postflight) execution failures where commands would skip or incompletely execute Stage 7, resulting in successful artifact creation but incomplete TODO.md/state.json updates.

**Changes Required**:

1. **Add stage tracking to orchestrator delegation registry** (orchestrator.md lines 95-146):
```javascript
{
  "sess_20251226_abc123": {
    "session_id": "sess_20251226_abc123",
    "command": "plan",
    "is_command": true,
    "command_stages": {
      "current_stage": 7,
      "stages_completed": [1, 2, 3, 4, 5, 6],
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

2. **Add validation in orchestrator Step 10 (ValidateReturn)** (orchestrator.md lines 524-630):
```
IF delegation is command:
  VERIFY Stage 7 completed:
    - CHECK command_stages["stage_7_completed"] == true
    - CHECK stage_7_artifacts["status_sync_manager_completed"] == true
    - CHECK stage_7_artifacts["todo_md_updated"] == true
    - CHECK stage_7_artifacts["state_json_updated"] == true
  
  IF any check fails:
    ERROR: "Command returned without completing Stage 7"
    RETURN error to user with checkpoint details
    REJECT return
```

**Note**: This recommendation is already documented in command-lifecycle.md lines 416-496 ("Orchestrator Stage Validation"). Implementation is pending.

---

## Estimated Effort for Fixes

### Per-Command Effort

| Command | Context Loading Fix | Path Error Fix | Total Effort |
|---------|-------------------|----------------|--------------|
| /research | 30 minutes | N/A | 30 minutes |
| /plan | 30 minutes | 5 minutes | 35 minutes |
| /implement | 30 minutes | N/A | 30 minutes |
| /revise | 30 minutes | 5 minutes | 35 minutes |
| /todo | N/A (no changes) | N/A | 0 minutes |
| /task | N/A (no changes) | N/A | 0 minutes |
| /review | N/A (no changes) | N/A | 0 minutes |
| /errors | N/A (no changes) | N/A | 0 minutes |

**Total Command Fixes**: 2 hours 10 minutes

### Documentation Effort

| Document | Changes | Effort |
|----------|---------|--------|
| command-lifecycle.md | Add Stage 4 context loading section | 30 minutes |
| lightweight-routing-pattern.md | Create new document | 1 hour |
| orchestrator.md | Add stage tracking validation (Rec 5) | 2 hours |

**Total Documentation**: 3 hours 30 minutes

### Testing Effort

| Test | Description | Effort |
|------|-------------|--------|
| Routing context usage | Verify <10% context usage during routing | 30 minutes |
| Command execution | Verify all commands still function correctly | 1 hour |
| Safety validation | Verify no regression in safety checks | 30 minutes |
| Error handling | Verify error messages still clear and actionable | 30 minutes |

**Total Testing**: 2 hours 30 minutes

### Total Effort Estimate

| Category | Effort |
|----------|--------|
| Command Fixes | 2 hours 10 minutes |
| Documentation | 3 hours 30 minutes |
| Testing | 2 hours 30 minutes |
| **Total** | **8 hours 10 minutes** |

**Breakdown by Priority**:
- CRITICAL (Rec 1): 2 hours 10 minutes (commands) + 30 minutes (lifecycle doc) + 2 hours (testing) = 4 hours 40 minutes
- HIGH (Rec 2): 10 minutes (path fixes) + 10 minutes (testing) = 20 minutes
- MEDIUM (Rec 3): 1 hour (doc) + 30 minutes (testing) = 1 hour 30 minutes
- MEDIUM (Rec 5): 2 hours (orchestrator) + 30 minutes (testing) = 2 hours 30 minutes
- LOW (Rec 4): 0 minutes (no changes)

**Recommended Implementation Order**:
1. **Phase 1** (CRITICAL): Recommendation 1 + 2 (5 hours total)
2. **Phase 2** (MEDIUM): Recommendation 3 + 5 (4 hours total)
3. **Phase 3** (LOW): Recommendation 4 (0 hours - no changes)

---

## Safety Considerations for Immediate Delegation

### Safety Mechanisms That Preserve Correctness

1. **Automated Validation** (no user confirmation needed):
   - Task existence verification (bash grep)
   - Status verification (not completed/abandoned)
   - Language field extraction with fallback (default to "general")
   - Plan existence verification (bash grep for "Plan:" link)
   - Range validation (for /implement with task ranges)

2. **Clear Error Messages** (actionable without confirmation):
   - "Error: Task number required. Usage: /implement TASK_NUMBER [PROMPT]"
   - "Error: Task {task_number} not found in .opencode/specs/TODO.md"
   - "Error: Task {task_number} has no plan. Use /plan instead."
   - "Warning: Tasks {missing_list} not found. Continuing with {found_list}"

3. **Atomic Operations** (safety via two-phase commit):
   - status-sync-manager performs two-phase commit
   - Phase 1: Prepare, validate artifacts, backup
   - Phase 2: Write all files or rollback all
   - No partial state corruption possible

4. **Graceful Degradation** (continue without confirmation):
   - Language defaults to "general" if extraction fails
   - Tool unavailability (lean-lsp-mcp) proceeds with degraded mode
   - Git commit failures log error but continue (non-critical)

5. **Warnings Without Blocking** (informational, not blocking):
   - Plan already exists (suggest /revise instead)
   - Tool unavailability (note in summary)
   - Partial success (some tasks in range missing)

### When User Confirmation IS Required

**Legitimate Confirmation Scenarios**:

1. **Destructive Bulk Operations** (>threshold):
   - /todo archiving >5 tasks (moves directories)
   - Bulk deletion operations (if implemented)
   - Mass status changes (if implemented)

2. **Ambiguous User Intent** (multiple valid interpretations):
   - Command has multiple modes with different outcomes
   - User input could mean multiple things
   - Clarification needed to proceed correctly

3. **External Approval Required** (policy/process):
   - Production deployments
   - Security-sensitive operations
   - Operations requiring manager approval

**Current Commands**:
- /research: NO confirmation needed (read-only research)
- /plan: NO confirmation needed (creates plan artifact)
- /implement: NO confirmation needed (creates implementation artifacts)
- /revise: NO confirmation needed (creates new plan version)
- /todo: YES confirmation needed for >5 tasks (destructive bulk operation)

### Safety Checklist for Immediate Delegation

Before implementing immediate delegation, verify:

- [ ] All preconditions can be validated automatically
- [ ] Error messages are clear and actionable
- [ ] Operations are atomic (two-phase commit)
- [ ] Graceful degradation for tool unavailability
- [ ] Warnings are informational, not blocking
- [ ] No destructive bulk operations without threshold
- [ ] No ambiguous user intent requiring clarification
- [ ] No external approval required

**All workflow commands (/research, /plan, /implement, /revise) pass this checklist**, so immediate delegation is safe and correct.

---

## Conclusion

This research systematically analyzed all workflow commands to identify confirmation prompts, context loading patterns, and routing logic inefficiencies. The findings reveal that:

1. **No confirmation prompts exist in workflow commands** - All commands already follow immediate delegation patterns
2. **Context is loaded too early** - 7-8 files loaded in command frontmatter during orchestrator routing
3. **Routing needs only 3 pieces of info** - task_number, language, plan_existence (extracted via bash)
4. **Safety is preserved** - Automated validation, atomic operations, clear errors ensure correctness
5. **Lightweight routing pattern exists** - Extract info via bash, route to agent, delegate with minimal context

**Primary Fix**: Move context loading from command frontmatter (lines 11-18) to command execution stage (Stage 4, after delegation). This will reduce orchestrator routing context usage from 60-70% to <10%, preserving context budget for actual work.

**Secondary Fixes**: Fix duplicate path errors in /plan and /revise, document lightweight routing pattern, add orchestrator Stage 7 validation checkpoint.

**Total Effort**: 8 hours 10 minutes (4 hours 40 minutes for critical fixes)

**Expected Impact**: 90% reduction in orchestrator routing context usage, elimination of unnecessary context loading, preservation of safety and correctness, improved user experience with instant command response.
