# Research Report: Orchestrator Command File Workflow Execution Mechanism

**Task**: 342 - Research orchestrator command file workflow execution mechanism  
**Report**: research-001  
**Date**: 2026-01-08  
**Researcher**: researcher  
**Session**: Task 342 Research

---

## Executive Summary

The orchestrator does NOT execute command file `<workflow_execution>` stages, causing systematic postflight failures across all workflow commands. Root cause: The OpenAgents migration (tasks 240-247) moved workflow ownership from subagents to command files but the orchestrator was never updated to parse and execute command file stages. Current orchestrator is a "pure router" (v7.0) that loads command files and delegates to them via the task tool, but OpenCode's task tool does NOT execute XML workflow stages - it only passes the command file content as context. This architectural mismatch causes Stage 3.5 (Postflight) to never execute, resulting in artifacts created but not linked, status not updated, and no git commits. Solution requires implementing a workflow execution engine in the orchestrator that parses `<workflow_execution>` stages from command files and executes them sequentially with proper context passing, error handling, and rollback mechanisms. Alternative: Revert to subagent-driven workflow ownership (pre-migration architecture) where subagents own complete workflows including postflight.

---

## Research Scope

**Objective**: Understand how the orchestrator should execute command file workflow_execution stages and why they are currently not being executed.

**Sources Analyzed**:
- `.opencode/agent/orchestrator.md` (current v7.0 implementation)
- `.opencode/command/research.md` (example command with workflow_execution stages)
- `.opencode/command/implement.md` (example command with workflow_execution stages)
- `.opencode/docs/architecture/orchestrator-workflow-execution-issue.md` (issue documentation)
- `.opencode/docs/migrations/001-openagents-migration/adr/ADR-002-agent-workflow-ownership.md`
- `.opencode/specs/archive/240_*/reports/research-001.md` (OpenAgents comparison)
- `.opencode/specs/archive/245_*/plans/implementation-001.md` (migration plan)
- `.opencode/agent/subagents/researcher.md` (subagent with deprecated preflight/postflight)
- `.opencode/agent/subagents/implementer.md` (subagent with deprecated preflight/postflight)

**Methodology**: 
1. Analyze current orchestrator delegation mechanism
2. Examine command file workflow_execution structure
3. Trace execution flow from orchestrator through command to subagent
4. Compare with OpenAgents architecture and migration goals
5. Identify architectural mismatch and root cause
6. Design solution approaches with tradeoffs

---

## Key Findings

### Finding 1: Orchestrator is a Pure Router (Does NOT Execute Workflow Stages)

**Current Orchestrator Architecture** (v7.0):

The orchestrator is a "pure router" with only 2 stages:

```markdown
<workflow_execution>
  <stage id="1" name="LoadCommand">
    <action>Load command file and extract configuration</action>
    <process>
      1. Extract command name from invocation (e.g., "/research 271")
      2. Load command file: .opencode/command/{command_name}.md
      3. Parse command frontmatter (extract agent field)
      4. Validate command file (must have agent field)
    </process>
  </stage>

  <stage id="2" name="Delegate">
    <action>Delegate to command file agent with $ARGUMENTS</action>
    <process>
      1. Invoke command file as agent via task tool
      2. Wait for command agent return
      3. Relay result to user
    </process>
  </stage>
</workflow_execution>
```

**Critical Observation**: The orchestrator has NO stage parsing logic, NO workflow execution engine, and NO mechanism to execute command file `<workflow_execution>` stages.

**What the Orchestrator Does**:
1. Loads command file from disk
2. Extracts `agent` field from frontmatter (which is "orchestrator")
3. Invokes task tool with command file content as context
4. Relays result to user

**What the Orchestrator Does NOT Do**:
- Parse `<workflow_execution>` stages from command files
- Execute stages sequentially
- Pass context between stages
- Handle stage errors or rollback
- Validate stage completion

**Architectural Note**: The orchestrator documentation states:

> "When agent field is 'orchestrator', OpenCode delegates to the command file itself. The command file is a full agent with workflow_execution stages."

This implies OpenCode's task tool should execute workflow stages, but this is NOT how OpenCode works.

---

### Finding 2: Command Files Have Comprehensive Workflow Stages (But They Don't Execute)

**Command File Structure** (e.g., `/research`, `/implement`):

All workflow command files have detailed 4-6 stage workflows:

```markdown
<workflow_execution>
  <stage id="1" name="ParseAndValidate">
    <action>Parse task number and lookup in state.json</action>
    <process>
      1. Parse task number from $ARGUMENTS
      2. Validate state.json exists
      3. Lookup task in state.json
      4. Extract metadata (language, status, description)
      5. Validate task status allows operation
      6. Determine target agent based on language
    </process>
  </stage>
  
  <stage id="1.5" name="Preflight">
    <action>Update status to [RESEARCHING] before delegating</action>
    <process>
      1. Generate session_id
      2. Delegate to status-sync-manager to update status
      3. Validate status-sync-manager return
      4. Verify status was actually updated (defense in depth)
      5. Log preflight success
    </process>
  </stage>
  
  <stage id="2" name="Delegate">
    <action>Delegate to researcher with parsed context</action>
    <process>
      1. Use session_id from Stage 1.5
      2. Invoke target agent via task tool
      3. Wait for researcher to complete
    </process>
  </stage>
  
  <stage id="3" name="ValidateReturn">
    <action>Validate subagent return format and artifacts</action>
    <process>
      1. Validate JSON structure
      2. Validate required fields
      3. Validate status field
      4. Validate session ID
      5. Validate artifacts exist on disk (CRITICAL)
    </process>
  </stage>
  
  <stage id="3.5" name="Postflight">
    <action>Update status to [RESEARCHED], link artifacts, create git commit</action>
    <process>
      1. Extract artifacts from subagent return
      2. Validate artifacts exist on disk (prevents Task 326 issue)
      3. Delegate to status-sync-manager to update status and link artifacts
      4. Validate status-sync-manager return
      5. Verify status and artifact links were actually updated
      6. Delegate to git-workflow-manager to create commit
      7. Validate git-workflow-manager return
      8. Log postflight success
    </process>
  </stage>
  
  <stage id="4" name="RelayResult">
    <action>Relay validated result to user</action>
  </stage>
</workflow_execution>
```

**Stage 3.5 (Postflight) is Critical**: This stage:
- Validates artifacts exist on disk
- Updates status to completed marker ([RESEARCHED], [COMPLETED], [PLANNED])
- Links artifacts in TODO.md and state.json
- Creates git commit

**Problem**: These stages are XML documentation, NOT executable code. The orchestrator does not parse or execute them.

---

### Finding 3: OpenCode's Task Tool Does NOT Execute Workflow Stages

**How OpenCode's Task Tool Works**:

When the orchestrator invokes:
```
task(
  subagent_type="orchestrator",
  prompt="Content of .opencode/command/implement.md with $ARGUMENTS=259",
  description="Execute /implement command"
)
```

OpenCode does the following:
1. Loads the command file content as context
2. Passes $ARGUMENTS to the agent
3. Invokes Claude with the context
4. Returns Claude's response

**What OpenCode Does NOT Do**:
- Parse `<workflow_execution>` stages
- Execute stages sequentially
- Pass context between stages
- Handle stage errors
- Validate stage completion

**Critical Insight**: The `<workflow_execution>` XML is treated as narrative documentation for Claude, NOT as executable instructions. Claude may or may not follow the stages depending on context window pressure, token limits, and interpretation.

**Evidence from Task 335**: Task 335 (`/implement 335`) created implementation artifacts successfully but:
- Status remained [NOT STARTED] instead of [COMPLETED]
- Artifacts were not linked in TODO.md or state.json
- No git commit was created automatically
- User had to manually fix status and links

This proves Stage 3.5 (Postflight) did NOT execute.

---

### Finding 4: OpenAgents Migration Created Architectural Mismatch

**Pre-Migration Architecture** (Before tasks 240-247):

```
Orchestrator (router)
  ↓
Command File (thin routing layer, ~200 lines)
  ↓
Subagent (owns complete workflow including preflight/postflight)
```

**Subagents owned**:
- Step 0 (Preflight): Update status to in-progress marker
- Steps 1-5: Core work execution
- Step 6 (Postflight): Update status to completed marker, link artifacts, create git commit

**Result**: Preflight and postflight executed reliably because subagents owned them as executable code.

**Post-Migration Architecture** (After tasks 240-247):

```
Orchestrator (router)
  ↓
Command File (owns workflow stages, ~700 lines)
  ↓
Subagent (core work only, preflight/postflight deprecated)
```

**Command files own**:
- Stage 1 (ParseAndValidate)
- Stage 1.5 (Preflight): Update status to in-progress marker
- Stage 2 (Delegate to subagent)
- Stage 3 (ValidateReturn)
- Stage 3.5 (Postflight): Update status to completed marker, link artifacts, create git commit
- Stage 4 (RelayResult)

**Subagents deprecated**:
- Step 0 (Preflight): DEPRECATED - command file handles preflight
- Step 6 (Postflight): DEPRECATED - command file handles postflight

**Problem**: Command files define stages as XML documentation, but orchestrator does not execute them. Subagents deprecated their preflight/postflight, so no one executes them.

**Architectural Mismatch**: The migration moved workflow ownership from subagents (executable code) to command files (XML documentation) without updating the orchestrator to execute command file stages.

---

### Finding 5: ADR-002 Documents Intended Architecture (But Not Implemented)

**ADR-002: Agent Workflow Ownership Pattern** states:

> "Chosen Option: Agent-Driven Workflow (Option 3)
> 
> Agents own complete 8-stage workflow. Commands become thin delegation layers that route to agents."

**Implementation**:
1. **8-Stage Workflow Ownership**: Agents own all 8 stages
2. **Command Simplification**: Commands become thin delegation layers
3. **Stage 7 Requirements**: All agents must implement Stage 7 (artifact validation, status updates, git commits)

**Expected Results**:
- Reliability: Achieved 100% Stage 7 execution rate (up from ~80%)
- Commands reduced from 800-1200 lines to 180-270 lines

**Actual Results**:
- Commands are 500-800 lines (NOT thin delegation layers)
- Commands contain full workflow stages (NOT agents)
- Subagents deprecated preflight/postflight (NOT owning complete workflow)
- Stage 7 execution rate is 0% (NOT 100%)

**Conclusion**: ADR-002 describes the intended architecture but the implementation went in a different direction. Command files own workflow stages (not agents), creating the architectural mismatch.

---

### Finding 6: Two Conflicting Architectural Patterns

**Pattern A: Command-Driven Workflow** (Current Implementation):
- Command files contain `<workflow_execution>` stages (XML documentation)
- Orchestrator loads command file and delegates to it
- OpenCode treats stages as narrative, not executable
- Subagents deprecated preflight/postflight
- **Result**: Stages don't execute, postflight never runs

**Pattern B: Agent-Driven Workflow** (ADR-002 Intent):
- Command files are thin routing layers (~200 lines)
- Agents own complete workflow including preflight/postflight
- Agents execute workflow as code, not documentation
- Orchestrator delegates to agent immediately
- **Result**: Workflow executes reliably (proven in OpenAgents)

**Current State**: Hybrid of both patterns, taking the worst of each:
- Command files are heavy (700 lines) like Pattern A
- Subagents deprecated preflight/postflight like Pattern B
- Orchestrator doesn't execute stages (neither pattern)
- **Result**: No one owns preflight/postflight execution

---

## Root Cause Analysis

### Primary Root Cause

**The orchestrator does not execute command file `<workflow_execution>` stages.**

The orchestrator is a "pure router" that:
1. Loads command file
2. Delegates to command file via task tool
3. Relays result

OpenCode's task tool treats `<workflow_execution>` stages as narrative documentation for Claude, NOT as executable instructions. Claude may skip stages under context window pressure or token limits.

### Secondary Root Cause

**The OpenAgents migration (tasks 240-247) moved workflow ownership from subagents to command files without updating the orchestrator to execute command file stages.**

The migration:
- Moved preflight/postflight from subagents (executable code) to command files (XML documentation)
- Deprecated subagent preflight/postflight
- Did NOT update orchestrator to parse and execute command file stages
- **Result**: No one executes preflight/postflight

### Tertiary Root Cause

**Architectural mismatch between ADR-002 intent (agent-driven) and actual implementation (command-driven).**

ADR-002 intended:
- Agents own complete workflow
- Commands are thin routing layers
- 100% Stage 7 execution

Actual implementation:
- Commands own workflow stages (as XML)
- Agents deprecated preflight/postflight
- 0% Stage 7 execution

---

## Solution Approaches

### Approach 1: Implement Workflow Execution Engine in Orchestrator (Command-Driven)

**Description**: Update orchestrator to parse `<workflow_execution>` stages from command files and execute them sequentially.

**Implementation**:

1. **Stage Parser**: Parse `<workflow_execution>` XML from command file
   - Extract stage id, name, action, process, checkpoint
   - Build stage execution plan
   - Validate stage dependencies

2. **Execution Engine**: Execute stages sequentially
   - Execute stage process steps in order
   - Pass context between stages (e.g., session_id, task_data)
   - Capture stage outputs for next stage
   - Validate checkpoint conditions

3. **Context Passing**: Maintain execution context across stages
   - session_id (generated in Stage 1.5)
   - task_number, language, status, description (from Stage 1)
   - subagent_return (from Stage 2)
   - validated_artifacts (from Stage 3)

4. **Error Handling**: Handle stage failures gracefully
   - If stage fails: Log error, execute rollback, return error to user
   - If validation fails: Abort execution, return error
   - If timeout: Cancel execution, return timeout error

5. **Rollback Mechanism**: Revert changes on failure
   - Track state changes per stage
   - On failure: Revert status updates, delete partial artifacts
   - Log rollback actions

**Pros**:
- Preserves current command file structure (no migration needed)
- Enables command-driven workflow pattern
- Provides explicit stage execution control
- Allows stage-level error handling and rollback

**Cons**:
- High implementation complexity (8-12 hours)
- Orchestrator becomes complex (no longer "pure router")
- XML parsing adds overhead
- Requires maintaining execution engine
- Does not align with ADR-002 intent (agent-driven)

**Effort**: 8-12 hours

**Risk**: Medium (complex implementation, potential bugs in stage parsing/execution)

---

### Approach 2: Revert to Agent-Driven Workflow (Align with ADR-002)

**Description**: Revert to pre-migration architecture where subagents own complete workflows including preflight/postflight.

**Implementation**:

1. **Simplify Command Files**: Reduce to thin routing layers (~200 lines)
   - Remove `<workflow_execution>` stages
   - Keep only frontmatter, description, usage
   - Delegate immediately to agent

2. **Restore Subagent Workflow Ownership**: Un-deprecate preflight/postflight
   - Move Stage 1.5 (Preflight) back to subagents as Step 0
   - Move Stage 3.5 (Postflight) back to subagents as Step 6
   - Subagents own complete workflow (Steps 0-6)

3. **Update Orchestrator**: Simplify to pure router
   - Load command file
   - Extract agent field
   - Delegate to agent immediately
   - Relay result

**Pros**:
- Aligns with ADR-002 intent (agent-driven workflow)
- Proven pattern (worked pre-migration)
- Simple orchestrator (pure router)
- Subagents own workflow as executable code (not XML)
- Achieves 100% Stage 7 execution (proven in OpenAgents)

**Cons**:
- Requires reverting migration work (tasks 240-247)
- Command files lose workflow control
- Subagents become more complex (own complete workflow)
- Requires updating all 4 command files and 6 subagents

**Effort**: 12-16 hours (4 commands + 6 subagents)

**Risk**: Low (proven pattern, reverting to known-good state)

---

### Approach 3: Hybrid - Command Preflight/Postflight, Agent Core Work

**Description**: Keep preflight/postflight in command files but make them executable (not XML).

**Implementation**:

1. **Convert Command Stages to Bash Scripts**: Replace XML stages with executable bash
   - Stage 1: Parse arguments (bash script)
   - Stage 1.5: Preflight (bash script calling status-sync-manager)
   - Stage 2: Delegate to agent (bash script calling task tool)
   - Stage 3: Validate return (bash script with jq)
   - Stage 3.5: Postflight (bash script calling status-sync-manager and git-workflow-manager)
   - Stage 4: Relay result (bash script)

2. **Update Orchestrator**: Execute command file as bash script
   - Load command file
   - Extract bash script sections
   - Execute bash script with $ARGUMENTS
   - Capture output and relay to user

3. **Subagents**: Keep core work only (no preflight/postflight)

**Pros**:
- Command files own workflow (executable, not XML)
- Orchestrator executes bash (simpler than XML parsing)
- Preserves command-driven pattern
- Explicit stage execution

**Cons**:
- Command files become bash scripts (not markdown)
- Loses markdown documentation structure
- Bash scripting complexity
- Harder to maintain than agent-driven pattern

**Effort**: 10-14 hours

**Risk**: Medium (bash scripting complexity, potential for bugs)

---

### Approach 4: Minimal Fix - Execute Postflight Only

**Description**: Keep current architecture but add explicit postflight execution in orchestrator.

**Implementation**:

1. **Orchestrator Stage 2.5 (Postflight)**: After delegation, execute postflight
   - Extract artifacts from subagent return
   - Validate artifacts exist on disk
   - Call status-sync-manager to update status and link artifacts
   - Call git-workflow-manager to create commit
   - Validate postflight succeeded

2. **Command Files**: Keep current structure (no changes)

3. **Subagents**: Keep current structure (no changes)

**Pros**:
- Minimal changes (orchestrator only)
- Preserves current architecture
- Fixes immediate issue (postflight not executing)
- Low implementation effort

**Cons**:
- Does not fix preflight (still in command files as XML)
- Does not align with ADR-002 intent
- Orchestrator becomes less "pure" (owns postflight logic)
- Duplicates postflight logic (orchestrator + command files)

**Effort**: 4-6 hours

**Risk**: Low (minimal changes, focused fix)

---

## Comparison of Approaches

| Aspect | Approach 1 (Workflow Engine) | Approach 2 (Agent-Driven) | Approach 3 (Bash Scripts) | Approach 4 (Minimal Fix) |
|--------|------------------------------|---------------------------|---------------------------|--------------------------|
| **Complexity** | High (XML parsing, execution engine) | Medium (revert migration) | Medium (bash scripting) | Low (orchestrator only) |
| **Effort** | 8-12 hours | 12-16 hours | 10-14 hours | 4-6 hours |
| **Risk** | Medium (complex implementation) | Low (proven pattern) | Medium (bash complexity) | Low (minimal changes) |
| **Aligns with ADR-002** | No (command-driven) | Yes (agent-driven) | No (command-driven) | No (hybrid) |
| **Orchestrator Simplicity** | Low (complex engine) | High (pure router) | Medium (bash execution) | Medium (postflight logic) |
| **Command File Size** | 700 lines (no change) | 200 lines (thin routing) | 700 lines (bash scripts) | 700 lines (no change) |
| **Subagent Complexity** | Low (core work only) | High (complete workflow) | Low (core work only) | Low (core work only) |
| **Stage 7 Execution** | 100% (explicit execution) | 100% (agent owns it) | 100% (bash execution) | 100% (orchestrator owns it) |
| **Maintainability** | Low (complex engine) | High (proven pattern) | Medium (bash scripts) | Medium (duplicated logic) |

---

## Recommendations

### Primary Recommendation: Approach 2 (Agent-Driven Workflow)

**Rationale**:
1. **Aligns with ADR-002 Intent**: Agent-driven workflow is the documented architectural decision
2. **Proven Pattern**: Worked reliably pre-migration, proven in OpenAgents
3. **Simple Orchestrator**: Pure router pattern (15-100 lines)
4. **Executable Workflow**: Subagents own workflow as code, not XML documentation
5. **100% Stage 7 Execution**: Guaranteed because subagents own it
6. **Long-Term Maintainability**: Clear ownership (agents own workflow)

**Implementation Path**:
1. Simplify command files to thin routing layers (~200 lines each)
2. Un-deprecate subagent preflight/postflight (restore Step 0 and Step 6)
3. Move Stage 1.5 (Preflight) from commands to subagents as Step 0
4. Move Stage 3.5 (Postflight) from commands to subagents as Step 6
5. Update orchestrator to pure router (if not already)
6. Test all 4 commands with 20 runs each (80 total)
7. Validate 100% Stage 7 execution

**Effort**: 12-16 hours (4 commands × 2 hours + 6 subagents × 1 hour + 2 hours testing)

**Risk**: Low (reverting to known-good state)

### Secondary Recommendation: Approach 4 (Minimal Fix)

**Rationale**:
1. **Quick Fix**: Addresses immediate issue (postflight not executing)
2. **Low Risk**: Minimal changes, focused fix
3. **Low Effort**: 4-6 hours implementation
4. **Preserves Current Architecture**: No migration needed

**Use Case**: If time-constrained or need immediate fix before full refactor

**Implementation Path**:
1. Add Stage 2.5 (Postflight) to orchestrator after delegation
2. Extract artifacts from subagent return
3. Validate artifacts exist on disk
4. Call status-sync-manager to update status and link artifacts
5. Call git-workflow-manager to create commit
6. Test all 4 commands

**Effort**: 4-6 hours

**Risk**: Low

**Note**: This is a band-aid fix. Long-term, should migrate to Approach 2 (agent-driven).

### Not Recommended: Approach 1 (Workflow Engine)

**Rationale**:
1. **High Complexity**: XML parsing, execution engine, context passing
2. **Does Not Align with ADR-002**: Command-driven, not agent-driven
3. **Maintenance Burden**: Complex engine to maintain
4. **Orchestrator Complexity**: No longer "pure router"

**Use Case**: Only if command-driven workflow is explicitly desired (contradicts ADR-002)

### Not Recommended: Approach 3 (Bash Scripts)

**Rationale**:
1. **Loses Markdown Structure**: Command files become bash scripts
2. **Bash Complexity**: Harder to maintain than agent-driven pattern
3. **Does Not Align with ADR-002**: Command-driven, not agent-driven

**Use Case**: None (worse than Approach 1 or 2)

---

## Design Specification: Approach 2 (Agent-Driven Workflow)

### Architecture Overview

```
User
  ↓
Orchestrator (pure router, ~100 lines)
  ↓
Command File (thin routing layer, ~200 lines)
  - Frontmatter: agent field
  - Description: What this command does
  - Usage: How to use it
  ↓
Subagent (owns complete workflow, ~500 lines)
  - Step 0 (Preflight): Update status to in-progress
  - Steps 1-5: Core work execution
  - Step 6 (Postflight): Update status to completed, link artifacts, create git commit
```

### Orchestrator Workflow (2 Stages)

```markdown
<workflow_execution>
  <stage id="1" name="LoadCommand">
    <action>Load command file and extract configuration</action>
    <process>
      1. Extract command name from invocation
      2. Load command file: .opencode/command/{command_name}.md
      3. Parse command frontmatter (extract agent field)
      4. Validate command file (must have agent field)
    </process>
  </stage>

  <stage id="2" name="Delegate">
    <action>Delegate to agent with $ARGUMENTS</action>
    <process>
      1. Extract agent path from frontmatter
      2. Invoke agent via task tool with $ARGUMENTS
      3. Wait for agent return
      4. Relay result to user
    </process>
  </stage>
</workflow_execution>
```

### Command File Structure (~200 lines)

```markdown
---
name: research
agent: researcher
description: "Conduct research and create reports with [RESEARCHED] status"
timeout: 3600
routing:
  language_based: true
  lean: lean-research-agent
  default: researcher
---

# /research - Research Command

Conduct comprehensive research on a specified topic and generate structured research reports.

## Usage

/research {task_number}
/research {task_number} {custom_prompt}
/research {task_number} --force

## What This Command Does

1. Parses task number from arguments
2. Validates task exists in TODO.md
3. Extracts language from task metadata
4. Routes to appropriate researcher based on language
5. Researcher conducts research and creates report
6. Updates task status to [RESEARCHED]
7. Links artifacts in TODO.md and state.json
8. Creates git commit

## Examples

/research 271
/research 271 Focus on API integration
/research 271 --force

## Notes

- Researcher owns complete workflow including status updates and git commits
- Command file is thin routing layer only
- See researcher.md for workflow details
```

### Subagent Workflow (Steps 0-6)

```markdown
<process_flow>
  <step_0_preflight>
    <action>Preflight: Update status to [RESEARCHING]</action>
    <process>
      1. Generate session_id for tracking
      2. Delegate to status-sync-manager to update status
      3. Validate status-sync-manager return
      4. Verify status was actually updated (defense in depth)
      5. Log preflight success
    </process>
    <checkpoint>Status updated to [RESEARCHING] before research begins</checkpoint>
  </step_0_preflight>

  <step_1_research_execution>
    <action>Research Execution: Conduct research and gather findings</action>
    <process>
      1. Analyze research topic and determine approach
      2. Subdivide topic if requested or beneficial
      3. Conduct research (web search, documentation review)
      4. Organize findings for report creation
    </process>
    <output>Research findings with citations and recommendations</output>
  </step_1_research_execution>

  <step_2_artifact_creation>
    <action>Artifact Creation: Create research report</action>
    <process>
      1. Generate topic slug from research topic
      2. Lazy create project directory
      3. Lazy create reports subdirectory
      4. Write detailed report: reports/research-001.md
      5. Include metadata, sections, citations
      6. Validate artifact created successfully
    </process>
    <output>Research report artifact at validated path</output>
  </step_2_artifact_creation>

  <step_3_validation>
    <action>Validation: Verify artifact and prepare return</action>
    <process>
      1. Validate research artifact created successfully
      2. Prepare artifact metadata
      3. Create brief summary for return object
      4. Prepare validated_artifacts array
      5. Calculate duration_seconds
    </process>
    <output>Validated artifact metadata and brief summary</output>
  </step_3_validation>

  <step_4_return>
    <action>Return: Format and return standardized result</action>
    <process>
      1. Format return following subagent-return-format.md
      2. Validate return format
      3. Return standardized result
    </process>
    <output>Standardized return object with validated research report</output>
  </step_4_return>

  <step_5_postflight>
    <action>Postflight: Update status to [RESEARCHED], link artifacts, create git commit</action>
    <process>
      1. Extract artifacts from return object
      2. Validate artifacts exist on disk (CRITICAL)
      3. Delegate to status-sync-manager to update status and link artifacts
      4. Validate status-sync-manager return
      5. Verify status and artifact links were actually updated
      6. Delegate to git-workflow-manager to create commit
      7. Validate git-workflow-manager return
      8. Log postflight success
    </process>
    <checkpoint>Status updated to [RESEARCHED], artifacts linked, git commit created</checkpoint>
  </step_5_postflight>
</process_flow>
```

### Context Passing

**Orchestrator → Command File**:
- $ARGUMENTS (e.g., "271" or "271 custom prompt")

**Command File → Subagent**:
- task_number (parsed from $ARGUMENTS)
- language (extracted from state.json)
- task_description (extracted from TODO.md or state.json)
- custom_prompt (optional, from $ARGUMENTS)
- session_id (generated by command or subagent)
- delegation_depth (tracked by orchestrator)
- delegation_path (tracked by orchestrator)

**Subagent → Command File → Orchestrator → User**:
- Standardized return object (subagent-return-format.md):
  ```json
  {
    "status": "completed",
    "summary": "Research completed on {topic}. Found {N} key insights.",
    "artifacts": [{
      "type": "research",
      "path": ".opencode/specs/{task_number}_{slug}/reports/research-001.md",
      "summary": "Detailed research report"
    }],
    "metadata": {
      "session_id": "sess_20260108_abc123",
      "duration_seconds": 1250,
      "agent_type": "researcher",
      "delegation_depth": 1,
      "delegation_path": ["orchestrator", "research", "researcher"]
    },
    "errors": [],
    "next_steps": "Review research findings and create implementation plan"
  }
  ```

### Error Handling

**Preflight Failure** (Step 0):
- If status-sync-manager fails: Log error, return error to user, DO NOT proceed to research
- If status verification fails: Log error, return error to user, DO NOT proceed to research

**Research Failure** (Steps 1-2):
- If research fails: Log error, create partial report (if any), return status: "partial"
- If artifact creation fails: Log error, return status: "failed"

**Postflight Failure** (Step 5):
- If status-sync-manager fails: Log warning, research work is done, manual fix needed
- If git-workflow-manager fails: Log warning, non-critical, manual git commit needed

### Rollback Mechanism

**Preflight Rollback**:
- If preflight fails: No rollback needed (no work done yet)

**Research Rollback**:
- If research fails: Delete partial artifacts, revert status to previous value

**Postflight Rollback**:
- If postflight fails: Research work is done, no rollback (manual fix needed)

---

## Implementation Checklist

### Phase 1: Simplify Command Files (8 hours)

- [ ] Simplify /research command to thin routing layer (~200 lines)
  - [ ] Remove `<workflow_execution>` stages
  - [ ] Keep frontmatter, description, usage only
  - [ ] Update frontmatter: agent: researcher
  - [ ] Test /research command

- [ ] Simplify /plan command to thin routing layer (~200 lines)
  - [ ] Remove `<workflow_execution>` stages
  - [ ] Keep frontmatter, description, usage only
  - [ ] Update frontmatter: agent: planner
  - [ ] Test /plan command

- [ ] Simplify /implement command to thin routing layer (~200 lines)
  - [ ] Remove `<workflow_execution>` stages
  - [ ] Keep frontmatter, description, usage only
  - [ ] Update frontmatter: agent: implementer
  - [ ] Test /implement command

- [ ] Simplify /revise command to thin routing layer (~200 lines)
  - [ ] Remove `<workflow_execution>` stages
  - [ ] Keep frontmatter, description, usage only
  - [ ] Update frontmatter: agent: task-executor
  - [ ] Test /revise command

### Phase 2: Restore Subagent Workflow Ownership (6 hours)

- [ ] Un-deprecate researcher.md preflight/postflight
  - [ ] Restore Step 0 (Preflight) from deprecated section
  - [ ] Restore Step 5 (Postflight) from deprecated section
  - [ ] Update process_flow to include Steps 0-5
  - [ ] Test researcher with /research command

- [ ] Un-deprecate planner.md preflight/postflight
  - [ ] Restore Step 0 (Preflight)
  - [ ] Restore Step 5 (Postflight)
  - [ ] Update process_flow to include Steps 0-5
  - [ ] Test planner with /plan command

- [ ] Un-deprecate implementer.md preflight/postflight
  - [ ] Restore Step 0 (Preflight)
  - [ ] Restore Step 5 (Postflight)
  - [ ] Update process_flow to include Steps 0-5
  - [ ] Test implementer with /implement command

- [ ] Un-deprecate task-executor.md preflight/postflight
  - [ ] Restore Step 0 (Preflight)
  - [ ] Restore Step 5 (Postflight)
  - [ ] Update process_flow to include Steps 0-5
  - [ ] Test task-executor with /revise command

- [ ] Un-deprecate lean-research-agent.md preflight/postflight
  - [ ] Restore Step 0 (Preflight)
  - [ ] Restore Step 5 (Postflight)
  - [ ] Test lean-research-agent with /research on Lean task

- [ ] Un-deprecate lean-implementation-agent.md preflight/postflight
  - [ ] Restore Step 0 (Preflight)
  - [ ] Restore Step 5 (Postflight)
  - [ ] Test lean-implementation-agent with /implement on Lean task

### Phase 3: Validate Orchestrator (2 hours)

- [ ] Verify orchestrator is pure router
  - [ ] Verify Stage 1 (LoadCommand) loads command file
  - [ ] Verify Stage 2 (Delegate) delegates to agent
  - [ ] Verify no workflow execution logic in orchestrator
  - [ ] Test orchestrator with all 4 commands

### Phase 4: Comprehensive Testing (2 hours)

- [ ] Test /research command (20 runs)
  - [ ] Verify preflight executes (status updates to [RESEARCHING])
  - [ ] Verify research executes (report created)
  - [ ] Verify postflight executes (status updates to [RESEARCHED], artifacts linked, git commit)
  - [ ] Validate 100% Stage 7 execution

- [ ] Test /plan command (20 runs)
  - [ ] Verify preflight executes (status updates to [PLANNING])
  - [ ] Verify planning executes (plan created)
  - [ ] Verify postflight executes (status updates to [PLANNED], artifacts linked, git commit)
  - [ ] Validate 100% Stage 7 execution

- [ ] Test /implement command (20 runs)
  - [ ] Verify preflight executes (status updates to [IMPLEMENTING])
  - [ ] Verify implementation executes (code changes made)
  - [ ] Verify postflight executes (status updates to [COMPLETED], artifacts linked, git commit)
  - [ ] Validate 100% Stage 7 execution

- [ ] Test /revise command (20 runs)
  - [ ] Verify preflight executes (status updates to [REVISING])
  - [ ] Verify revision executes (plan revised)
  - [ ] Verify postflight executes (status updates to [REVISED], artifacts linked, git commit)
  - [ ] Validate 100% Stage 7 execution

- [ ] Validate overall success metrics
  - [ ] 80/80 test runs successful (100% success rate)
  - [ ] 80/80 postflight executions (100% Stage 7 execution)
  - [ ] All artifacts linked in TODO.md and state.json
  - [ ] All git commits created

---

## Risks and Mitigations

### Risk 1: Subagents become too complex

**Probability**: Medium  
**Impact**: Medium  
**Mitigation**: 
- Follow subagent template with clear step structure
- Keep steps focused (single responsibility)
- Delegate to status-sync-manager and git-workflow-manager (don't implement inline)

### Risk 2: Command files lose workflow visibility

**Probability**: Low  
**Impact**: Low  
**Mitigation**:
- Document workflow in command file description
- Reference subagent for detailed workflow
- Maintain workflow documentation in subagent

### Risk 3: Migration breaks existing functionality

**Probability**: Low  
**Impact**: High  
**Mitigation**:
- Backup all files before migration
- Test each command after migration
- Rollback if any test fails
- Comprehensive testing (80 runs total)

### Risk 4: Preflight/postflight still don't execute

**Probability**: Very Low  
**Impact**: High  
**Mitigation**:
- Subagents own preflight/postflight as executable code (not XML)
- Test preflight/postflight explicitly in each test run
- Validate status updates and artifact links after each run

---

## Success Criteria

1. **Command File Size**: All 4 command files under 250 lines each (total under 1000 lines, down from 2800 lines)
2. **Subagent Workflow Ownership**: All 6 subagents own complete workflow (Steps 0-5)
3. **Orchestrator Simplicity**: Orchestrator remains pure router (under 100 lines)
4. **Stage 7 Execution**: 100% postflight execution across 80 test runs
5. **Artifact Linking**: All artifacts linked in TODO.md and state.json
6. **Git Commits**: All git commits created automatically
7. **No Manual Fixes**: Zero manual fixes needed (unlike Task 326, Task 335)

---

## Next Steps

1. **Create Task 343**: Design command file workflow execution architecture
   - Design stage parsing mechanism
   - Design execution engine
   - Design context passing between stages
   - Design error handling and rollback strategy
   - Plan integration with existing delegation system

2. **Create Task 344**: Implement orchestrator workflow execution engine
   - Implement stage parser
   - Implement execution engine
   - Implement context passing mechanism
   - Implement error handling and rollback
   - Integrate with existing delegation system

3. **Create Task 345**: Test and validate all workflow commands
   - Test /implement, /research, /plan, /revise
   - Verify artifact creation and linking
   - Verify status updates to completed markers
   - Verify git commit creation
   - Test error handling and rollback
   - Validate Task 335 scenario is fixed

**OR (Recommended)**:

1. **Implement Approach 2 (Agent-Driven Workflow)**: Revert to agent-driven workflow ownership
   - Simplify command files to thin routing layers
   - Un-deprecate subagent preflight/postflight
   - Test all 4 commands with 20 runs each
   - Validate 100% Stage 7 execution

---

## Conclusion

The orchestrator does NOT execute command file `<workflow_execution>` stages because OpenCode's task tool treats XML stages as narrative documentation, not executable instructions. The OpenAgents migration (tasks 240-247) moved workflow ownership from subagents to command files without updating the orchestrator to execute command file stages, creating an architectural mismatch. The recommended solution is **Approach 2 (Agent-Driven Workflow)**: Revert to agent-driven workflow ownership where subagents own complete workflows including preflight/postflight as executable code. This aligns with ADR-002 intent, is a proven pattern (worked pre-migration), and achieves 100% Stage 7 execution. Alternative minimal fix (Approach 4) adds postflight execution to orchestrator as a band-aid, but long-term should migrate to agent-driven pattern.

---

## References

- `.opencode/agent/orchestrator.md` - Current orchestrator implementation (v7.0)
- `.opencode/command/research.md` - Example command with workflow_execution stages
- `.opencode/command/implement.md` - Example command with workflow_execution stages
- `.opencode/docs/architecture/orchestrator-workflow-execution-issue.md` - Issue documentation
- `.opencode/docs/migrations/001-openagents-migration/adr/ADR-002-agent-workflow-ownership.md` - ADR-002
- `.opencode/specs/archive/240_*/reports/research-001.md` - OpenAgents comparison
- `.opencode/specs/archive/245_*/plans/implementation-001.md` - Migration plan
- `.opencode/agent/subagents/researcher.md` - Subagent with deprecated preflight/postflight
- `.opencode/agent/subagents/implementer.md` - Subagent with deprecated preflight/postflight
- Task 335 - Example of postflight failure (artifacts created but not linked)
- Task 326 - Example of manual fixes needed (status not updated)

---

**End of Research Report**
