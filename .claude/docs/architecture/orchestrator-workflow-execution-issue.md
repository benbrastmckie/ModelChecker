# Orchestrator Workflow Execution Issue - Root Cause Analysis

## Issue Summary

Task 335 (`/implement 335`) failed to update status and link artifacts in TODO.md and state.json, despite successfully creating implementation artifacts. This is a **systematic architectural issue** affecting ALL workflow commands (`/implement`, `/research`, `/plan`, `/revise`).

## Root Cause

The orchestrator loads command files and delegates to them, but **does NOT execute the command file's `<workflow_execution>` stages**. 

### What Should Happen

Command files (e.g., `.claude/command/implement.md`) have comprehensive 4-stage workflow patterns:

1. **Stage 1 (ParseAndValidate)**: Parse arguments, validate task, extract metadata
2. **Stage 1.5 (Preflight)**: Update status to in-progress marker ([IMPLEMENTING])
3. **Stage 2 (Delegate)**: Delegate to subagent with parsed context
4. **Stage 3 (ValidateReturn)**: Validate subagent return format and artifacts (5 validation steps)
5. **Stage 3.5 (Postflight)**: Update status to completed marker, link artifacts, create git commit (8 steps)
6. **Stage 4 (RelayResult)**: Relay validated result to user

### What Actually Happens

The orchestrator:
1. Loads command file from `.claude/command/{command}.md`
2. Extracts `agent` field from frontmatter (which is "orchestrator")
3. Delegates to command file via task tool
4. **STOPS HERE** - command file's workflow_execution stages are never executed

The orchestrator treats command files as simple routing metadata rather than full agents with workflow logic.

## Evidence

### 1. Command Files Have Comprehensive Postflight

All workflow command files have detailed Stage 3.5 (Postflight) with 8 steps:

```markdown
<stage id="3.5" name="Postflight">
  <action>Update status to [COMPLETED], link artifacts, create git commit</action>
  <process>
    1. Extract artifacts from subagent return
    2. Validate artifacts exist on disk (CRITICAL)
    3. Delegate to status-sync-manager to update status and link artifacts
    4. Validate status-sync-manager return
    5. Verify status and artifact links were actually updated (defense in depth)
    6. Delegate to git-workflow-manager to create commit
    7. Validate git-workflow-manager return
    8. Log postflight success
  </process>
</stage>
```

### 2. Subagents Have Deprecated Their Postflight

Subagents (implementer, researcher, planner) have **DEPRECATED** their postflight stages:

```markdown
<deprecated_step_0_preflight>
  <action>DEPRECATED: Preflight now handled by command file</action>
  <process>
    CRITICAL TIMING REQUIREMENT: This step MUST complete BEFORE step_1 begins.
    ...
  </process>
  <checkpoint>DEPRECATED - command file handles preflight</checkpoint>
</deprecated_step_0_preflight>
```

This deprecation was part of the "OpenAgents migration" (tasks 240-247) which moved workflow ownership from subagents to command files.

### 3. Task 335 Demonstrates the Issue

Task 335 (`/implement 335`) created implementation artifacts successfully but:
- Status remained [NOT STARTED] instead of [COMPLETED]
- Artifacts were not linked in TODO.md or state.json
- No git commit was created automatically
- User had to manually fix status and links

### 4. This Was Supposed to Be Fixed

Tasks 240-247 (OpenAgents migration) were supposed to fix this by:
- Moving workflow ownership from subagents to command files
- Implementing comprehensive preflight and postflight in command files
- Deprecating subagent preflight/postflight stages

However, **the orchestrator was never updated** to actually execute command file workflow stages.

## Impact

This affects **EVERY workflow command invocation**:

- ❌ All workflow commands fail to update status after completion
- ❌ Artifacts are created but not linked in TODO.md or state.json
- ❌ Git commits are not created automatically
- ❌ Users must manually fix status and links after every command execution
- ❌ This breaks the entire workflow automation system

## Solution

Create 4 tasks to systematically fix this architectural issue:

### Task 342: Research (4-6 hours)
Research how the orchestrator should execute command file workflow_execution stages:
- Analyze current orchestrator delegation mechanism
- Identify why command file stages are not being executed
- Compare with OpenAgents architecture (tasks 240-247)
- Design solution for parsing and executing workflow_execution stages
- Document stage sequencing, context passing, error handling, and rollback mechanisms

### Task 343: Design (3-4 hours)
Design comprehensive architecture for orchestrator to execute command file workflow_execution stages:
- Define stage parsing mechanism
- Design execution engine
- Specify context passing between stages
- Define error handling and rollback strategy
- Plan integration with existing delegation system

### Task 344: Implementation (8-12 hours)
Implement orchestrator workflow execution engine:
- Implement stage parser
- Implement execution engine
- Implement context passing mechanism
- Implement error handling and rollback
- Integrate with existing delegation system
- Ensure Stage 3.5 (Postflight) executes correctly for all workflow commands

### Task 345: Testing (4-6 hours)
Comprehensive testing of all workflow commands:
- Test `/implement`, `/research`, `/plan`, `/revise`
- Verify artifact creation and linking
- Verify status updates to completed markers
- Verify git commit creation
- Test error handling and rollback
- Validate Task 335 scenario is fixed

## Total Effort

**19-28 hours** across 4 tasks

## Priority

**HIGH** - This blocks all workflow automation and affects every command invocation.

## Dependencies

- Task 342: No dependencies (research)
- Task 343: Depends on 342 (design based on research)
- Task 344: Depends on 342, 343 (implement based on research and design)
- Task 345: Depends on 342, 343, 344 (test after implementation)

## Next Steps

1. Start with Task 342 (Research) to understand the current mechanism and design the solution
2. Proceed to Task 343 (Design) to create detailed architecture
3. Implement in Task 344 (Implementation)
4. Validate in Task 345 (Testing)

## References

- Command files: `.claude/command/implement.md`, `.claude/command/research.md`, etc.
- Subagents: `.claude/agent/subagents/implementer.md`, `.claude/agent/subagents/researcher.md`, etc.
- Orchestrator: `.claude/agent/orchestrator.md`
- OpenAgents migration: Tasks 240-247
- Task 335: Example of the issue
