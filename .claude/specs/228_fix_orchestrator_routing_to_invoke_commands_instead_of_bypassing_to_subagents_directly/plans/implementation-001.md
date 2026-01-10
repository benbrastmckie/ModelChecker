# Implementation Plan: Fix Orchestrator Routing to Invoke Commands Instead of Bypassing to Subagents

- **Task**: 228 - Fix orchestrator routing to invoke commands instead of bypassing to subagents directly
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Priority**: High
- **Complexity**: Medium
- **Dependencies**: None
- **Research Inputs**: .opencode/specs/228_fix_orchestrator_routing_to_invoke_commands_instead_of_bypassing_to_subagents_directly/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/tasks.md
- **Language**: markdown
- **Lean Intent**: false

## Overview

The orchestrator currently bypasses the command layer and directly invokes subagents (planner, researcher, task-executor, implementer), preventing command Stage 7 (Postflight) from executing. This causes ALL workflow commands (/plan, /research, /implement, /revise) to fail updating TODO.md and state.json despite successfully creating artifacts. The fix requires refactoring orchestrator Step 4 (PrepareRouting) and Step 7 (RouteToAgent) to invoke commands instead of subagents, allowing commands to execute their full 8-stage lifecycle including postflight status updates via status-sync-manager.

**Definition of Done**: Orchestrator routes to commands (/plan, /research, /implement, /revise) which then delegate to subagents internally. All workflow commands execute complete 8-stage lifecycle including Stage 7 postflight that updates TODO.md and state.json atomically.

## Goals & Non-Goals

**Goals**:
- Refactor orchestrator Step 4 to route to commands instead of subagents
- Refactor orchestrator Step 7 to invoke commands instead of subagents
- Simplify orchestrator Step 3 (language extraction moves to command layer)
- Ensure all workflow commands execute full 8-stage lifecycle
- Enable command Stage 7 postflight to invoke status-sync-manager
- Verify TODO.md and state.json updates occur after command completion
- Maintain backward compatibility with command argument parsing

**Non-Goals**:
- Modifying command file structure (already correct)
- Changing subagent implementations (already correct)
- Altering status-sync-manager logic (already correct)
- Implementing new commands or subagents
- Changing delegation depth limits

## Risks & Mitigations

- **Risk**: Command invocation mechanism may differ from subagent invocation, causing failures.  
  **Mitigation**: Research command invocation pattern in OpenCode documentation. Test with single command (/plan) before applying to all commands.

- **Risk**: Language extraction in orchestrator Step 3 may be needed for routing decisions.  
  **Mitigation**: Keep minimal language extraction in orchestrator for routing to correct command, but move detailed extraction to command Stage 2.

- **Risk**: Delegation depth counting may break if orchestrator → command counts as depth 1.  
  **Mitigation**: Set orchestrator → command as depth 0 (command layer is part of orchestrator's workflow execution, not separate delegation).

- **Risk**: Existing in-progress tasks may have stale status markers.  
  **Mitigation**: Test with fresh tasks first. Document manual cleanup procedure for stale tasks if needed.

- **Risk**: Commands may not be invokable by orchestrator (missing frontmatter or configuration).  
  **Mitigation**: Audit all command files for invokability requirements. Add necessary frontmatter if missing.

## Implementation Phases

### Phase 1: Audit Command Invokability [NOT STARTED]

- **Goal**: Verify all workflow commands can be invoked by orchestrator
- **Tasks**:
  - [ ] Read plan.md command file and check for agent frontmatter or invocation requirements
  - [ ] Read research.md command file and check for agent frontmatter or invocation requirements
  - [ ] Read implement.md command file and check for agent frontmatter or invocation requirements
  - [ ] Read revise.md command file and check for agent frontmatter or invocation requirements
  - [ ] Document any missing frontmatter or configuration needed
  - [ ] Add missing frontmatter to command files if needed
  - [ ] Verify commands accept $ARGUMENTS substitution pattern
- **Timing**: 0.5 hours
- **Validation**: All 4 command files have necessary frontmatter and accept $ARGUMENTS

### Phase 2: Refactor Orchestrator Step 4 (PrepareRouting) [NOT STARTED]

- **Goal**: Change routing logic to target commands instead of subagents
- **Tasks**:
  - [ ] Read orchestrator.md Step 4 (lines 219-332) to understand current routing logic
  - [ ] Replace subagent routing with command routing for /task → /task command
  - [ ] Replace subagent routing with command routing for /research → /research command
  - [ ] Replace subagent routing with command routing for /plan → /plan command
  - [ ] Replace subagent routing with command routing for /implement → /implement command
  - [ ] Replace subagent routing with command routing for /revise → /revise command
  - [ ] Replace subagent routing with command routing for /review → /review command
  - [ ] Replace subagent routing with command routing for /todo → /todo command
  - [ ] Replace subagent routing with command routing for /errors → /errors command
  - [ ] Update routing_logic section to specify target commands and arguments
  - [ ] Update logging statements to reflect command routing (e.g., "Routing to /plan command")
  - [ ] Remove language-based subagent selection (commands handle this in Stage 2)
  - [ ] Keep minimal language extraction for command routing validation if needed
- **Timing**: 1 hour
- **Validation**: Step 4 routing_logic section specifies commands as targets, not subagents

### Phase 3: Refactor Orchestrator Step 7 (RouteToAgent → RouteToCommand) [NOT STARTED]

- **Goal**: Change invocation pattern to invoke commands instead of subagents
- **Tasks**:
  - [ ] Read orchestrator.md Step 7 (lines 398-419) to understand current invocation pattern
  - [ ] Rename step from "RouteToAgent" to "RouteToCommand" for clarity
  - [ ] Replace task_tool(subagent_type=...) with command invocation pattern
  - [ ] Research correct command invocation syntax (load command file, substitute $ARGUMENTS, execute)
  - [ ] Implement command file loading mechanism
  - [ ] Implement $ARGUMENTS substitution mechanism
  - [ ] Implement command execution mechanism
  - [ ] Update delegation_depth to 0 for orchestrator → command (commands start depth at 1 for subagents)
  - [ ] Update delegation_path to ["orchestrator"] for command invocation
  - [ ] Update invocation_pattern section with command invocation code
  - [ ] Add command_execution section documenting 8-stage workflow execution
  - [ ] Update logging to reflect command invocation
- **Timing**: 1.5 hours
- **Validation**: Step 7 invokes commands using command invocation pattern, not task_tool with subagent_type

### Phase 4: Simplify Orchestrator Step 3 (CheckLanguage) [NOT STARTED]

- **Goal**: Remove or simplify language extraction since commands handle detailed extraction
- **Tasks**:
  - [ ] Read orchestrator.md Step 3 (lines 160-217) to understand current language extraction
  - [ ] Determine if orchestrator needs language for command routing decisions
  - [ ] If language not needed for routing: Remove Step 3 entirely
  - [ ] If language needed for routing: Simplify to minimal extraction (just read Language field)
  - [ ] Move detailed language extraction logic to command-lifecycle.md Stage 2 documentation
  - [ ] Update orchestrator.md to note that commands handle language-based subagent routing
  - [ ] Update Step 4 to use language from Step 3 only if Step 3 retained
  - [ ] Remove language_routing_map from Step 3 (commands have this logic)
- **Timing**: 0.5 hours
- **Validation**: Step 3 is removed or simplified to minimal extraction, with note that commands handle detailed routing

### Phase 5: Testing and Validation [NOT STARTED]

- **Goal**: Verify all workflow commands execute full lifecycle with status updates
- **Tasks**:
  - [ ] Create test task for /plan testing (or use existing task 224)
  - [ ] Execute /plan {task_number} and verify orchestrator routes to /plan command
  - [ ] Verify /plan command executes all 8 stages including Stage 7 postflight
  - [ ] Verify TODO.md updated to [PLANNED] with plan link
  - [ ] Verify state.json updated with status="planned" and plan_metadata
  - [ ] Verify git commit created for plan
  - [ ] Create test task for /research testing with language="lean"
  - [ ] Execute /research {task_number} and verify routing to /research command
  - [ ] Verify /research command routes to lean-research-agent (Stage 2 language extraction)
  - [ ] Verify TODO.md updated to [RESEARCHED] with research links
  - [ ] Verify state.json updated with status="researched"
  - [ ] Create test task for /implement testing with plan
  - [ ] Execute /implement {task_number} and verify routing to /implement command
  - [ ] Verify TODO.md updated to [COMPLETED] with checkmark
  - [ ] Verify state.json updated with status="completed"
  - [ ] Verify plan phases updated to [COMPLETED]
  - [ ] Test /revise command with plan revision
  - [ ] Verify TODO.md updated to [REVISED] with new plan link
  - [ ] Verify state.json plan_versions array updated
  - [ ] Document any failures or issues encountered
  - [ ] Fix any issues found during testing
- **Timing**: 1 hour
- **Validation**: All 4 workflow commands successfully update TODO.md and state.json after execution

### Phase 6: Documentation Update [NOT STARTED]

- **Goal**: Update documentation to reflect corrected orchestrator → command → subagent flow
- **Tasks**:
  - [ ] Update orchestrator.md with command invocation pattern documentation
  - [ ] Add section explaining command vs subagent delegation
  - [ ] Update ARCHITECTURE.md with corrected delegation flow diagram
  - [ ] Document orchestrator → command (depth 0) → subagent (depth 1) → specialist (depth 2) pattern
  - [ ] Add troubleshooting guide for routing issues
  - [ ] Update command-lifecycle.md if needed to clarify command invocation by orchestrator
  - [ ] Add note in orchestrator.md that commands handle language-based subagent routing
  - [ ] Document that orchestrator routes to commands, commands route to subagents
- **Timing**: 0.5 hours
- **Validation**: Documentation clearly explains orchestrator → command → subagent architecture

## Testing & Validation

**Unit Tests** (per phase):
- [ ] Phase 1: All command files have necessary frontmatter and accept $ARGUMENTS
- [ ] Phase 2: Step 4 routing_logic specifies commands as targets
- [ ] Phase 3: Step 7 uses command invocation pattern, not task_tool
- [ ] Phase 4: Step 3 removed or simplified with note about command-level routing
- [ ] Phase 5: All workflow commands update TODO.md and state.json
- [ ] Phase 6: Documentation reflects corrected architecture

**Integration Tests**:
- [ ] /plan command: Creates plan artifact, updates TODO.md to [PLANNED], updates state.json, creates git commit
- [ ] /research command (lean): Creates research artifact, routes to lean-research-agent, updates TODO.md to [RESEARCHED], updates state.json
- [ ] /research command (general): Creates research artifact, routes to researcher, updates TODO.md to [RESEARCHED], updates state.json
- [ ] /implement command (with plan): Executes phases, updates TODO.md to [COMPLETED], updates state.json, updates plan phases, creates git commit
- [ ] /implement command (without plan): Executes direct implementation, updates TODO.md to [COMPLETED], updates state.json, creates git commit
- [ ] /revise command: Creates revised plan, updates TODO.md to [REVISED], updates state.json plan_versions, creates git commit

**Regression Tests**:
- [ ] Existing tasks with [RESEARCHED] status remain unchanged
- [ ] Existing tasks with [PLANNED] status remain unchanged
- [ ] Delegation depth limits still enforced (max depth 3)
- [ ] Cycle detection still works
- [ ] Error handling still works for invalid task numbers

## Artifacts & Outputs

- **Modified Files**:
  - .opencode/agent/orchestrator.md (Step 4, Step 7, possibly Step 3)
  - .opencode/command/plan.md (frontmatter if needed)
  - .opencode/command/research.md (frontmatter if needed)
  - .opencode/command/implement.md (frontmatter if needed)
  - .opencode/command/revise.md (frontmatter if needed)
  - .opencode/ARCHITECTURE.md (delegation flow diagram)

- **Documentation**:
  - Updated orchestrator.md with command invocation pattern
  - Updated ARCHITECTURE.md with corrected delegation flow
  - Troubleshooting guide for routing issues

- **Testing Artifacts**:
  - Test task entries in TODO.md for validation
  - Test artifacts created during Phase 5 testing

## Rollback/Contingency

**If command invocation fails**:
1. Revert orchestrator.md Step 4 and Step 7 to previous version
2. Investigate command file issues (missing frontmatter, incorrect argument parsing)
3. Fix command files if needed
4. Retry orchestrator changes

**If status updates still fail after fix**:
1. This indicates issue with status-sync-manager (Task 227)
2. Verify status-sync-manager is being invoked by commands
3. Investigate status-sync-manager TODO.md update logic
4. Task 227 can proceed with investigation

**If delegation depth breaks**:
1. Revert delegation_depth changes in Step 7
2. Re-evaluate depth counting logic
3. Adjust depth counting to maintain max depth 3 limit

**Manual cleanup for stale tasks**:
- If tasks stuck in [RESEARCHING], [PLANNING], [IMPLEMENTING], [REVISING]:
  1. Manually update TODO.md status to [NOT STARTED] or appropriate status
  2. Manually update state.json status field
  3. Re-run workflow command to test fix

## Notes

**Research Integration**:
- Research report (research-001.md) provides comprehensive root cause analysis
- Key finding: Orchestrator Step 7 routes to subagents instead of commands
- Expected flow: User → Orchestrator → Command → Subagent → status-sync-manager
- Current broken flow: User → Orchestrator → Subagent (no postflight, no status updates)

**Relationship to Other Tasks**:
- Task 227 (status-sync-manager failures) depends on this fix
- Task 227 assumes status-sync-manager is invoked but failing
- This task reveals status-sync-manager is never invoked because commands are bypassed
- Task 228 must complete FIRST before Task 227 can investigate remaining update failures

**Critical Success Factors**:
- Commands must be invokable by orchestrator (frontmatter, argument parsing)
- Command invocation pattern must work correctly (load, substitute, execute)
- Delegation depth must remain at 0 for orchestrator → command
- Commands must execute full 8-stage lifecycle including postflight
- status-sync-manager must be invoked by command Stage 7
- TODO.md and state.json must update atomically after command completion
