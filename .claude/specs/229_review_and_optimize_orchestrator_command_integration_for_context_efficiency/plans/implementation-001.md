# Implementation Plan: Fix Orchestrator-Command Integration Architecture

- **Task**: 229 - Review and optimize orchestrator-command integration for context efficiency
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Priority**: High
- **Complexity**: Medium
- **Dependencies**: None (Tasks 227 and 228 are duplicates/subsumed by this architectural fix)
- **Research Inputs**: .opencode/specs/229_review_and_optimize_orchestrator_command_integration_for_context_efficiency/reports/research-001.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/workflows/command-lifecycle.md
  - .opencode/context/core/workflows/subagent-delegation-guide.md
- **Language**: markdown
- **Lean Intent**: false

## Overview

Research has identified a **critical architectural flaw** where orchestrator.md routes directly to subagents instead of to commands, bypassing the entire command lifecycle (8 stages), causing 100% workflow failure for status updates, 60-70% context bloat, and breaking the intended 3-layer architecture. The fix is straightforward: modify orchestrator Step 7 to route to commands (/plan, /research, etc.) which then delegate to subagents internally, ensuring full workflow execution including preflight/postflight procedures and status-sync-manager integration.

**Current (Broken)**: User → Orchestrator → Subagent (direct bypass)

**Expected (Correct)**: User → Orchestrator → Command → Subagent

This fix resolves tasks 227 and 228 as side effects and establishes the correct architectural layering for scalable, maintainable agent system.

## Goals & Non-Goals

**Goals**:
- Refactor orchestrator Step 4 (PrepareRouting) to route to commands instead of subagents
- Refactor orchestrator Step 7 (RouteToAgent → RouteToCommand) to invoke commands
- Remove/simplify orchestrator Step 3 (CheckLanguage) - commands handle language extraction
- Reduce orchestrator context loading to core standards only (3 files instead of ~20)
- Ensure all 4 workflow commands execute full 8-stage lifecycle
- Achieve 60-70% reduction in orchestrator context window
- Ensure 100% workflow completion (all postflight procedures execute)
- Resolve tasks 227 and 228 architecturally

**Non-Goals**:
- Modifying command file structure (already correct per command-lifecycle.md)
- Changing subagent implementations (already correct)
- Altering status-sync-manager logic (already correct)
- Implementing new commands or subagents
- Changing delegation depth limits

## Risks & Mitigations

- **Risk**: Breaking existing workflows during orchestrator refactoring.  
  **Mitigation**: Test each command individually with real tasks. Rollback plan ready.

- **Risk**: Commands may not be invokable by orchestrator (missing frontmatter).  
  **Mitigation**: Phase 1 audits command invocability and adds necessary frontmatter.

- **Risk**: Context loading changes break command execution.  
  **Mitigation**: Phase 2 reduces orchestrator context carefully with validation.

- **Risk**: Routing changes cause 404 or delegation failures.  
  **Mitigation**: Phase 3 documents command invocation pattern and tests thoroughly.

## Implementation Phases

### Phase 1: Audit Command Invocability and Add Frontmatter [NOT STARTED]

- **Goal**: Ensure all commands can be invoked by orchestrator
- **Tasks**:
  - [ ] Read plan.md command file and check for agent frontmatter
  - [ ] Read research.md command file and check for agent frontmatter
  - [ ] Read implement.md command file and check for agent frontmatter
  - [ ] Read revise.md command file and check for agent frontmatter
  - [ ] Read review.md command file and check for agent frontmatter
  - [ ] Document current frontmatter status for each command
  - [ ] Add missing frontmatter if needed (agent: orchestrator, mode: all)
  - [ ] Verify commands accept $ARGUMENTS substitution pattern
  - [ ] Document command invocation requirements
- **Timing**: 0.5 hours
- **Acceptance Criteria**:
  - All 5 command files have necessary frontmatter
  - All commands accept $ARGUMENTS pattern
  - Command invocability documented

### Phase 2: Reduce Orchestrator Context Loading [NOT STARTED]

- **Goal**: Remove project-specific and language-specific context from orchestrator
- **Tasks**:
  - [ ] Document current orchestrator context loading (lines 16-36)
  - [ ] Remove Level 2 context loading (project-specific by language)
  - [ ] Keep Level 1 context only: return-format.md, delegation-guide.md, status-markers.md
  - [ ] Remove language routing map from orchestrator context
  - [ ] Remove validation logic context (commands handle validation)
  - [ ] Update orchestrator.md context_loading section
  - [ ] Measure context reduction (before/after token counts)
  - [ ] Document new minimal context loading pattern
- **Timing**: 0.5 hours
- **Acceptance Criteria**:
  - Orchestrator loads only 3 core context files
  - Project-specific context removed
  - Context reduction measured (~60-70% expected)
  - Context loading pattern documented

### Phase 3: Refactor Orchestrator Step 7 (RouteToCommand) [NOT STARTED]

- **Goal**: Change invocation pattern from subagents to commands
- **Tasks**:
  - [ ] Read orchestrator.md Step 7 (RouteToAgent lines 398-419)
  - [ ] Rename step from "RouteToAgent" to "RouteToCommand"
  - [ ] Replace task_tool(subagent_type=...) with command invocation pattern
  - [ ] Document command invocation syntax (load command file, substitute $ARGUMENTS, execute)
  - [ ] Implement command file loading mechanism
  - [ ] Implement $ARGUMENTS substitution mechanism
  - [ ] Implement command execution mechanism (execute 8-stage workflow)
  - [ ] Set delegation_depth = 0 for orchestrator → command
  - [ ] Set delegation_path = ["orchestrator"] for command invocation
  - [ ] Update invocation_pattern section with command invocation code
  - [ ] Add command_execution section documenting 8-stage workflow
  - [ ] Update logging to reflect command invocation
- **Timing**: 1.5 hours
- **Acceptance Criteria**:
  - Step 7 renamed to "RouteToCommand"
  - Step 7 invokes commands using correct invocation pattern
  - delegation_depth = 0 for orchestrator → command
  - Command execution documented

### Phase 4: Refactor Orchestrator Step 4 (PrepareRouting) [NOT STARTED]

- **Goal**: Change routing targets from subagents to commands
- **Tasks**:
  - [ ] Read orchestrator.md Step 4 (lines 219-332)
  - [ ] Replace /task routing: atomic-task-numberer → /task command
  - [ ] Replace /research routing: lean-research-agent/researcher → /research command
  - [ ] Replace /plan routing: planner → /plan command
  - [ ] Replace /implement routing: task-executor/implementer → /implement command
  - [ ] Replace /revise routing: planner → /revise command
  - [ ] Replace /review routing: reviewer → /review command
  - [ ] Replace /todo routing: todo-manager → /todo command
  - [ ] Replace /errors routing: error-diagnostics-agent → /errors command
  - [ ] Update routing_logic section to specify commands as targets
  - [ ] Update logging statements to reflect command routing
  - [ ] Remove language-based subagent selection (commands handle this)
  - [ ] Document routing map: command → arguments pattern
- **Timing**: 1 hour
- **Acceptance Criteria**:
  - Step 4 routing_logic specifies commands as targets
  - All 8 workflow commands have routing entries
  - Language-based subagent selection removed
  - Routing map documented

### Phase 5: Simplify Orchestrator Step 3 (CheckLanguage) [NOT STARTED]

- **Goal**: Remove or simplify language extraction since commands handle it
- **Tasks**:
  - [ ] Read orchestrator.md Step 3 (lines 160-217)
  - [ ] Determine if language needed for command routing (answer: NO)
  - [ ] Remove Step 3 CheckLanguage entirely
  - [ ] Update Step numbering (Step 4 becomes Step 3, etc.)
  - [ ] Add note that commands handle language extraction in Stage 2
  - [ ] Document rationale: language extraction belongs in command layer
  - [ ] Update orchestrator.md process_flow section
  - [ ] Remove language_routing_map references
- **Timing**: 0.5 hours
- **Acceptance Criteria**:
  - Step 3 CheckLanguage removed
  - Step numbering updated
  - Rationale documented
  - Commands noted as handling language extraction

### Phase 6: Testing and Validation [NOT STARTED]

- **Goal**: Verify all workflow commands execute full lifecycle with status updates
- **Tasks**:
  - [ ] Test /plan 229 (this task): Verify orchestrator routes to /plan command
  - [ ] Verify /plan command executes all 8 stages including postflight
  - [ ] Verify TODO.md updated to [PLANNED] with plan link
  - [ ] Verify state.json updated with status="planned" and plan_metadata
  - [ ] Verify git commit created
  - [ ] Create test task for /research with language="lean"
  - [ ] Test /research: Verify routing to /research command → lean-research-agent
  - [ ] Verify TODO.md updated to [RESEARCHED] with research links
  - [ ] Verify state.json updated with status="researched"
  - [ ] Create test task for /implement with plan
  - [ ] Test /implement: Verify routing to /implement command → task-executor
  - [ ] Verify TODO.md updated to [COMPLETED] with checkmark
  - [ ] Verify state.json updated with status="completed"
  - [ ] Verify plan phases updated to [COMPLETED]
  - [ ] Test /revise command
  - [ ] Verify TODO.md updated to [REVISED] with new plan link
  - [ ] Verify state.json plan_versions array updated
  - [ ] Measure orchestrator context window reduction
  - [ ] Document test results
  - [ ] Fix any issues found during testing
- **Timing**: 1.5 hours
- **Acceptance Criteria**:
  - All 4 workflow commands successfully execute full lifecycle
  - TODO.md and state.json updated for all commands
  - Git commits created
  - Context window reduction measured (target: 60-70%)
  - Test results documented

### Phase 7: Documentation and Integration [NOT STARTED]

- **Goal**: Update documentation to reflect corrected architecture
- **Tasks**:
  - [ ] Update orchestrator.md with command invocation pattern
  - [ ] Add section explaining command vs subagent delegation
  - [ ] Document orchestrator → command (depth 0) → subagent (depth 1) pattern
  - [ ] Update command-lifecycle.md if needed (add orchestrator integration section)
  - [ ] Add note in orchestrator.md that commands handle language routing
  - [ ] Document that orchestrator routes to commands, commands route to subagents
  - [ ] Create architecture diagram showing correct 3-layer flow
  - [ ] Update ARCHITECTURE.md if it exists
  - [ ] Add troubleshooting guide for routing issues
  - [ ] Document context window reduction measurements
  - [ ] Document resolution of tasks 227 and 228
  - [ ] Create integration testing checklist for future commands
- **Timing**: 0.5 hours
- **Acceptance Criteria**:
  - orchestrator.md documents command invocation pattern
  - command-lifecycle.md includes orchestrator integration section
  - Architecture diagram created
  - Tasks 227 and 228 resolution documented
  - Integration patterns documented

## Testing & Validation

**Unit Tests** (per phase):
- [ ] Phase 1: All command files have frontmatter and accept $ARGUMENTS
- [ ] Phase 2: Orchestrator context reduced to 3 files, reduction measured
- [ ] Phase 3: Step 7 uses command invocation pattern
- [ ] Phase 4: Step 4 routing_logic specifies commands
- [ ] Phase 5: Step 3 removed, commands handle language
- [ ] Phase 6: All workflow commands update TODO.md and state.json
- [ ] Phase 7: Documentation reflects corrected architecture

**Integration Tests**:
- [ ] /plan: Creates plan, updates TODO.md to [PLANNED], updates state.json, creates git commit
- [ ] /research (lean): Routes to /research → lean-research-agent, updates TODO.md to [RESEARCHED]
- [ ] /research (general): Routes to /research → researcher, updates TODO.md to [RESEARCHED]
- [ ] /implement (with plan): Executes phases, updates TODO.md to [COMPLETED], updates plan phases
- [ ] /implement (without plan): Executes direct, updates TODO.md to [COMPLETED]
- [ ] /revise: Creates revised plan, updates TODO.md to [REVISED], updates plan_versions

**Regression Tests**:
- [ ] Existing tasks with [RESEARCHED] status remain unchanged
- [ ] Existing tasks with [PLANNED] status remain unchanged
- [ ] Delegation depth limits still enforced (max depth 3)
- [ ] Cycle detection still works
- [ ] Error handling still works

## Artifacts & Outputs

**Modified Files**:
- .opencode/agent/orchestrator.md (Steps 3, 4, 7, context loading)
- .opencode/command/plan.md (frontmatter if needed)
- .opencode/command/research.md (frontmatter if needed)
- .opencode/command/implement.md (frontmatter if needed)
- .opencode/command/revise.md (frontmatter if needed)
- .opencode/command/review.md (frontmatter if needed)
- .opencode/context/core/workflows/command-lifecycle.md (orchestrator integration section)

**Documentation**:
- Updated orchestrator.md with command invocation pattern
- Architecture diagram showing correct 3-layer flow
- Troubleshooting guide for routing issues
- Context window reduction measurements

**Testing Artifacts**:
- Test task entries in TODO.md for validation
- Test artifacts created during Phase 6 testing

## Rollback/Contingency

**If command invocation fails**:
1. Revert orchestrator.md Steps 4 and 7 to previous version
2. Investigate command file issues (missing frontmatter, incorrect argument parsing)
3. Fix command files if needed
4. Retry orchestrator changes

**If status updates still fail after fix**:
1. This would indicate issue with commands not delegating to status-sync-manager
2. Verify status-sync-manager is being invoked by commands (should be per command-lifecycle.md)
3. Investigate command Stage 7 (Postflight) implementations
4. Task 227 plan may need revision if commands themselves have delegation gaps

**If context reduction breaks workflows**:
1. Revert orchestrator context loading changes
2. Re-evaluate which context is truly needed by orchestrator vs commands
3. Gradually reduce context with testing at each step

**If routing changes cause errors**:
1. Revert orchestrator.md Step 4 and Step 7
2. Debug command invocation mechanism
3. Verify command files are invokable
4. Retry with corrected invocation pattern

## Notes

**Research Integration**:
- Research report (research-001.md) provides comprehensive analysis
- Key finding: Orchestrator bypasses commands, causing 100% workflow failure
- Expected outcome: 60-70% context reduction, 100% workflow completion

**Relationship to Other Tasks**:
- **Task 228**: Duplicate - describes same root cause (orchestrator routing)
- **Task 227**: Related - assumes status-sync-manager is invoked but failing
- Both tasks resolve architecturally when commands execute full lifecycle
- Task 228 can be marked as duplicate/resolved by 229
- Task 227 may need revision if status-sync-manager issues remain after fix

**Critical Success Factors**:
- Commands must be invokable by orchestrator (frontmatter verified in Phase 1)
- Command invocation pattern must work correctly (implemented in Phase 3)
- Orchestrator context must reduce without breaking functionality (Phase 2)
- All commands must execute full 8-stage lifecycle (validated in Phase 6)
- status-sync-manager must be invoked by command Stage 7 (per command-lifecycle.md)

**Expected Outcomes**:
1. [PASS] 60-70% reduction in orchestrator context window
2. [PASS] 100% workflow completion (all stages execute)
3. [PASS] Clear 3-layer architecture (orchestrator → command → subagent)
4. [PASS] Context loaded exactly where needed
5. [PASS] All status updates via status-sync-manager
6. [PASS] Proper git commit integration
7. [PASS] Resolves tasks 227 and 228 architecturally
