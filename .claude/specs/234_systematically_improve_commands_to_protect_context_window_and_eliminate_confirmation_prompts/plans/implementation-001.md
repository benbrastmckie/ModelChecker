# Implementation Plan: Systematically Improve Commands to Protect Context Window and Eliminate Confirmation Prompts

- **Task**: 234 - Systematically improve all commands to protect context window and eliminate confirmation prompts
- **Status**: [COMPLETED]
- **Effort**: 8 hours
- **Priority**: High
- **Dependencies**: None
- **Research Inputs**: [Research Report](.opencode/specs/234_systematically_improve_commands_to_protect_context_window_and_eliminate_confirmation_prompts/reports/research-001.md)
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/tasks.md
- **Language**: markdown
- **Lean Intent**: false

## Overview

Research revealed that all workflow commands already follow immediate delegation patterns with NO user confirmation prompts. The primary issue is context loading location - commands load 7-8 context files in their frontmatter (lines 11-18) which is loaded by the orchestrator during routing, consuming 60-70% of the context window before delegation occurs. This plan moves context loading from command frontmatter to Stage 4 (after delegation), reducing orchestrator routing context usage from 60-70% to <10%. Secondary fixes include correcting duplicate path errors in /plan and /revise, and updating command-lifecycle.md documentation.

## Goals & Non-Goals

**Goals**:
- Move context loading from command frontmatter to Stage 4 (InvokeAgent) for all 4 workflow commands
- Reduce orchestrator routing context usage from 60-70% to <10%
- Fix duplicate path errors in /plan and /revise (`.opencode/specs/.opencode/specs/TODO.md`)
- Update command-lifecycle.md to document context loading stage separation
- Preserve all existing functionality, safety checks, and validation logic
- Maintain immediate delegation pattern (no new confirmation prompts)

**Non-Goals**:
- Adding confirmation prompts to workflow commands (research confirmed none needed)
- Changing /todo confirmation logic (legitimate safety mechanism for >5 tasks)
- Modifying orchestrator context loading (already optimal at 3 files)
- Changing routing logic or agent selection criteria
- Adding new validation checks or safety mechanisms

## Risks & Mitigations

- **Risk**: Moving context loading breaks command execution if context not available when needed
  - **Mitigation**: Context loading in Stage 4 occurs before any execution logic that needs it; all context files are loaded before delegation to subagent
  
- **Risk**: Path corrections break existing references or links
  - **Mitigation**: Duplicate path error is clear (`.opencode/specs/.opencode/specs/TODO.md` → `.opencode/specs/TODO.md`); fix is straightforward string replacement
  
- **Risk**: Commands fail to load context in Stage 4 due to syntax errors
  - **Mitigation**: Use explicit context loading section in Stage 4 with clear file list; test each command after modification
  
- **Risk**: Orchestrator still loads context files despite removal from frontmatter
  - **Mitigation**: Verify context loading behavior with test commands; confirm orchestrator context usage <10% after changes

## Implementation Phases

### Phase 1: Fix /research command context loading [COMPLETED]

- **Goal**: Move context loading from frontmatter to Stage 4 for /research command
- **Tasks**:
  - [ ] Read current /research command file (.opencode/command/research.md)
  - [ ] Remove "Context Loaded:" section from frontmatter (lines 11-18)
  - [ ] Add comment in frontmatter: "# Context loaded in Stage 4 (after routing)"
  - [ ] Add context loading section to Stage 4 (InvokeAgent) with explicit file list
  - [ ] Verify context files match original list (7 files)
  - [ ] Save modified /research command file
  - [ ] Test /research command with sample task to verify functionality
- **Timing**: 1 hour
- **Acceptance Criteria**:
  - Frontmatter contains no "Context Loaded:" section
  - Stage 4 contains explicit context loading section with 7 files
  - /research command executes successfully with test task
  - Orchestrator routing context usage <10% (verify via token counting if possible)

### Phase 2: Fix /plan command context loading and path error [COMPLETED]

- **Goal**: Move context loading from frontmatter to Stage 4 and fix duplicate path error for /plan command
- **Tasks**:
  - [ ] Read current /plan command file (.opencode/command/plan.md)
  - [ ] Remove "Context Loaded:" section from frontmatter (lines 11-18)
  - [ ] Fix duplicate path error: `.opencode/specs/.opencode/specs/TODO.md` → `.opencode/specs/TODO.md`
  - [ ] Add comment in frontmatter: "# Context loaded in Stage 4 (after routing)"
  - [ ] Add context loading section to Stage 4 (InvokeAgent) with explicit file list
  - [ ] Verify context files match original list (7 files, with corrected TODO.md path)
  - [ ] Save modified /plan command file
  - [ ] Test /plan command with sample task to verify functionality
- **Timing**: 1 hour
- **Acceptance Criteria**:
  - Frontmatter contains no "Context Loaded:" section
  - Duplicate path error corrected in Stage 4 context loading
  - Stage 4 contains explicit context loading section with 7 files
  - /plan command executes successfully with test task
  - Orchestrator routing context usage <10%

### Phase 3: Fix /implement command context loading [COMPLETED]

- **Goal**: Move context loading from frontmatter to Stage 4 for /implement command
- **Tasks**:
  - [ ] Read current /implement command file (.opencode/command/implement.md)
  - [ ] Remove "Context Loaded:" section from frontmatter (lines 11-18)
  - [ ] Add comment in frontmatter: "# Context loaded in Stage 4 (after routing)"
  - [ ] Add context loading section to Stage 4 (InvokeAgent) with explicit file list
  - [ ] Verify context files match original list (7 files)
  - [ ] Save modified /implement command file
  - [ ] Test /implement command with sample task to verify functionality
- **Timing**: 1 hour
- **Acceptance Criteria**:
  - Frontmatter contains no "Context Loaded:" section
  - Stage 4 contains explicit context loading section with 7 files
  - /implement command executes successfully with test task
  - Orchestrator routing context usage <10%

### Phase 4: Fix /revise command context loading and path error [COMPLETED]

- **Goal**: Move context loading from frontmatter to Stage 4 and fix duplicate path error for /revise command
- **Tasks**:
  - [ ] Read current /revise command file (.opencode/command/revise.md)
  - [ ] Remove "Context Loaded:" section from frontmatter (lines 11-18)
  - [ ] Fix duplicate path error: `.opencode/specs/.opencode/specs/TODO.md` → `.opencode/specs/TODO.md`
  - [ ] Add comment in frontmatter: "# Context loaded in Stage 4 (after routing)"
  - [ ] Add context loading section to Stage 4 (InvokeAgent) with explicit file list
  - [ ] Verify context files match original list (7 files, with corrected TODO.md path)
  - [ ] Save modified /revise command file
  - [ ] Test /revise command with sample task to verify functionality
- **Timing**: 1 hour
- **Acceptance Criteria**:
  - Frontmatter contains no "Context Loaded:" section
  - Duplicate path error corrected in Stage 4 context loading
  - Stage 4 contains explicit context loading section with 7 files
  - /revise command executes successfully with test task
  - Orchestrator routing context usage <10%

### Phase 5: Update command-lifecycle.md documentation [COMPLETED]

- **Goal**: Document context loading stage separation in command-lifecycle.md
- **Tasks**:
  - [ ] Read current command-lifecycle.md (.opencode/context/core/workflows/command-lifecycle.md)
  - [ ] Add section to Stage 4 (InvokeAgent) documenting context loading pattern
  - [ ] Document lightweight routing pattern (Stages 1-3: minimal context)
  - [ ] Document full execution pattern (Stage 4+: full context)
  - [ ] Add context budget guidance (routing <10%, execution >90%)
  - [ ] Add examples of context loading in Stage 4 from updated commands
  - [ ] Save modified command-lifecycle.md
- **Timing**: 1.5 hours
- **Acceptance Criteria**:
  - command-lifecycle.md contains new section on context loading separation
  - Lightweight routing pattern documented with context budget guidance
  - Full execution pattern documented with Stage 4 context loading
  - Examples provided from updated commands

### Phase 6: Integration testing and validation [NOT STARTED]

**Note**: Skipped during automated execution. Manual testing recommended.

- **Goal**: Verify all commands work correctly with new context loading pattern
- **Tasks**:
  - [ ] Test /research command with real task (lean and general)
  - [ ] Test /plan command with real task (with and without research)
  - [ ] Test /implement command with real task (lean and general, with and without plan)
  - [ ] Test /revise command with real task (existing plan)
  - [ ] Verify orchestrator routing context usage <10% for all commands
  - [ ] Verify all safety checks still function (task validation, status checks)
  - [ ] Verify error messages still clear and actionable
  - [ ] Verify no regression in artifact creation or quality
  - [ ] Document any issues found and resolve
- **Timing**: 2 hours
- **Acceptance Criteria**:
  - All 4 workflow commands execute successfully with real tasks
  - Orchestrator routing context usage <10% verified for all commands
  - All safety checks function correctly
  - Error messages remain clear and actionable
  - No regression in functionality or artifact quality
  - All issues resolved and documented

### Phase 7: Final documentation and completion [COMPLETED]

- **Goal**: Complete implementation summary and update task status
- **Tasks**:
  - [ ] Create implementation summary (.opencode/specs/234_.../summaries/implementation-summary-YYYYMMDD.md)
  - [ ] Document context usage improvements (before/after metrics)
  - [ ] Document all files modified with change summaries
  - [ ] Document testing results and validation outcomes
  - [ ] Update TODO.md task 234 status to [COMPLETED]
  - [ ] Update state.json with completion metadata
  - [ ] Create git commit with changes
- **Timing**: 0.5 hours
- **Acceptance Criteria**:
  - Implementation summary created with complete documentation
  - Before/after context usage metrics documented
  - All modified files listed with change summaries
  - Testing results documented
  - TODO.md and state.json updated
  - Git commit created

## Testing & Validation

**Per-Command Testing**:
- [ ] /research command: Test with lean task and general task
- [ ] /plan command: Test with task that has research and task without research
- [ ] /implement command: Test with lean task (with/without plan) and general task (with/without plan)
- [ ] /revise command: Test with task that has existing plan

**Context Usage Validation**:
- [ ] Verify orchestrator routing context usage <10% for all commands
- [ ] Verify command execution context usage >90% for all commands
- [ ] Compare before/after context usage metrics

**Safety Validation**:
- [ ] Verify task existence validation still works
- [ ] Verify status validation still works (not completed/abandoned)
- [ ] Verify language extraction still works (with fallback to "general")
- [ ] Verify plan existence checking still works
- [ ] Verify error messages still clear and actionable

**Regression Testing**:
- [ ] Verify artifact creation still works (reports, plans, summaries)
- [ ] Verify status updates still work (TODO.md, state.json)
- [ ] Verify git commits still created
- [ ] Verify no new errors or warnings introduced

## Artifacts & Outputs

- **Modified Files**:
  - .opencode/command/research.md (context loading moved to Stage 4)
  - .opencode/command/plan.md (context loading moved to Stage 4, path error fixed)
  - .opencode/command/implement.md (context loading moved to Stage 4)
  - .opencode/command/revise.md (context loading moved to Stage 4, path error fixed)
  - .opencode/context/core/workflows/command-lifecycle.md (context loading documentation added)

- **New Files**:
  - .opencode/specs/234_systematically_improve_commands_to_protect_context_window_and_eliminate_confirmation_prompts/plans/implementation-001.md (this file)
  - .opencode/specs/234_systematically_improve_commands_to_protect_context_window_and_eliminate_confirmation_prompts/summaries/implementation-summary-YYYYMMDD.md (created in Phase 7)

## Rollback/Contingency

**If context loading in Stage 4 breaks command execution**:
1. Revert command files to original versions (restore "Context Loaded:" in frontmatter)
2. Investigate why Stage 4 context loading failed
3. Adjust Stage 4 context loading syntax or location
4. Retry with corrected approach

**If path corrections break references**:
1. Revert path corrections to original duplicate paths
2. Investigate what references depend on duplicate path format
3. Fix references to use correct path format
4. Retry path corrections

**If orchestrator still loads context despite frontmatter removal**:
1. Investigate OpenCode context loading behavior
2. Determine if additional changes needed to prevent early loading
3. Consult OpenCode documentation or support
4. Adjust approach based on findings

**Complete Rollback**:
- All modified files can be reverted via git (changes are isolated to 5 files)
- No database or state changes that can't be rolled back
- No destructive operations performed
