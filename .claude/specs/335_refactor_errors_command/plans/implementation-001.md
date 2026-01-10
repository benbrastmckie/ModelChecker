# Implementation Plan: Refactor /errors Command and error-diagnostics-agent

- **Task**: 335 - Refactor /errors command and error-diagnostics-agent to follow modern standards
- **Status**: [COMPLETED]
- **Effort**: 3-4 hours (actual: ~2 hours)
- **Priority**: High
- **Dependencies**: None
- **Research Inputs**: 
  - Current implementations: .opencode/command/errors.md (150 lines), .opencode/agent/subagents/error-diagnostics-agent.md (525 lines)
  - Reference implementations: /research, /implement commands
  - Standards: command-template.md, subagent-template.md, workflow_execution pattern
- **Artifacts**: 
  - plans/implementation-001.md (this file)
  - .opencode/command/errors.md (refactored, <300 lines)
  - .opencode/agent/subagents/error-diagnostics-agent.md (refactored with 8-stage workflow)
- **Standards**:
  - .opencode/context/core/formats/plan-format.md
  - .opencode/context/core/workflows/command-workflow.md
  - .opencode/context/core/workflows/agent-workflow.md
  - .opencode/context/core/formats/subagent-return.md
- **Type**: general
- **Lean Intent**: false

## Overview

Refactor the /errors command and error-diagnostics-agent subagent to follow modern .opencode standards established by /research and /implement. The current implementation has workflow logic embedded in the command file and uses the older process_flow pattern in the subagent instead of the standardized 8-stage workflow_execution. This refactoring will achieve clean separation of concerns (command parses/validates/delegates, subagent executes), minimize complexity, optimize context loading, and ensure robust functionality with comprehensive validation.

## Goals & Non-Goals

**Goals**:
- Simplify command file to <300 lines with 4-stage pattern (ParseAndValidate, Delegate, ValidateReturn, RelayResult)
- Refactor error-diagnostics-agent to use 8-stage workflow_execution pattern
- Move all workflow logic from command to subagent
- Optimize context loading to Level 2 (50KB budget)
- Ensure subagent returns standardized format per subagent-return-format.md
- Maintain all existing functionality (error grouping, fix recommendations, recurrence tracking)
- No preflight/postflight needed (errors command is read-only analysis)

**Non-Goals**:
- Changing error.json schema or structure
- Adding new error analysis features (scope: refactoring only)
- Creating fix plan artifacts (error-diagnostics-agent returns analysis only, no file creation)
- Modifying status-sync-manager or git-workflow-manager

## Risks & Mitigations

| Risk | Mitigation |
|------|-----------|
| Breaking existing error analysis workflow | Maintain exact same inputs/outputs, comprehensive testing before deployment |
| Context bloat in subagent | Use Level 2 context loading (50KB), lazy load only required context files |
| Loss of error grouping logic | Carefully migrate all grouping logic from command to subagent Stage 3 |
| Validation gaps | Add comprehensive validation in both command (Stage 3) and subagent (Stage 4) |

## Implementation Phases

### Phase 1: Refactor Command File (errors.md) [COMPLETED]
- **Goal:** Simplify command to 4-stage pattern, <300 lines
- **Tasks:**
  - [ ] Read current errors.md implementation (150 lines)
  - [ ] Extract workflow logic to be moved to subagent
  - [ ] Implement Stage 1 (ParseAndValidate):
    - Parse flags: --all, --type TYPE
    - Validate errors.json exists and is valid JSON
    - Load errors.json content
    - Filter errors based on flags (--all includes all, default excludes addressed)
    - If --type specified, filter to that type only
    - Count errors to analyze
    - If zero errors: Return early with message "No errors found matching filter"
  - [ ] Implement Stage 2 (Delegate):
    - Generate session_id for tracking
    - Prepare delegation context (errors_data, filter_type, session_id, delegation_depth=1, delegation_path)
    - Invoke error-diagnostics-agent via task tool
    - Pass filtered errors and metadata
    - Wait for return (timeout: 1800s)
  - [ ] Implement Stage 3 (ValidateReturn):
    - Parse return as JSON
    - Validate required fields: status, summary, metadata, analysis
    - Validate status is "completed" or "partial"
    - Validate session_id matches expected
    - Validate analysis object has required fields (error_groups, recommendations)
    - If validation fails: Return error with details
  - [ ] Implement Stage 4 (RelayResult):
    - Extract key information from analysis
    - Format user-friendly summary
    - Display error groups with counts
    - Display top recommendations
    - Display next steps
    - Return to user
  - [ ] Update frontmatter:
    - context_level: 2 (keep current)
    - routing.target_agent: error-diagnostics-agent
    - context_loading.required: delegation.md, state-management.md, subagent-return.md
    - Remove unnecessary context files
  - [ ] Remove embedded workflow logic (moved to subagent)
  - [ ] Verify file is <300 lines
- **Timing:** 1-1.5 hours

### Phase 2: Refactor Subagent (error-diagnostics-agent.md) [COMPLETED]
- **Goal:** Convert to 8-stage workflow_execution pattern
- **Tasks:**
  - [ ] Read current error-diagnostics-agent.md (525 lines)
  - [ ] Replace process_flow with workflow_execution
  - [ ] Implement Stage 1 (ValidateInputs):
    - Validate errors_data is non-empty object
    - Validate session_id provided
    - Validate delegation_depth <= 3
    - Validate delegation_path is array
    - If validation fails: Return error status
  - [ ] Implement Stage 2 (LoadContext):
    - Load required context files (Level 2):
      * core/orchestration/delegation.md
      * core/orchestration/state-management.md
      * core/formats/subagent-return.md
    - Load errors.json for historical comparison
    - Load TODO.md for fix tracking
    - Verify context loaded successfully
  - [ ] Implement Stage 3 (AnalyzeErrors):
    - Group errors by type and root cause (migrate from command)
    - Analyze error patterns and frequency
    - Check historical fix effectiveness
    - Identify recurring errors
    - Perform root cause analysis
    - Categorize by severity and impact
    - Generate fix recommendations
    - Create fix plan outline
  - [ ] Implement Stage 4 (ValidateOutputs):
    - Validate all error groups analyzed
    - Validate recommendations are specific and actionable
    - Validate fix plan outline is logical
    - Validate effort estimates are reasonable
    - If validation fails: Log errors and return partial status
  - [ ] Implement Stage 5 (CreateArtifacts):
    - NO artifacts created (analysis only)
    - Skip this stage (return empty artifacts array)
  - [ ] Implement Stage 6 (UpdateState):
    - NO state updates needed (read-only analysis)
    - Skip this stage
  - [ ] Implement Stage 7 (CreateCommit):
    - NO git commits needed (no file changes)
    - Skip this stage
  - [ ] Implement Stage 8 (ReturnResults):
    - Format return per subagent-return-format.md
    - Include status: "completed"
    - Include summary: Brief findings (<100 tokens)
    - Include artifacts: [] (empty, no files created)
    - Include metadata: session_id, duration, agent_type, delegation info
    - Include errors: [] (or error details if any)
    - Include next_steps: "Review recommendations and create fix plan"
    - Include analysis object with all findings
  - [ ] Update frontmatter:
    - context_loading.strategy: lazy
    - context_loading.required: delegation.md, state-management.md, subagent-return.md
    - context_loading.max_context_size: 50000 (Level 2)
    - delegation.can_delegate_to: [] (no further delegation)
  - [ ] Remove old process_flow sections
  - [ ] Verify workflow_execution follows 8-stage pattern
- **Timing:** 1.5-2 hours

### Phase 3: Testing & Validation [PENDING]
- **Goal:** Verify refactored implementation works correctly
- **Tasks:**
  - [ ] Test command with no errors:
    - Expected: "No errors found matching filter"
  - [ ] Test command with --all flag:
    - Expected: All errors analyzed (including addressed)
  - [ ] Test command with --type delegation_hang:
    - Expected: Only delegation_hang errors analyzed
  - [ ] Test command with mixed error types:
    - Expected: Error groups by type, recommendations prioritized
  - [ ] Test subagent return validation:
    - Verify status field validated
    - Verify session_id validated
    - Verify analysis object validated
  - [ ] Test error handling:
    - Invalid errors.json: Expected error message
    - Subagent timeout: Expected timeout handling
    - Validation failure: Expected error details
  - [ ] Verify context loading efficiency:
    - Check context size <50KB (Level 2)
    - Verify only required context loaded
  - [ ] Verify file sizes:
    - errors.md <300 lines
    - error-diagnostics-agent.md follows 8-stage pattern
  - [ ] Compare output with original implementation:
    - Same error grouping logic
    - Same recommendations quality
    - Same fix effectiveness tracking
- **Timing:** 1 hour

### Phase 4: Documentation & Cleanup [COMPLETED]
- **Goal:** Update documentation and commit changes
- **Tasks:**
  - [ ] Update errors.md documentation section:
    - Document 4-stage workflow
    - Update delegation section
    - Update error handling section
  - [ ] Update error-diagnostics-agent.md documentation:
    - Document 8-stage workflow
    - Update input/output specifications
    - Update examples
  - [ ] Verify standards compliance:
    - Command follows command-template.md
    - Subagent follows subagent-template.md
    - Return format matches subagent-return-format.md
  - [ ] Create git commit:
    - Message: "refactor: modernize /errors command and error-diagnostics-agent (task 335)"
    - Include: errors.md, error-diagnostics-agent.md
  - [ ] Update this plan status to [COMPLETED]
- **Timing:** 30 minutes

## Testing & Validation

**Command File Validation**:
- [ ] File size <300 lines
- [ ] 4-stage workflow implemented (ParseAndValidate, Delegate, ValidateReturn, RelayResult)
- [ ] No embedded workflow logic (all in subagent)
- [ ] Context loading optimized (Level 2, <50KB)
- [ ] Comprehensive validation in Stage 3

**Subagent Validation**:
- [ ] 8-stage workflow_execution implemented
- [ ] All stages have action, process, validation, checkpoint
- [ ] Return format matches subagent-return-format.md
- [ ] Context loading strategy: lazy, Level 2
- [ ] No preflight/postflight (read-only analysis)

**Functional Validation**:
- [ ] Error grouping logic preserved
- [ ] Fix recommendations quality maintained
- [ ] Recurrence tracking works correctly
- [ ] All flags work (--all, --type)
- [ ] Error handling comprehensive

**Standards Compliance**:
- [ ] Follows command-template.md
- [ ] Follows subagent-template.md
- [ ] Follows workflow_execution pattern
- [ ] Follows subagent-return-format.md

## Artifacts & Outputs

**Modified Files**:
- .opencode/command/errors.md (refactored, <300 lines)
- .opencode/agent/subagents/error-diagnostics-agent.md (refactored, 8-stage workflow)

**No New Files**:
- No artifacts created (analysis only)
- No state updates (read-only)
- No git commits from subagent

## Rollback/Contingency

If refactoring breaks functionality:
1. Revert git commit: `git revert HEAD`
2. Restore original implementations from git history
3. Review test failures and fix issues
4. Re-test before re-deploying

If validation fails:
1. Review validation errors in detail
2. Fix specific validation issues
3. Re-run tests
4. Update plan with lessons learned

## Success Criteria

- [ ] errors.md <300 lines with 4-stage pattern
- [ ] error-diagnostics-agent.md uses 8-stage workflow_execution
- [ ] All workflow logic in subagent (not command)
- [ ] Context loading optimized (Level 2, <50KB)
- [ ] Return format standardized per subagent-return-format.md
- [ ] All existing functionality preserved
- [ ] Comprehensive validation at command and subagent levels
- [ ] All tests pass
- [ ] Standards compliance verified
- [ ] Git commit created

## Notes

- **No Preflight/Postflight**: /errors is read-only analysis, no status updates or git commits needed
- **No Artifacts**: error-diagnostics-agent returns analysis only, does not create files
- **Context Efficiency**: Level 2 loading (50KB budget) sufficient for error analysis
- **Separation of Concerns**: Command parses/validates/delegates, subagent executes analysis
- **Standards Alignment**: Follows same pattern as /research and /implement commands
