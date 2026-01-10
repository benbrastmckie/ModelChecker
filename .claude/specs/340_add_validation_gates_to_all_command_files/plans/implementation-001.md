# Implementation Plan: Add Validation Gates to All Command Files

- **Task**: 340 - Add validation gates to all command files
- **Status**: [NOT STARTED]
- **Effort**: 3-4 hours
- **Priority**: High
- **Dependencies**: None
- **Research Inputs**: /research and /implement command validation patterns
- **Artifacts**: 
  - plans/implementation-001.md (this file)
  - .opencode/context/core/standards/validation-gates.md (to be created)
  - Updated command files in .opencode/command/
- **Standards**:
  - .opencode/context/core/formats/plan-format.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/orchestration/delegation.md
- **Type**: general
- **Lean Intent**: false

## Overview

Audit all command files in .opencode/command/ to ensure they have proper validation gates that prevent architectural violations. Add pre-execution and post-execution validation following patterns from /research and /implement commands. Document validation gate patterns in new standards file for consistency across all commands.

## Goals & Non-Goals

**Goals**:
- Audit all command files for validation gates
- Add missing pre-execution validation (input validation, file existence checks)
- Add missing post-execution validation (output verification, artifact validation)
- Create .opencode/context/core/standards/validation-gates.md documenting patterns
- Ensure consistent validation across all commands
- Prevent architectural violations (e.g., /task implementing tasks)

**Non-Goals**:
- Fixing specific command bugs (separate tasks)
- Refactoring command structure (separate tasks)
- Creating new commands

## Risks & Mitigations

| Risk | Mitigation |
|------|-----------|
| Breaking existing commands | Test each command after adding validation |
| Inconsistent validation patterns | Document standard patterns first, then apply consistently |
| Over-validation causing false positives | Balance strictness with usability, allow graceful degradation |

## Implementation Phases

### Phase 1: Audit Existing Commands [NOT STARTED]
- **Goal:** Identify which commands lack validation gates
- **Tasks:**
  - [ ] List all command files:
    * ls .opencode/command/*.md
    * Count total commands
  - [ ] For each command, check for validation gates:
    * Pre-execution validation (input checks, file existence)
    * Post-execution validation (output verification, artifact checks)
    * Error handling (clear error messages, recovery suggestions)
  - [ ] Create audit matrix:
    * Command name | Has pre-validation | Has post-validation | Has error handling | Notes
  - [ ] Identify commands needing updates:
    * Prioritize by usage frequency (task, research, implement, plan, review, etc.)
    * Prioritize by architectural risk (commands that create/modify files)
- **Timing:** 1 hour

### Phase 2: Document Validation Gate Patterns [NOT STARTED]
- **Goal:** Create standard validation patterns for all commands
- **Tasks:**
  - [ ] Create .opencode/context/core/standards/validation-gates.md:
    * Define pre-execution validation pattern
    * Define post-execution validation pattern
    * Define error handling pattern
    * Provide examples from /research and /implement
  - [ ] Document validation gate types:
    * Input validation (parameters, flags, arguments)
    * File existence validation (state.json, TODO.md, plan files)
    * Permission validation (can agent perform operation?)
    * Architectural constraint validation (e.g., /task not implementing)
    * Output validation (return format, artifact existence)
    * State consistency validation (TODO.md and state.json synchronized)
  - [ ] Document error handling best practices:
    * Clear error messages (what went wrong)
    * Recovery suggestions (how to fix)
    * Graceful degradation (continue if non-critical failure)
    * Rollback mechanisms (restore state on critical failure)
- **Timing:** 1 hour

### Phase 3: Add Validation to High-Priority Commands [NOT STARTED]
- **Goal:** Update commands with highest usage/risk first
- **Tasks:**
  - [ ] Update /task command (if not done in task 338):
    * Add pre-execution validation (Stage 1)
    * Add post-execution validation (Stage 8)
    * Add architectural constraint validation (no implementation)
  - [ ] Update /research command:
    * Verify pre-execution validation exists
    * Add post-execution validation if missing
    * Verify artifact validation
  - [ ] Update /implement command:
    * Verify pre-execution validation exists
    * Add post-execution validation if missing
    * Verify artifact validation
  - [ ] Update /plan command:
    * Add pre-execution validation
    * Add post-execution validation
    * Verify plan file validation
  - [ ] Update /review command:
    * Add pre-execution validation
    * Add post-execution validation
    * Verify review artifact validation
  - [ ] Test each command after updates:
    * Verify validation gates work correctly
    * Verify error messages are clear
    * Verify no regression in functionality
- **Timing:** 1.5 hours

### Phase 4: Add Validation to Remaining Commands [NOT STARTED]
- **Goal:** Update all remaining commands with validation gates
- **Tasks:**
  - [ ] Update /revise command:
    * Add pre-execution validation
    * Add post-execution validation
  - [ ] Update /todo command:
    * Add pre-execution validation
    * Add post-execution validation
  - [ ] Update /errors command:
    * Add pre-execution validation
    * Add post-execution validation
  - [ ] Update /meta command:
    * Add pre-execution validation
    * Add post-execution validation
    * Add architectural constraint validation (creates tasks, not implementations)
  - [ ] Update /abandon command:
    * Add pre-execution validation
    * Add post-execution validation
  - [ ] Test each command after updates
- **Timing:** 30 minutes

## Testing & Validation

- [ ] All commands have pre-execution validation
- [ ] All commands have post-execution validation
- [ ] All commands have clear error handling
- [ ] validation-gates.md standard created and complete
- [ ] All commands tested and working correctly
- [ ] No regression in existing functionality
- [ ] Architectural violations prevented (e.g., /task not implementing)

## Artifacts & Outputs

- .opencode/context/core/standards/validation-gates.md (new standard)
- Updated command files with validation gates
- Audit matrix documenting validation coverage
- Test results for all commands

## Rollback/Contingency

If validation gates cause issues:
- Revert specific command to previous version
- Investigate validation logic error
- Fix validation logic
- Retry update with corrected validation
- Document lessons learned in validation-gates.md
