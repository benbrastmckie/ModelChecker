# Implementation Plan: Create Deprecation Policy and Migration Guide

- **Task**: 341 - Create deprecation policy and migration guide
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Priority**: Medium
- **Dependencies**: None
- **Research Inputs**: task-creator deprecation experience, OpenAgents best practices
- **Artifacts**: 
  - plans/implementation-001.md (this file)
  - .opencode/context/core/standards/deprecation-policy.md (to be created)
  - .opencode/context/core/standards/migration-guide.md (to be created)
- **Standards**:
  - .opencode/context/core/formats/plan-format.md
  - .opencode/context/core/standards/status-markers.md
- **Type**: markdown
- **Lean Intent**: false

## Overview

Create comprehensive deprecation policy and migration guide to prevent future issues like the task-creator deprecation. Document safe deprecation process: (1) Mark as deprecated with reason, (2) Update all callers, (3) Add deprecation warnings, (4) Remove after migration complete. Provide migration checklist and examples for moving from deprecated agents to replacements.

## Goals & Non-Goals

**Goals**:
- Create .opencode/context/core/standards/deprecation-policy.md
- Create .opencode/context/core/standards/migration-guide.md
- Document safe deprecation process (4-step checklist)
- Provide migration examples (task-creator → status-sync-manager)
- Establish deprecation timeline guidelines
- Define deprecation warning format
- Document rollback procedures

**Non-Goals**:
- Deprecating other agents (separate tasks)
- Implementing deprecation warnings in code (future enhancement)
- Creating automated deprecation detection (future enhancement)

## Risks & Mitigations

| Risk | Mitigation |
|------|-----------|
| Policy too strict (slows development) | Balance safety with agility, allow fast deprecation for internal agents |
| Policy too loose (causes breakage) | Require migration checklist completion before removal |
| Policy not followed | Reference in all agent templates, include in code review checklist |

## Implementation Phases

### Phase 1: Document Deprecation Policy [NOT STARTED]
- **Goal:** Create comprehensive deprecation policy standard
- **Tasks:**
  - [ ] Create .opencode/context/core/standards/deprecation-policy.md
  - [ ] Document deprecation process (4 steps):
    1. Mark as deprecated with reason and date
    2. Update all callers to use replacement
    3. Add deprecation warnings to agent frontmatter
    4. Remove after migration complete and verified
  - [ ] Define deprecation timeline guidelines:
    * Internal agents (used by 1-2 commands): 1 week minimum
    * Core agents (used by 3+ commands): 2 weeks minimum
    * Public agents (used by users): 4 weeks minimum
    * Emergency deprecation (security/critical bug): Immediate with rollback plan
  - [ ] Define deprecation warning format:
    * YAML frontmatter fields: status, deprecation_reason, deprecated_date, replacement
    * Warning message format for agent invocation
    * Documentation update requirements
  - [ ] Document verification requirements:
    * All callers updated (grep verification)
    * All tests passing
    * No deprecation warnings in logs
    * Documentation updated
  - [ ] Document removal checklist:
    * Verify migration complete
    * Remove agent file
    * Update documentation
    * Remove from agent registry (if exists)
    * Create git commit with deprecation details
- **Timing:** 1 hour

### Phase 2: Create Migration Guide [NOT STARTED]
- **Goal:** Provide step-by-step migration guide with examples
- **Tasks:**
  - [ ] Create .opencode/context/core/standards/migration-guide.md
  - [ ] Document migration process:
    1. Identify deprecated agent and replacement
    2. Analyze delegation interface differences
    3. Update delegation parameters
    4. Update return format handling
    5. Test updated caller
    6. Verify no regression
  - [ ] Provide migration examples:
    * task-creator → status-sync-manager (operation: create_task)
    * Include before/after code snippets
    * Show delegation parameter mapping
    * Show return format changes
  - [ ] Document common migration patterns:
    * Delegation layer elimination (task-creator case)
    * Interface consolidation (multiple agents → single agent)
    * Parameter renaming (old_param → new_param)
    * Return format changes (old_format → new_format)
  - [ ] Document testing requirements:
    * Unit tests for updated caller
    * Integration tests for full workflow
    * Performance comparison (before/after)
    * Regression testing checklist
  - [ ] Document rollback procedures:
    * When to rollback (critical failures, data loss)
    * How to rollback (git revert, restore agent file)
    * How to investigate failures (logs, error messages)
    * How to retry migration (fix issues, test again)
- **Timing:** 1 hour

## Testing & Validation

- [ ] deprecation-policy.md created and complete
- [ ] migration-guide.md created and complete
- [ ] Policy includes 4-step deprecation process
- [ ] Policy includes timeline guidelines
- [ ] Policy includes deprecation warning format
- [ ] Policy includes verification requirements
- [ ] Policy includes removal checklist
- [ ] Guide includes migration process
- [ ] Guide includes task-creator → status-sync-manager example
- [ ] Guide includes common migration patterns
- [ ] Guide includes testing requirements
- [ ] Guide includes rollback procedures

## Artifacts & Outputs

- .opencode/context/core/standards/deprecation-policy.md (new standard)
- .opencode/context/core/standards/migration-guide.md (new guide)

## Rollback/Contingency

No rollback needed (documentation only). If policy proves inadequate:
- Update policy based on lessons learned
- Add new sections for edge cases
- Provide additional examples
- Refine timeline guidelines
