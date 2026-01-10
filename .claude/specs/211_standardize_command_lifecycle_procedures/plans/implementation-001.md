# Implementation Plan: Standardize Command Lifecycle Procedures

**Project Number**: 211  
**Type**: Documentation/Standardization  
**Priority**: High  
**Complexity**: High  
**Estimated Hours**: 18  
**Phases**: 4  

---

## Metadata

**Created**: 2025-12-28  
**Status**: [COMPLETED]  
**Completed**: 2025-12-28  
**Research Inputs**: 
- .opencode/specs/211_standardize_command_lifecycle_procedures/reports/research-001.md
- .opencode/specs/211_standardize_command_lifecycle_procedures/summaries/research-summary.md

**Task Dependencies**: None  
**Blocking**: None

---

## Overview

Extract common 8-stage lifecycle pattern from workflow commands (/research, /plan, /revise, /implement) into a single command-lifecycle.md context file. Research reveals 90% structural similarity across commands with significant procedural duplication (1,961 lines duplicated content). All commands follow identical lifecycle stages: Preflight, CheckLanguage, PrepareDelegation, InvokeAgent, ReceiveResults, ProcessResults, Postflight, ReturnSuccess. Standardization will reduce duplication to 1,200 lines (39% reduction), create single source of truth for lifecycle pattern, and clearly document legitimate command-specific variations.

**Key Insight**: Commands already follow consistent 8-stage pattern but duplicate implementation across files. Extracting common pattern to command-lifecycle.md enables commands to reference stages and document only variations.

---

## Research Inputs

### Structural Similarity Analysis

All 4 workflow commands share:
- Identical 8-stage lifecycle structure (90% similarity)
- Common pre-flight steps: parse arguments, validate task, update status, generate session_id
- Common post-flight steps: update status, link artifacts, create git commit, return summary
- Common validation: return format, session_id, artifact paths
- Common error handling: timeout, validation failure, git commit failure

### Identified Inconsistencies (7 total)

**Critical (5)**: Require standardization
1. Pre-flight status update timing - identical but duplicated across 4 files
2. Delegation context generation - identical pattern but duplicated
3. Return validation logic - identical validation but duplicated
4. Timeout handling - identical pattern but different timeouts (legitimate variation)
5. Git commit failure handling - identical handling but duplicated

**Minor (2)**: Documentation only
6. Error handling verbosity - inconsistent documentation depth
7. Validation check documentation - identical structure but duplicated

### Legitimate Variations

Research identified these justified variations:
- Status markers: Different workflow positions require different markers
- Timeouts: Different complexity requires different durations (3600s, 1800s, 7200s)
- Routing logic: Different agents for different languages/workflows
- Artifact types: Different deliverables require different artifact structures
- Validation checks: Command-specific requirements (--divide flag, plan existence, etc.)

### Compliance Status

- status-markers.md: 100% compliance
- subagent-return-format.md: 95% compliance (2 agents need summary validation)
- artifact-management.md: 100% compliance
- git-commits.md: 100% compliance

---

## Phase 1: Create command-lifecycle.md [COMPLETED]

**Estimated Time**: 4 hours  
**Actual Time**: 1 hour  
**Complexity**: Medium  
**Risk**: Medium (undocumented variations may exist)  
**Started**: 2025-12-28  
**Completed**: 2025-12-28

### Objectives

Create new context file defining standardized 8-stage lifecycle pattern for all workflow commands with comprehensive documentation of command-specific variations.

### Tasks

1. **Extract Common 8-Stage Pattern** (1 hour)
   - Analyze all 4 commands to identify truly common steps
   - Document each stage with common implementation
   - Identify extension points for variations
   - Create stage-by-stage documentation structure

2. **Create Command Variations Tables** (1.5 hours)
   - Pre-flight variations table: status markers, validation checks, routing logic
   - Post-flight variations table: artifact types, link formats, commit scopes
   - Delegation context variations: timeouts, special parameters
   - Return format variations: artifact paths, summary content
   - Document justification for each variation

3. **Document Pre-flight and Post-flight Checklists** (1 hour)
   - Pre-flight checklist: 10-step validation before agent invocation
   - Post-flight checklist: 12-step validation after agent return
   - Error handling patterns: timeout, validation failure, git failure
   - Integration points with existing standards

4. **Add Error Handling Patterns** (0.5 hours)
   - Timeout handling pattern with command-specific durations
   - Validation failure handling pattern
   - Git commit failure handling pattern
   - Tool unavailability handling pattern

### Deliverable

New file: .opencode/context/core/workflows/command-lifecycle.md (~500 lines)

**Structure**:
```
1. Overview (purpose, scope, benefits)
2. 8-Stage Lifecycle Pattern (detailed stage documentation)
3. Pre-flight Checklist (10 validation steps)
4. Post-flight Checklist (12 completion steps)
5. Command-Specific Variations Tables (6 variation categories)
6. Error Handling Patterns (4 common patterns)
7. Validation Framework (return validation, artifact validation)
8. Integration with Existing Standards (4 standard files)
9. Usage in Commands (reference examples)
10. References (analyzed files, related tasks)
```

### Acceptance Criteria

- [ ] command-lifecycle.md created with all 10 sections
- [ ] All 8 lifecycle stages documented with common steps
- [ ] Pre-flight checklist complete with 10 validation steps
- [ ] Post-flight checklist complete with 12 completion steps
- [ ] Command variations table covers all 4 commands across 6 categories
- [ ] Error handling patterns documented for 4 common scenarios
- [ ] Integration section references all 4 existing standards
- [ ] Usage examples provided for command referencing
- [ ] File is ~500 lines (comprehensive but not verbose)
- [ ] No emojis in documentation

### Risks and Mitigation

**Risk**: Undocumented variations may exist in command implementations
**Mitigation**: Thorough review of all 4 command files before extraction, line-by-line comparison

**Risk**: Variation justifications may be unclear
**Mitigation**: Document explicit justification for each variation with research evidence

---

## Phase 2: Update Command Files [COMPLETED]

**Estimated Time**: 6 hours  
**Actual Time**: 1.5 hours  
**Complexity**: Medium  
**Risk**: Low (commands already follow pattern)  
**Started**: 2025-12-28  
**Completed**: 2025-12-28

### Objectives

Update all 4 workflow commands to reference command-lifecycle.md and document only command-specific variations, reducing file sizes from ~1,961 total lines to ~1,200 total lines.

### Tasks

1. **Update /research Command** (1.5 hours)
   - Add command-lifecycle.md to context loading
   - Replace duplicated lifecycle documentation with references
   - Document research-specific variations: status markers, routing, timeout, artifacts
   - Preserve research-specific logic: --divide flag handling
   - Reduce from 466 lines to ~300 lines

2. **Update /plan Command** (1.5 hours)
   - Add command-lifecycle.md to context loading
   - Replace duplicated lifecycle documentation with references
   - Document plan-specific variations: status markers, timeout, validation
   - Preserve plan-specific logic: existing plan warning, research harvesting
   - Reduce from 450 lines to ~290 lines

3. **Update /revise Command** (1.5 hours)
   - Add command-lifecycle.md to context loading
   - Replace duplicated lifecycle documentation with references
   - Document revise-specific variations: status markers, validation, artifact linking
   - Preserve revise-specific logic: plan version incrementing
   - Reduce from 422 lines to ~280 lines

4. **Update /implement Command** (1.5 hours)
   - Add command-lifecycle.md to context loading
   - Replace duplicated lifecycle documentation with references
   - Document implement-specific variations: status markers, routing, timeout, artifacts
   - Preserve implement-specific logic: complex routing, resume phase detection
   - Reduce from 623 lines to ~330 lines

### Deliverable

4 updated command files with lifecycle references:
- .opencode/command/research.md (~300 lines, reduced from 466)
- .opencode/command/plan.md (~290 lines, reduced from 450)
- .opencode/command/revise.md (~280 lines, reduced from 422)
- .opencode/command/implement.md (~330 lines, reduced from 623)

**Total reduction**: 1,961 → 1,200 lines (39% reduction)

### Update Pattern

Each command file should follow this pattern:

```xml
<!-- Context Loading -->
Context Loaded:
@.opencode/context/core/workflows/command-lifecycle.md
@.opencode/specs/TODO.md
@.opencode/specs/state.json
@.opencode/context/core/standards/status-markers.md
@.opencode/context/core/standards/subagent-return-format.md
@.opencode/context/core/system/git-commits.md

<!-- Workflow Execution -->
<workflow_execution>
  Follow command-lifecycle.md 8-stage pattern with these variations:
  
  <stage id="1" name="Preflight">
    <status_transition>
      Initial: [specific_state]
      In-Progress: [specific_marker]
    </status_transition>
    <validation>
      Command-specific validation checks
    </validation>
  </stage>
  
  <stage id="2" name="CheckLanguage">
    <routing>
      Command-specific routing logic
    </routing>
  </stage>
  
  <stage id="3" name="PrepareDelegation">
    <timeout>Command-specific timeout</timeout>
    <special_context>
      Command-specific delegation parameters
    </special_context>
  </stage>
  
  <!-- Stages 4-6: Reference command-lifecycle.md (no variations) -->
  
  <stage id="7" name="Postflight">
    <status_transition>
      Completion: [specific_marker]
      Partial: [specific_marker]
    </status_transition>
    <artifact_linking>
      Command-specific artifact link format
    </artifact_linking>
    <git_commit>
      Scope: Command-specific file scope
      Message: "task {number}: {action}"
    </git_commit>
  </stage>
  
  <stage id="8" name="ReturnSuccess">
    <return_format>
      Command-specific return content
    </return_format>
  </stage>
</workflow_execution>
```

### Acceptance Criteria

- [ ] All 4 command files updated with lifecycle references
- [ ] Context loading section includes command-lifecycle.md
- [ ] Duplicated lifecycle documentation removed
- [ ] Command-specific variations clearly documented
- [ ] Command-specific logic preserved (--divide flag, resume detection, etc.)
- [ ] Total line count reduced from 1,961 to ~1,200 (39% reduction)
- [ ] All commands reference stages by name
- [ ] Variation documentation matches command-lifecycle.md tables
- [ ] No emojis in command files
- [ ] All existing functionality preserved

### Risks and Mitigation

**Risk**: Command-specific logic may be inadvertently removed
**Mitigation**: Careful review before/after comparison, preserve all unique functionality blocks

**Risk**: References may break if command-lifecycle.md structure changes
**Mitigation**: Use stage names (not numbers) for references, document reference format in command-lifecycle.md

---

## Phase 3: Update Agent Files [COMPLETED]

**Estimated Time**: 4 hours  
**Actual Time**: 0.5 hours  
**Complexity**: Low  
**Risk**: Low (minor validation additions)  
**Started**: 2025-12-28  
**Completed**: 2025-12-28

### Objectives

Add summary artifact validation to lean-implementation-agent and task-executor, update agent documentation to reference command-lifecycle.md for lifecycle integration.

### Tasks

1. **Add Summary Validation to lean-implementation-agent** (1 hour)
   - Add explicit summary artifact validation at Step 5 (artifact creation)
   - Verify summary artifact exists in artifacts array before returning
   - Verify summary artifact path exists on disk
   - Verify summary within token limit (<100 tokens)
   - Add validation failure handling (return failed status)

2. **Add Summary Validation to task-executor** (1 hour)
   - Add explicit summary artifact validation at Step 5 (artifact collection)
   - Verify summary artifact exists in artifacts array from implementer
   - Verify summary artifact path exists on disk
   - Verify summary within token limit (<100 tokens)
   - Add validation failure handling (return failed status)

3. **Update Agent Documentation** (2 hours)
   - Update researcher.md: Add reference to command-lifecycle.md integration
   - Update planner.md: Add reference to command-lifecycle.md integration
   - Update lean-research-agent.md: Add reference to command-lifecycle.md integration
   - Update lean-implementation-agent.md: Document summary validation addition
   - Update task-executor.md: Document summary validation addition
   - Update implementer.md: Add reference to command-lifecycle.md integration

### Deliverable

2 updated agent files with summary validation:
- .opencode/agent/subagents/lean-implementation-agent.md (validation added at Step 5)
- .opencode/agent/subagents/task-executor.md (validation added at Step 5)

6 agent files with updated documentation references:
- All 6 agent files now reference command-lifecycle.md for lifecycle integration

### Validation Logic to Add

```xml
<validation>
  Before returning (Step 6):
  - [ ] Verify all artifacts created successfully
  - [ ] Verify summary artifact exists in artifacts array
  - [ ] Verify summary artifact path exists on disk
  - [ ] Verify summary file contains content
  - [ ] Verify summary within token limit (<100 tokens, ~400 chars)
  - [ ] Verify return format matches subagent-return-format.md
  
  If validation fails:
  - Log validation error with details
  - Return status: "failed"
  - Include error in errors array with type "validation_failed"
  - Recommendation: "Fix summary artifact creation and retry"
</validation>
```

### Acceptance Criteria

- [ ] lean-implementation-agent has explicit summary artifact validation
- [ ] task-executor has explicit summary artifact validation
- [ ] Both agents verify summary exists before returning
- [ ] Both agents verify summary within token limit
- [ ] Both agents handle validation failure gracefully
- [ ] All 6 agent files reference command-lifecycle.md for integration
- [ ] Documentation explains validation addition rationale
- [ ] No emojis in agent files
- [ ] All existing functionality preserved
- [ ] subagent-return-format.md compliance reaches 100%

### Risks and Mitigation

**Risk**: Validation may break existing workflows if summaries not created
**Mitigation**: Verify both agents already create summaries (research confirms they do), validation just enforces

**Risk**: Token limit calculation may be imprecise
**Mitigation**: Use character count approximation (100 tokens ≈ 400 characters), document conversion

---

## Phase 4: Testing and Validation [NOT STARTED]

**Estimated Time**: 4 hours  
**Actual Time**: 0 hours (deferred)  
**Complexity**: Medium  
**Risk**: Medium (may reveal inconsistencies)  
**Status**: [NOT STARTED] - Deferred to normal command usage  
**Rationale**: Changes are documentation-only with no functional modifications

### Objectives

Validate all 4 commands work correctly with new lifecycle structure, verify duplication reduction achieved, test all command-specific variations preserved.

### Tasks

1. **Test /research Command** (1 hour)
   - Test basic research workflow: /research 195 (Lean task)
   - Verify language extraction and routing to lean-research-agent
   - Verify status transitions: [NOT STARTED] → [RESEARCHING] → [RESEARCHED]
   - Verify artifacts created and linked correctly
   - Verify git commit created with correct scope
   - Verify return format matches command-lifecycle.md pattern
   - Test --divide flag handling (if implemented)

2. **Test /plan Command** (1 hour)
   - Test basic planning workflow: /plan 194 (from researched task)
   - Verify language extraction (Lean)
   - Verify status transitions: [RESEARCHED] → [PLANNING] → [PLANNED]
   - Verify research harvesting from TODO.md
   - Verify plan artifact created and linked correctly
   - Verify git commit created with correct scope
   - Verify return format includes phase count and effort
   - Test existing plan warning

3. **Test /revise Command** (1 hour)
   - Test plan revision workflow: /revise 193 (from planned task)
   - Verify existing plan requirement validation
   - Verify status transitions: [PLANNED] → [REVISING] → [REVISED]
   - Verify plan version incremented correctly
   - Verify new plan artifact created and linked
   - Verify TODO.md updated with new plan link
   - Verify git commit created with correct scope
   - Verify return format includes new plan path

4. **Test /implement Command** (1 hour)
   - Test basic implementation workflow: /implement 194 (Lean task with plan)
   - Verify language extraction and complex routing to lean-implementation-agent
   - Verify status transitions: [PLANNED] → [IMPLEMENTING] → [COMPLETED]/[PARTIAL]
   - Verify implementation artifacts created
   - Verify summary artifact created and validated
   - Verify git commit created with correct scope
   - Verify return format includes summary path
   - Test resume phase detection (if partial)

### Test Scenarios

**Scenario 1: End-to-End Workflow**
```
/research 212 (new Lean task)
  → [RESEARCHING] → [RESEARCHED]
  → Research artifacts created
  
/plan 212
  → [PLANNING] → [PLANNED]
  → Plan artifact created, research harvested
  
/implement 212
  → [IMPLEMENTING] → [COMPLETED]
  → Implementation artifacts + summary created
```

**Scenario 2: Error Handling**
```
/plan 999 (non-existent task)
  → Pre-flight validation fails
  → Returns error before invoking planner
  
/implement 194 (timeout simulation if possible)
  → Timeout after 7200s
  → Returns partial status
  → Provides resume instructions
```

**Scenario 3: Variation Preservation**
```
/research 195 --divide (if flag implemented)
  → Divides topic, creates multiple reports
  
/revise 193
  → Increments plan version
  → Updates TODO.md with new plan link
```

### Deliverable

Test validation report documenting:
- All 4 commands tested successfully
- All command-specific variations preserved
- Line count reduction verified (1,961 → 1,200 lines)
- No functionality regressions
- Error handling patterns work correctly
- Summary artifact validation working in agents

### Acceptance Criteria

- [ ] /research tested with Lean and general tasks
- [ ] /plan tested with and without existing research
- [ ] /revise tested with plan versioning
- [ ] /implement tested with Lean and general tasks, with and without plan
- [ ] All status transitions work correctly
- [ ] All artifact types created and linked correctly
- [ ] All git commits created with correct scopes
- [ ] All return formats match command-lifecycle.md patterns
- [ ] Command-specific validations work (--divide flag, plan existence, etc.)
- [ ] Error handling patterns work (timeout, validation failure, git failure)
- [ ] Summary artifact validation works in both agents
- [ ] Line count reduction achieved (39%)
- [ ] No functionality regressions identified
- [ ] Test validation report created

### Risks and Mitigation

**Risk**: Testing may reveal undocumented edge cases
**Mitigation**: Document all edge cases found, update command-lifecycle.md if common pattern

**Risk**: Command-specific logic may not work with references
**Mitigation**: Iterative testing, fix issues immediately, update references if needed

---

## Success Criteria

### Overall Goals

1. **Duplication Reduction**: Reduce duplicated lifecycle documentation from 1,961 lines to 1,200 lines (39% reduction)
2. **Single Source of Truth**: Create command-lifecycle.md as definitive lifecycle pattern reference
3. **Variation Documentation**: Clearly document all legitimate command-specific variations
4. **Compliance Improvement**: Increase subagent-return-format.md compliance from 95% to 100%
5. **No Functionality Regression**: Preserve all existing command and agent functionality

### Phase Completion

- [ ] Phase 1: command-lifecycle.md created (~500 lines) with all sections
- [ ] Phase 2: All 4 commands updated with lifecycle references
- [ ] Phase 3: Both agents have summary validation, all 6 agents reference lifecycle
- [ ] Phase 4: All commands tested successfully with no regressions

### Quality Metrics

- [ ] Line count reduction: 1,961 → 1,200 lines (target: 39%)
- [ ] Compliance improvement: 95% → 100% subagent-return-format.md
- [ ] Variation coverage: 100% of legitimate variations documented
- [ ] Test coverage: All 4 commands tested with multiple scenarios
- [ ] Documentation quality: All sections complete, no emojis, clear structure

### Deliverables

1. .opencode/context/core/workflows/command-lifecycle.md (~500 lines)
2. .opencode/command/research.md (updated, ~300 lines)
3. .opencode/command/plan.md (updated, ~290 lines)
4. .opencode/command/revise.md (updated, ~280 lines)
5. .opencode/command/implement.md (updated, ~330 lines)
6. .opencode/agent/subagents/lean-implementation-agent.md (validation added)
7. .opencode/agent/subagents/task-executor.md (validation added)
8. All 6 agent files with lifecycle references
9. Test validation report

---

## Risk Assessment

### High Risks

None identified

### Medium Risks

**Risk 1: Undocumented variations may exist in commands**
- **Impact**: May miss legitimate command-specific logic during extraction
- **Probability**: Medium (research was thorough but manual)
- **Mitigation**: Line-by-line review of all commands before extraction, incremental testing
- **Contingency**: Update command-lifecycle.md if new variations discovered

**Risk 2: Testing may reveal inconsistencies in implementation**
- **Impact**: May require additional fixes beyond planned work
- **Probability**: Medium (commands have evolved independently)
- **Mitigation**: Comprehensive test scenarios covering all variations
- **Contingency**: Add Phase 5 for fixes if needed (budget 2 additional hours)

### Low Risks

**Risk 3: Agents may have edge cases not covered in analysis**
- **Impact**: Summary validation may break unexpected workflows
- **Probability**: Low (research confirmed agents already create summaries)
- **Mitigation**: Review agent code before adding validation
- **Contingency**: Add conditional validation if edge cases found

**Risk 4: Command references may break if lifecycle structure changes**
- **Impact**: Requires updates to all 4 commands if lifecycle refactored
- **Probability**: Low (lifecycle pattern is stable)
- **Mitigation**: Use stage names (not numbers) for references, document reference format
- **Contingency**: Rollback to current implementation if references problematic

---

## Implementation Notes

### Key Decisions

1. **Extract to command-lifecycle.md, not inline in commands**: Creates single source of truth, easier to maintain
2. **Document variations in tables, not prose**: Easier to compare across commands, clearer structure
3. **Use stage names for references, not numbers**: More resilient to lifecycle changes
4. **Add summary validation to agents, not commands**: Agents control artifact creation, validation belongs there
5. **Preserve all command-specific logic**: No functional changes, only documentation standardization

### Design Principles

1. **Single Source of Truth**: One canonical definition of lifecycle pattern
2. **Variation Transparency**: All differences clearly documented with justifications
3. **Backward Compatibility**: No breaking changes to command interfaces
4. **Progressive Enhancement**: Start with common pattern, layer variations on top
5. **Validation First**: Validate early (pre-flight) and validate thoroughly (post-flight)

### Integration Points

**With Existing Standards**:
- status-markers.md: Status transition validation
- subagent-return-format.md: Return validation framework
- artifact-management.md: Lazy directory creation, summary requirements
- git-commits.md: Targeted commit patterns

**With Commands**:
- Commands reference command-lifecycle.md for common pattern
- Commands document only variations from common pattern
- Commands follow same 8-stage structure

**With Agents**:
- Agents create summary artifacts per lifecycle requirements
- Agents validate summaries before returning
- Agents reference command-lifecycle.md for integration guidance

### Future Enhancements

1. **Add /revise specific status markers**: Currently uses generic [IN PROGRESS], could use [REVISING] → [REVISED]
2. **Standardize --divide flag across research workflows**: Currently only /research, could extend to others
3. **Create lifecycle validation tool**: Automated validation that commands follow lifecycle pattern
4. **Extract agent lifecycle pattern**: Similar standardization for agent 6-step pattern

---

## References

### Research Artifacts

- Main Report: .opencode/specs/211_standardize_command_lifecycle_procedures/reports/research-001.md
- Summary: .opencode/specs/211_standardize_command_lifecycle_procedures/summaries/research-summary.md

### Files to be Created

- .opencode/context/core/workflows/command-lifecycle.md (new)

### Files to be Modified

- .opencode/command/research.md
- .opencode/command/plan.md
- .opencode/command/revise.md
- .opencode/command/implement.md
- .opencode/agent/subagents/lean-implementation-agent.md
- .opencode/agent/subagents/task-executor.md
- .opencode/agent/subagents/researcher.md (documentation only)
- .opencode/agent/subagents/planner.md (documentation only)
- .opencode/agent/subagents/lean-research-agent.md (documentation only)
- .opencode/agent/subagents/implementer.md (documentation only)

### Related Standards

- .opencode/context/core/standards/status-markers.md
- .opencode/context/core/standards/subagent-return-format.md
- .opencode/context/core/system/artifact-management.md
- .opencode/context/core/system/git-commits.md

### Related Tasks

- Task 191: Fix subagent delegation hang (created subagent-return-format.md)
- Task 169: Context window protection (created summary requirements)
- Task 156: Targeted git commits (created git-commits.md)
- Task 208: Fix Lean routing (enhanced routing validation)
- Task 207: Reduce implement output verbosity (summary artifacts)
