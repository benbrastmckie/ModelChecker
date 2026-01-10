# Implementation Plan: Meta-System Optimization

- **Task**: 190 - Optimize meta-system: commands, agents, contexts, and routing
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Priority**: Medium
- **Dependencies**: None
- **Research Inputs**: None linked
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/commands.md
- **Language**: markdown
- **Lean Intent**: false

## Overview

Execute a comprehensive optimization review of the .opencode meta-system to align command-agent-subagent flows and context usage. This review analyzes all commands, agents, subagents, context references, and routing patterns to identify inconsistencies, inefficiencies, and optimization opportunities. The output is a detailed optimization report with actionable recommendations for improving meta-system coherence and performance.

## Goals & Non-Goals

**Goals**:
- Analyze all commands for compliance with standards/commands.md
- Review all agents and subagents for proper routing patterns and context allocation
- Identify context reference optimization opportunities
- Verify plan.md compliance across all plan artifacts
- Map command-agent-subagent flows and detect routing mismatches
- Generate comprehensive optimization report with prioritized recommendations
- Ensure lazy directory creation enforcement across all components
- Validate status marker usage and registry synchronization patterns

**Non-Goals**:
- Implementing optimization recommendations (separate task)
- Modifying existing commands or agents during review
- Creating new commands or agents
- Refactoring code outside .opencode meta-system
- Performance profiling of Lean code

## Risks & Mitigations

- **Risk**: Analysis scope too broad, exceeds time estimate. **Mitigation**: Use parallel subagent coordination; focus on high-impact patterns first.
- **Risk**: Context loading becomes circular (analyzing context while loading context). **Mitigation**: Use Level 2 context allocation; load only standards and system contexts.
- **Risk**: Report becomes too detailed, bloats context window. **Mitigation**: Create summary artifact alongside detailed report; return only summary to orchestrator.
- **Risk**: Routing analysis reveals deep architectural issues requiring major refactoring. **Mitigation**: Document issues clearly; prioritize recommendations by impact and effort.

## Implementation Phases

### Phase 1: Preflight Validation [NOT STARTED]

- **Goal**: Validate scope, load context references, initialize analysis environment
- **Tasks**:
  - [ ] Validate task number 190 exists in TODO.md with correct metadata
  - [ ] Verify scope parameter is "all" (commands, agents, contexts, docs, routing)
  - [ ] Load context references from core/standards/ and core/system/
  - [ ] Verify access to .opencode/command/, .opencode/agent/, .opencode/context/
  - [ ] Initialize analysis tracking structure (in-memory)
  - [ ] Validate no Lean intent (language: markdown)
- **Timing**: 15 minutes
- **Validation**: All context files accessible, scope confirmed, tracking initialized

### Phase 2: Command Analysis [NOT STARTED]

- **Goal**: Review all commands for compliance with standards/commands.md
- **Tasks**:
  - [ ] Enumerate all command files in .opencode/command/
  - [ ] For each command, verify YAML front matter structure (name, agent, description, context_level, language, subagents, mcp_requirements, registry_impacts, creates_root_on, creates_subdir)
  - [ ] Verify Context Loaded block uses @ paths and includes required standards
  - [ ] Verify XML section order (context, role, task, workflow_execution, routing_intelligence, artifact_management, quality_standards, usage_examples, validation)
  - [ ] Check status marker usage in workflow_execution stages
  - [ ] Verify lazy directory creation guardrails in artifact_management
  - [ ] Check registry/state sync patterns in artifact_management
  - [ ] Validate language routing logic (Lean vs non-Lean)
  - [ ] Document deviations, missing sections, and inconsistencies
- **Timing**: 2 hours
- **Validation**: All 15 commands analyzed, deviations documented

### Phase 3: Agent Analysis [NOT STARTED]

- **Goal**: Review all agents and subagents for proper routing patterns and context allocation
- **Tasks**:
  - [ ] Enumerate all agent files in .opencode/agent/subagents/
  - [ ] Enumerate all specialist files in .opencode/agent/subagents/specialists/
  - [ ] For each agent, verify context allocation level (1/2/3) is appropriate for scope
  - [ ] Check routing patterns: verify subagent invocations use correct context levels
  - [ ] Verify status marker usage in workflow stages
  - [ ] Check lazy directory creation enforcement
  - [ ] Validate artifact return patterns (references + summaries, not full content)
  - [ ] Identify agents with overlapping responsibilities
  - [ ] Document routing inefficiencies (e.g., unnecessary delegation chains)
  - [ ] Check for circular routing patterns
- **Timing**: 2.5 hours
- **Validation**: All 30+ agents analyzed, routing patterns mapped

### Phase 4: Context Analysis [NOT STARTED]

- **Goal**: Analyze context references and loading patterns for optimization opportunities
- **Tasks**:
  - [ ] Route to context-analyzer specialist to analyze context directory structure
  - [ ] Identify context files loaded by multiple commands/agents
  - [ ] Detect redundant context content across files
  - [ ] Analyze context allocation patterns (Level 1/2/3 usage)
  - [ ] Identify missing context references (commands not loading required standards)
  - [ ] Check for context bloat (files loading unnecessary contexts)
  - [ ] Verify @ path consistency across all context references
  - [ ] Document optimization opportunities (consolidation, splitting, reordering)
- **Timing**: 1.5 hours
- **Validation**: Context usage patterns mapped, optimization opportunities identified

### Phase 5: Documentation Analysis [NOT STARTED]

- **Goal**: Verify plan.md compliance, command documentation, and workflow documentation
- **Tasks**:
  - [ ] Route to doc-analyzer specialist to check plan artifacts in .opencode/specs/
  - [ ] Verify all plan files follow plan.md standard (metadata, section order, status markers)
  - [ ] Check command documentation completeness (all commands have usage_examples)
  - [ ] Verify workflow documentation in core/workflows/ is referenced by relevant commands
  - [ ] Check for orphaned documentation (docs not referenced by any command/agent)
  - [ ] Validate status marker usage across all plan artifacts
  - [ ] Check timestamp format compliance (YYYY-MM-DD in TODO, ISO8601 in plans)
  - [ ] Document documentation gaps and compliance issues
- **Timing**: 1.5 hours
- **Validation**: All plan artifacts checked, documentation gaps identified

### Phase 6: Routing Analysis [NOT STARTED]

- **Goal**: Map command-agent-subagent flows and identify mismatches or inefficiencies
- **Tasks**:
  - [ ] Route to dependency-mapper specialist to map command-agent flows
  - [ ] For each command, trace full execution path (command -> agent -> subagents)
  - [ ] Identify routing mismatches (command YAML lists agent X, but invokes agent Y)
  - [ ] Detect inefficient routing (unnecessary delegation layers)
  - [ ] Check for missing routing documentation (subagents not listed in command YAML)
  - [ ] Verify context level propagation (Level 2 command -> Level 2 subagents)
  - [ ] Identify commands with complex routing that could be simplified
  - [ ] Document routing flow diagrams for complex commands
  - [ ] Check for routing patterns that violate lazy directory creation
- **Timing**: 1.5 hours
- **Validation**: All command flows mapped, routing issues documented

### Phase 7: Report Generation [NOT STARTED]

- **Goal**: Create comprehensive optimization report with prioritized recommendations
- **Tasks**:
  - [ ] Synthesize findings from all analysis phases
  - [ ] Categorize issues by severity (critical, high, medium, low)
  - [ ] Prioritize recommendations by impact and effort
  - [ ] Create detailed optimization report in reports/optimize-report-20251225.md
  - [ ] Include specific examples for each issue category
  - [ ] Provide actionable remediation steps for each recommendation
  - [ ] Create executive summary section (3-5 sentences)
  - [ ] Create implementation summary in summaries/implementation-summary-20251225.md
  - [ ] Ensure report follows markdown standards (no emojis)
  - [ ] Validate report structure and completeness
- **Timing**: 1 hour
- **Validation**: Report created, summary created, all findings documented

### Phase 8: Postflight Synchronization [NOT STARTED]

- **Goal**: Sync TODO/state, update registries, finalize artifacts
- **Tasks**:
  - [ ] Update TODO.md task 190 status to [COMPLETED]
  - [ ] Add completion timestamp to TODO.md
  - [ ] Update .opencode/specs/state.json with project 190 completion
  - [ ] Update project state.json with artifact paths
  - [ ] Link optimization report in TODO.md task 190
  - [ ] Verify IMPLEMENTATION_STATUS.md does not require updates (review task, no code changes)
  - [ ] Verify no registry updates needed (no sorry/tactic changes)
  - [ ] Validate all artifacts follow lazy directory creation (reports/ created only when writing report)
  - [ ] Confirm no emojis in any artifacts
  - [ ] Return artifact references and summary to orchestrator
- **Timing**: 30 minutes
- **Validation**: TODO/state synchronized, artifacts linked, orchestrator receives summary

## Testing & Validation

- [ ] All 15 commands analyzed for standards compliance
- [ ] All 30+ agents analyzed for routing patterns
- [ ] Context usage patterns mapped and documented
- [ ] All plan artifacts checked for plan.md compliance
- [ ] Command-agent-subagent flows mapped for all commands
- [ ] Optimization report contains actionable recommendations
- [ ] Summary artifact created (3-5 sentences, <100 tokens)
- [ ] No emojis in any artifacts
- [ ] Lazy directory creation followed (reports/ created only when writing report)
- [ ] TODO.md and state.json synchronized
- [ ] All status markers follow status-markers.md standard

## Artifacts & Outputs

- **plans/implementation-001.md**: This implementation plan
- **reports/optimize-report-20251225.md**: Detailed optimization report with findings and recommendations
- **summaries/implementation-summary-20251225.md**: Brief summary of optimization review (3-5 sentences)
- **state.json**: Project state tracking

## Rollback/Contingency

This is a review task with no code changes, so rollback is not applicable. If analysis reveals critical issues requiring immediate attention:

1. Document critical issues in separate section of report
2. Create follow-up tasks in TODO.md for urgent fixes
3. Notify orchestrator of critical findings in return summary
4. Preserve all analysis artifacts for reference

If analysis cannot complete within time estimate:

1. Complete high-priority analyses first (commands, agents, routing)
2. Document incomplete analyses in report
3. Create follow-up task for remaining analyses
4. Return partial results with clear scope limitations
