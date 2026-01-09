# ADR-002: Agent Workflow Ownership Pattern

**Status**: Accepted  
**Date**: 2025-12-28  
**Decision Makers**: ProofChecker Development Team  
**Related Tasks**: Task 245 (Phase 2)

---

## Context and Problem Statement

The original OpenCode system split workflow execution between commands and agents. Commands owned Stages 1-6 (routing, delegation, execution) while agents owned only the core work. Stage 7 (artifact validation, status updates, git commits) was inconsistently implemented, leading to ~20% failure rate.

**Problems**:
1. **Stage 7 Failures**: ~20% of executions failed to complete Stage 7 properly
2. **Split Responsibility**: Unclear who owns artifact validation and status updates
3. **Inconsistent Implementation**: Each command implemented Stage 7 differently
4. **Maintenance Burden**: Changes to workflow required updates across all commands
5. **Poor Reliability**: No guarantee that artifacts were validated or status updated

**Key Question**: Who should own the complete 8-stage workflow, and how should Stage 7 be implemented consistently?

---

## Decision Drivers

1. **Reliability**: Must achieve 100% Stage 7 execution rate
2. **Consistency**: All commands must execute workflow identically
3. **Maintainability**: Workflow changes should require minimal updates
4. **Clarity**: Clear ownership of each workflow stage
5. **Simplicity**: Reduce complexity in command files

---

## Considered Options

### Option 1: Command-Driven Workflow (Status Quo)

**Description**: Commands own Stages 1-7, agents own only core execution.

**Pros**:
- No changes required
- Commands have full control
- Familiar pattern

**Cons**:
- ~20% Stage 7 failure rate
- Inconsistent implementation across commands
- High maintenance burden (changes require updating all commands)
- Split responsibility (unclear ownership)

**Verdict**: ❌ Rejected - Doesn't solve reliability problem

### Option 2: Shared Workflow (Command + Agent)

**Description**: Commands own Stages 1-6, agents own Stage 7.

**Pros**:
- Clear separation of concerns
- Agents own artifact validation
- Commands simplified

**Cons**:
- Still split responsibility
- Requires coordination between command and agent
- Potential for inconsistency
- Complex handoff between stages

**Verdict**: ❌ Rejected - Still has split responsibility issues

### Option 3: Agent-Driven Workflow (Selected)

**Description**: Agents own complete 8-stage workflow. Commands become thin delegation layers that route to agents.

**Pros**:
- Single owner for complete workflow (agent)
- Consistent implementation (all agents follow same pattern)
- 100% Stage 7 execution (agent owns it)
- Simplified commands (just routing)
- Easy to maintain (workflow changes in one place)

**Cons**:
- Requires migrating all commands
- Agents become more complex
- Initial implementation effort

**Verdict**: ✅ **Selected** - Best reliability and maintainability

---

## Decision Outcome

**Chosen Option**: Agent-Driven Workflow (Option 3)

### Implementation

1. **8-Stage Workflow Ownership**: Agents own all 8 stages
   - Stage 1: Input Validation
   - Stage 2: Context Loading
   - Stage 3: Core Execution
   - Stage 4: Output Generation
   - Stage 5: Artifact Creation
   - Stage 6: Return Formatting
   - **Stage 7: Artifact Validation, Status Updates, Git Commits** ← Critical
   - Stage 8: Cleanup

2. **Command Simplification**: Commands become thin delegation layers
   - Commands specify agent in frontmatter (`agent:` field)
   - Commands provide usage documentation
   - Commands delegate to agent immediately
   - No workflow logic in commands

3. **Stage 7 Requirements**: All agents must implement Stage 7
   - Validate all artifacts created successfully
   - Update TODO.md with task status
   - Update state.json with completion status
   - Create git commit with artifacts
   - Include timestamps for all updates

4. **Standardization**: All agents follow same workflow pattern
   - Use agent-workflow.md as template
   - Follow subagent-return-format.md for returns
   - Implement all 8 stages consistently

### Positive Consequences

1. **Reliability**: Achieved 100% Stage 7 execution rate (up from ~80%)
2. **Consistency**: All agents execute workflow identically
3. **Maintainability**: Workflow changes require updating only agent template
4. **Simplicity**: Commands reduced from 800-1200 lines to 180-270 lines
5. **Clarity**: Clear ownership (agents own complete workflow)

### Negative Consequences

1. **Agent Complexity**: Agents are more complex (own complete workflow)
2. **Migration Effort**: Required migrating all commands and agents (one-time cost)
3. **Learning Curve**: Developers must understand 8-stage workflow

### Mitigation Strategies

1. **Agent Templates**: Provide templates implementing 8-stage workflow
2. **Documentation**: Document workflow pattern in development guide
3. **Code Review**: Ensure all agents implement Stage 7 correctly
4. **Validation**: Test Stage 7 execution in all validation reports

---

## Validation

### Success Criteria

- [x] 100% Stage 7 execution rate across all commands
- [x] All agents implement 8-stage workflow
- [x] All commands simplified to delegation layers
- [x] No functionality lost during migration

### Actual Results

- **Stage 7 Execution Rate**: 100% (up from ~80%)
- **Agent Compliance**: All 4 agents implement 8-stage workflow
- **Command Simplification**: 70-85% reduction in command file sizes
- **Functionality**: Zero regressions, all features working

**Validation Status**: ✅ [PASS] - All success criteria met

---

## Lessons Learned

1. **Single Ownership is Better**: Clear ownership improves reliability
2. **Stage 7 is Critical**: Artifact validation and status updates must be guaranteed
3. **Simplicity Wins**: Thin delegation layers are easier to maintain than embedded workflows
4. **Templates Help**: Agent templates ensure consistent implementation
5. **Validation is Essential**: Must test Stage 7 execution in all validations

---

## References

- **Implementation**: Task 245 (Phase 2: Core Architecture Migration)
- **Validation**: `.claude/specs/245_phase_2_core_architecture_migration/reports/validation-001.md`
- **Workflow Standard**: `.claude/context/core/standards/agent-workflow.md`
- **Return Format**: `.claude/context/core/standards/subagent-return-format.md`
- **Migration Guide**: `.claude/docs/migrations/001-openagents-migration/phase-2-guide.md`

---

**ADR Status**: Accepted and Implemented  
**Last Updated**: 2025-12-29
