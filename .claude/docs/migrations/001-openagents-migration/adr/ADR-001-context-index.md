# ADR-001: Context Index (Lazy-Loading Pattern)

**Status**: Accepted  
**Date**: 2025-12-28  
**Decision Makers**: ProofChecker Development Team  
**Related Tasks**: Task 244 (Phase 1)

---

## Context and Problem Statement

The original OpenCode system loaded all context files during command routing, consuming 30-40% of the 100k context window before any actual work began. This created several problems:

1. **Context Window Bloat**: 30-40k tokens consumed just for routing
2. **Slow Routing**: Loading 15+ context files added latency
3. **Unnecessary Loading**: Most context files weren't needed for routing
4. **Maintenance Burden**: Adding new context files increased routing overhead
5. **Scalability Issues**: System couldn't scale beyond ~20 context files

**Key Question**: How can we reduce context window usage during routing while maintaining access to all necessary context?

---

## Decision Drivers

1. **Context Window Efficiency**: Must reduce routing context to <10% of total window
2. **Maintainability**: Solution must be easy to maintain and extend
3. **Discoverability**: Developers must be able to find available context files
4. **Backward Compatibility**: Existing agents must continue to work
5. **Performance**: Solution must not add significant latency

---

## Considered Options

### Option 1: Full Loading (Status Quo)

**Description**: Continue loading all context files during routing.

**Pros**:
- No changes required
- All context immediately available
- Simple implementation

**Cons**:
- 30-40% context window usage during routing
- Doesn't scale beyond ~20 context files
- Slow routing performance
- Maintenance burden

**Verdict**: ❌ Rejected - Doesn't solve the problem

### Option 2: No Index (Agent Discovery)

**Description**: Remove all context loading. Agents discover and load context files as needed.

**Pros**:
- Zero routing context usage
- Maximum flexibility for agents
- No central index to maintain

**Cons**:
- Poor discoverability (agents don't know what's available)
- Inconsistent context loading across agents
- No standardization
- Difficult to maintain

**Verdict**: ❌ Rejected - Poor discoverability and maintainability

### Option 3: Lazy-Loading with Context Index (Selected)

**Description**: Create `.claude/context/index.md` as single entry point. Index lists all available context files with descriptions. Agents load only required context files on-demand.

**Pros**:
- Minimal routing context (only index loaded, ~2-3k tokens)
- Excellent discoverability (index lists all available context)
- Standardized approach (all agents use same index)
- Scalable (can add unlimited context files)
- Backward compatible (agents can still load context directly)

**Cons**:
- Requires maintaining index file
- Agents must explicitly load context (not automatic)
- Initial implementation effort

**Verdict**: ✅ **Selected** - Best balance of efficiency, discoverability, and maintainability

---

## Decision Outcome

**Chosen Option**: Lazy-Loading with Context Index (Option 3)

### Implementation

1. **Create Context Index**: `.claude/context/index.md`
   - Lists all available context files
   - Provides brief description of each file
   - Organized by category (common, agents, commands, etc.)
   - Includes file paths for easy loading

2. **Orchestrator Loading**: Load only index during routing
   - Orchestrator loads `.claude/context/index.md`
   - Total routing context: ~2-3k tokens (vs 30-40k before)
   - 85-87% reduction in routing context

3. **Agent Loading**: Agents load context on-demand
   - Agents read index to discover available context
   - Agents load only required context files
   - Context loaded after routing (not during)

4. **Index Maintenance**: Keep index updated
   - Add new context files to index when created
   - Remove obsolete files from index
   - Update descriptions as files evolve

### Positive Consequences

1. **Context Window Efficiency**: Reduced routing context from 30-40% to 5%
2. **Scalability**: Can now support unlimited context files
3. **Discoverability**: Developers can easily find available context
4. **Performance**: Faster routing (only index loaded)
5. **Maintainability**: Single file to maintain (index)

### Negative Consequences

1. **Index Maintenance**: Must keep index updated (low burden)
2. **Agent Complexity**: Agents must explicitly load context (minor increase)
3. **Initial Migration**: Required migrating all commands and agents (one-time cost)

### Mitigation Strategies

1. **Index Maintenance**: Include index updates in code review checklist
2. **Agent Templates**: Provide templates showing how to load context
3. **Documentation**: Document lazy-loading pattern in development guide

---

## Validation

### Success Criteria

- [x] Routing context usage <10% of total window
- [x] All context files listed in index
- [x] Agents can discover and load context on-demand
- [x] No functionality lost during migration

### Actual Results

- **Routing Context**: 5% of total window (well below 10% target)
- **Index Completeness**: All 5 core context files listed
- **Agent Compatibility**: All agents successfully load context on-demand
- **Functionality**: Zero regressions, 100% Stage 7 execution rate

**Validation Status**: ✅ [PASS] - All success criteria met

---

## Lessons Learned

1. **Lazy-Loading is Effective**: Reduced context usage by 85-87%
2. **Index is Essential**: Provides discoverability without loading all files
3. **Maintenance is Minimal**: Index updates are quick and infrequent
4. **Pattern is Reusable**: Can apply to other systems with large context requirements

---

## References

- **Implementation**: Task 244 (Phase 1: Context Index and /research Prototype)
- **Validation**: `.claude/specs/244_phase_1_context_index_and_research_prototype/reports/validation-001.md`
- **Context Index**: `.claude/context/index.md`
- **Migration Guide**: `.claude/docs/migrations/001-openagents-migration/phase-1-guide.md`

---

**ADR Status**: Accepted and Implemented  
**Last Updated**: 2025-12-29
