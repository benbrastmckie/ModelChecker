# Research Summary: Fix Verbose Artifact Output in Commands

**Task**: 202  
**Research Completed**: 2025-12-27  
**Effort Estimate**: 4-5 hours (full fix) or 1.25 hours (quick fix)

## Key Findings

Problem is **real but localized** to 2 legacy subagents, not all commands:

1. **Commands are correct**: /research, /plan, /implement, /revise, /review all specify concise return formats per subagent-return-format.md

2. **Newer subagents are correct**: researcher, lean-research-agent, planner follow subagent-return-format.md standard correctly

3. **Legacy subagents are verbose**: task-executor and batch-task-orchestrator (used by /implement) return 100-1000+ lines of verbose detail instead of following standard

4. **Root causes identified**:
   - task-executor returns full workflow tracking, coordinator results, verbose metadata (100+ lines vs ~10 lines expected)
   - batch-task-orchestrator aggregates full results from all tasks without summarization (1000+ lines for 10 tasks vs ~50 lines expected)
   - Both created before subagent-return-format.md was standardized (Task 191)

5. **Scope of fix**: Update 2 subagent files (task-executor.md, batch-task-orchestrator.md), not all commands

## Recommendations

### Full Standardization (Recommended, 4-5 hours)

Update both subagents to follow subagent-return-format.md standard:

- task-executor: Remove verbose internal tracking, return only status/summary/artifacts/metadata
- batch-task-orchestrator: Create batch-summary.md artifact for details, return only aggregate stats
- Impact: 90-95% context window reduction, no technical debt

### Quick Fix (Alternative, 1.25 hours)

Remove verbose fields without full standardization:

- task-executor: Remove internal tracking fields, truncate coordinator results
- batch-task-orchestrator: Replace full task results with concise summary array
- Impact: 80% context window reduction, leaves technical debt

## Implementation Approach

**Full Fix**:
1. Update task-executor return format (1.25h)
2. Update batch-task-orchestrator return format + create batch summary artifact (2.25h)
3. Test with /implement command (0.75h)
4. Update documentation (0.5h)

**Quick Fix**:
1. Remove verbose fields from task-executor (0.5h)
2. Condense batch-task-orchestrator output (0.75h)

## Impact

After fix:
- /implement command context window protected
- task-executor: 100+ lines → ~10 lines
- batch-task-orchestrator: 1000+ lines → ~50 lines
- Consistent return formats across all subagents

## Next Steps

1. Choose implementation approach (full or quick)
2. Create implementation plan for task 202
3. Execute fix
4. Verify context window reduction with tests
