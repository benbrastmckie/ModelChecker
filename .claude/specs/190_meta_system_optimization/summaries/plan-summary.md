# Plan Summary: Meta-System Optimization

**Version**: 001
**Complexity**: Moderate
**Estimated Effort**: 8 hours

## Key Steps

1. Preflight: Validate scope and load context references
2. Command Analysis: Review 15 commands for standards/commands.md compliance
3. Agent Analysis: Review 30+ agents/subagents for routing patterns and context allocation
4. Context Analysis: Identify context reference optimization opportunities using context-analyzer
5. Documentation Analysis: Verify plan.md compliance across all plan artifacts using doc-analyzer
6. Routing Analysis: Map command-agent-subagent flows and detect mismatches using dependency-mapper
7. Report Generation: Create comprehensive optimization report with prioritized recommendations
8. Postflight: Sync TODO/state and finalize artifacts

## Dependencies

- context-analyzer specialist (context usage patterns)
- doc-analyzer specialist (plan compliance checking)
- dependency-mapper specialist (routing flow mapping)
- style-checker specialist (standards compliance)

## Success Criteria

- All commands analyzed for YAML front matter, XML section order, and standards compliance
- All agents analyzed for routing patterns, context allocation, and lazy directory creation
- Context optimization opportunities identified and documented
- Command-agent-subagent flows mapped for all 15 commands
- Optimization report created with actionable, prioritized recommendations
- Summary artifact created (3-5 sentences, <100 tokens)
- TODO.md and state.json synchronized

## Full Plan

See: .opencode/specs/190_meta_system_optimization/plans/implementation-001.md
