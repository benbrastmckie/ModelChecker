# Research Summary: --divide Flag Implementation

**Project**: #189  
**Date**: 2025-12-25  
**Research Mode**: Standard  

## Key Findings

1. **Flag Implementation**: Use boolean `--divide` flag after task number, parsed in research.md ParseInput stage, passed to researcher agent. Pattern follows existing --lang and --simple/--complex flags. Incompatible with batch mode (error clearly).

2. **Topic Subdivision**: Use 3-5 subtopics with hierarchical decomposition for complex topics. Subdivision happens within researcher agent (stage 1.5) using criteria: breadth, orthogonality, depth, balance, coherence. Simple topics get 3 flat subtopics, complex topics get 5 hierarchical subtopics.

3. **Multi-Agent Coordination**: Vertical orchestration pattern with parallel execution. Researcher coordinates multiple web-research-specialist instances (one per subtopic), collects results, aggregates findings. Graceful degradation: partial success acceptable if >50% subtopics complete.

4. **Summary Structure**: Three-tier hierarchical summarization: (1) individual subtopic reports in reports/, (2) aggregated summary in summaries/ (<500 tokens), (3) return to orchestrator (<100 tokens). Cross-references between related subtopics, metadata tracking (subtopic count, sources, duration).

5. **Lazy Creation**: summaries/ directory created ONLY when --divide flag used and writing aggregated summary. Standard research (no --divide) creates no summaries/ directory. Project root + reports/ created when writing first subtopic report (same timing as current behavior).

## Most Relevant Resources

- **Web Research Report**: [web-research-findings.md](../reports/web-research-findings.md) - Multi-agent coordination patterns, topic subdivision strategies, hierarchical summarization
- **Codebase Analysis**: research.md, researcher.md, implement.md - Existing flag patterns, lazy creation rules, status tracking
- **Standards**: artifact-management.md, status-markers.md - Lazy creation rules, status transitions, state tracking

## Recommendations

1. **Implement in 5 phases**: (1) Command updates (research.md flag parsing), (2) Researcher agent updates (subdivision + coordination), (3) State tracking (research_mode field), (4) Documentation, (5) Testing. Total effort: 8-10 hours.

2. **Use 3-5 subtopics with vertical orchestration**: Optimal balance between coverage and complexity. Parallel execution with graceful degradation (partial success acceptable).

3. **Enforce token limits**: <500 tokens for aggregated summary, <100 tokens for orchestrator return. Use hierarchical summarization to protect context windows.

## Backward Compatibility

No breaking changes. Standard research (no --divide) works unchanged. Divided research (--divide) is additive feature. No migration needed. Status transitions unchanged ([NOT STARTED] → [IN PROGRESS] → [RESEARCHED]).

## Full Report

See: [research-001.md](../reports/research-001.md)
