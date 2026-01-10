# Research Summary: Orchestrator.md Improvements

**Task**: 214  
**Date**: 2025-12-28  
**Status**: Completed  

---

## Overview

Research completed on three orchestrator.md improvements: FIX comment resolution, XML styling application, and default agent configuration. Found clear solutions for all three objectives with total estimated implementation time of 2 hours 15 minutes.

---

## Key Findings

### FIX Comment (Line 14)

- **Issue**: Document uses historical comparisons ("Key Improvements Over v1", "Problems Solved") that reference past system state
- **Solution**: Rewrite as "Core Capabilities" and "Delegation Safety Features" presenting current features directly
- **Effort**: 30 minutes
- **Impact**: Improves clarity, professionalism, and maintainability

### XML Styling

- **Pattern**: All subagents use consistent XML tags: `<context>`, `<role>`, `<task>`, `<process_flow>`, `<step_N>`, `<constraints>`, `<output_specification>`, `<validation_checks>`, `<{agent}_principles>`
- **Mapping**: Orchestrator sections map cleanly to XML structure with some orchestrator-specific tags (`<delegation_registry>`, `<context_loading>`, `<registry_maintenance>`)
- **Effort**: 1.5 hours
- **Impact**: Consistency with other agents, better structure, improved LLM context
- **Compatibility**: Backward compatible - commands reference orchestrator by path, not by parsing structure

### Default Agent Configuration

- **CRITICAL FINDING**: AGENTS.md is for custom instructions (rules), NOT agent definitions
- **Renaming orchestrator.md to AGENTS.md would BREAK the orchestrator**
- **Correct location**: `.opencode/agent/orchestrator.md` (current location is correct)
- **Default agent**: Built-in "build" agent is hardcoded default (not configurable via AGENTS.md)
- **Invocation**: Users press Tab to switch to orchestrator or use `@orchestrator` mention
- **Recommendation**: Keep current location, optionally add to `opencode.json` for configuration

---

## Top Recommendations

1. **Rewrite Historical Sections** (High Priority, 30 min)
   - Replace "Key Improvements Over v1" with "Core Capabilities"
   - Replace "Problems Solved" with "Delegation Safety Features"
   - Remove version number and creation date
   - Present current features, not historical fixes

2. **Apply XML Styling** (Medium Priority, 1.5 hours)
   - Add YAML frontmatter
   - Wrap sections in XML tags following subagent pattern
   - Add `<orchestrator_principles>` section
   - Maintain backward compatibility

3. **Keep Current Agent Location** (High Priority, No Change)
   - Do NOT rename to AGENTS.md
   - Keep at `.opencode/agent/orchestrator.md`
   - Document usage (Tab key or `@orchestrator`)

4. **Document Agent Usage** (Medium Priority, 15 min)
   - Add "Usage" section explaining invocation
   - Clarify relationship to built-in agents

---

## Implementation Estimate

**Total Effort**: 2 hours 15 minutes

**Breakdown**:
- Rewrite historical sections: 30 min (High priority)
- Apply XML styling: 1.5 hours (Medium priority)
- Document agent usage: 15 min (Medium priority)

**Implementation Order**:
1. Rewrite historical sections (quick win)
2. Apply XML styling (larger effort)
3. Document agent usage (quick win)

---

## Next Steps

Review research findings and create implementation plan with `/plan 214` to execute all three improvements in logical phases.

---

## Full Report

See detailed analysis, code examples, and sources in:  
`.opencode/specs/214_orchestrator_improvements/reports/research-001.md`
