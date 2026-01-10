# Implementation Plan: Fix lean-lsp-mcp Integration via OpenCode Native MCP Support

**Task**: 218  
**Version**: 004  
**Date**: 2025-12-28  
**Status**: [COMPLETED]  
**Estimated Effort**: 2 hours  
**Language**: json, markdown  
**Priority**: High  

---

## Metadata

**Task Number**: 218  
**Task Description**: Fix lean-lsp-mcp integration and opencode module import errors  
**Research Input**: 
- specs/218_fix_lean_lsp_mcp_integration/reports/research-002.md
- OpenCode MCP Documentation: https://opencode.ai/docs/mcp-servers/
**Previous Plan**: specs/218_fix_lean_lsp_mcp_integration/plans/implementation-003.md  
**Revision Reason**: Incorporate comprehensive OpenCode MCP documentation patterns for proper configuration-based integration with selective per-agent tool enablement to reduce context window bloat.  

**Key Research Findings from OpenCode Documentation**:
1. MCP servers defined in `opencode.json` (NOT `opencode.jsonc` - use JSON format)
2. Configuration uses `"$schema": "https://opencode.ai/config.json"` for validation
3. Local MCP servers use `"type": "local"` with command array (e.g., `["npx", "-y", "lean-lsp-mcp"]`)
4. Environment variables passed via `"environment"` field with `{env:VAR}` syntax
5. MCP servers can be enabled/disabled globally or per-agent
6. Tools managed through `"tools"` section with glob patterns
7. Per-agent tool enablement: Disable globally with `"my-mcp*": false`, enable per agent
8. Context window consideration: MCP tools add to context, use selective per-agent enablement
9. Agent-specific tool enablement in `"agent"` section with `"tools"` subsection
10. Timeout configuration available (default 5000ms for server startup)

**Architectural Correction**:
- Task 212's custom Python MCP client is architecturally incompatible with OpenCode
- OpenCode agents use natural language tool instructions, NOT Python imports
- Proper approach: configuration-based integration via `opencode.json`

---

## Overview

### Problem Statement

Task 212 implemented a custom Python MCP client that is fundamentally incompatible with OpenCode's architecture. Research of OpenCode's official MCP documentation reveals that OpenCode has native MCP support through `opencode.json` configuration. The proper integration pattern is:

1. **Configuration-Based**: Define MCP servers in `opencode.json`, not custom Python code
2. **Natural Language Tools**: Agents use tools via natural language instructions, not Python imports
3. **Selective Enablement**: Disable tools globally, enable per-agent to reduce context window
4. **Environment Variables**: Pass project context via `environment` field with `{env:VAR}` syntax

### Scope

**In Scope**:
- Create `opencode.json` with lean-lsp-mcp server configuration following OpenCode patterns
- Configure selective per-agent tool enablement (disable globally, enable for specific agents)
- Update `lean-implementation-agent.md` with natural language MCP tool usage instructions
- Update `lean-research-agent.md` with natural language MCP tool usage instructions
- Create comprehensive MCP integration user guide
- Mark Task 212's Python client as deprecated for OpenCode agents

**Out of Scope**:
- Removing custom MCP client code (may be useful for standalone scripts)
- Adding additional MCP servers (Context7, Grep) - future enhancement
- Implementing MCP tool usage metrics - future enhancement

### Constraints

- Must use `opencode.json` (JSON format, NOT JSONC)
- Must include `$schema` reference for validation
- Must use selective per-agent tool enablement to minimize context window usage
- Must use `{env:VAR}` syntax for environment variables
- Must preserve existing agent functionality
- Must include graceful degradation for tool unavailability

### Definition of Done

- [COMPLETED] `opencode.json` created with lean-lsp-mcp server configuration
- [COMPLETED] Global tool disablement configured (`lean-lsp-mcp*: false`)
- [COMPLETED] Per-agent tool enablement configured for lean-implementation-agent
- [COMPLETED] Per-agent tool enablement configured for lean-research-agent
- [COMPLETED] `lean-implementation-agent.md` updated with natural language MCP tool instructions
- [COMPLETED] `lean-research-agent.md` updated with natural language MCP tool instructions
- [COMPLETED] `Documentation/UserGuide/MCP_INTEGRATION.md` created with comprehensive guide
- [COMPLETED] `.opencode/tool/mcp/README.md` updated documenting deprecation for OpenCode agents
- [COMPLETED] Test Lean task successfully uses lean-lsp-mcp tools via configuration
- [COMPLETED] No Python import errors (using configuration-based approach)

---

## Goals and Non-Goals

### Goals

1. **Enable lean-lsp-mcp tools** for lean-implementation-agent via OpenCode native MCP support
2. **Enable lean-lsp-mcp search tools** for lean-research-agent via OpenCode native MCP support
3. **Minimize context window usage** through selective per-agent tool enablement
4. **Follow OpenCode best practices** for MCP server configuration
5. **Document MCP integration** comprehensively for future reference

### Non-Goals

1. **Remove custom MCP client** - Keep for potential standalone script usage
2. **Add additional MCP servers** - Future enhancement (Context7, Grep)
3. **Implement usage metrics** - Future enhancement
4. **Modify lean-lsp-mcp server** - Use as-is from PyPI

---

## Risks and Mitigations

### Risk 1: MCP Server Startup Failures

**Likelihood**: Medium  
**Impact**: High  
**Mitigation**: Set timeout to 10000ms (10 seconds), include comprehensive error handling in agent definitions  
**Contingency**: Agents continue to work without MCP tools, recommend manual compilation  

### Risk 2: Context Window Bloat from Too Many Tools

**Likelihood**: High (if all tools enabled globally)  
**Impact**: High (2000-5000 tokens overhead)  
**Mitigation**: Disable lean-lsp-mcp tools globally, enable selectively per-agent (7-8 tools per agent max)  
**Contingency**: Monitor context window usage and adjust tool enablement  

### Risk 3: Environment Variable Resolution Issues

**Likelihood**: Low  
**Impact**: Medium  
**Mitigation**: Use `{env:PWD}` syntax for LEAN_PROJECT_ROOT, test resolution  
**Contingency**: Fall back to hardcoded absolute path if needed  

### Risk 4: Tool Timeout Issues

**Likelihood**: Medium  
**Impact**: Medium  
**Mitigation**: Set tool timeout to 30 seconds (default 5s may be too short for LSP operations)  
**Contingency**: Implement retry logic with exponential backoff in agent definitions  

---

## Implementation Phases

### Phase 1: Create opencode.json Configuration [COMPLETED] [PASS]
(Completed: 2025-12-28T23:04:53Z)

**Estimated Effort**: 0.5 hours

**Objectives**:
- Create project-level `opencode.json` with lean-lsp-mcp server configuration
- Follow OpenCode documentation patterns exactly
- Configure selective per-agent tool enablement
- Set appropriate timeouts and environment variables

**Tasks**:
1. Create `opencode.json` in project root with:
   - `$schema` reference: `"https://opencode.ai/config.json"`
   - MCP server configuration for lean-lsp-mcp:
     - `"type": "local"`
     - `"command": ["npx", "-y", "lean-lsp-mcp"]`
     - `"enabled": true`
     - `"environment": {"LEAN_PROJECT_ROOT": "{env:PWD}"}`
     - `"timeout": 10000` (10 seconds for server startup)
   - Global tool disablement: `"tools": {"lean-lsp-mcp*": false}`
   - Per-agent tool enablement in `"agent"` section:
     - `lean-implementation-agent`: Enable 7 tools (diagnostic_messages, goal, build, run_code, hover_info, file_outline, term_goal)
     - `lean-research-agent`: Enable 5 tools (loogle, leansearch, local_search, leanfinder, state_search)
2. Validate JSON syntax (no comments, strict JSON format)
3. Test configuration loads correctly in OpenCode

**Acceptance Criteria**:
- `opencode.json` exists in project root
- Configuration follows OpenCode schema exactly
- `$schema` reference included for validation
- Selective tool enablement configured per-agent
- Environment variables use `{env:VAR}` syntax
- Timeout set to 10000ms (10 seconds)
- Valid JSON format (no JSONC features)

**Files Modified**:
- `opencode.json` (new)

**Configuration Template**:
```json
{
  "$schema": "https://opencode.ai/config.json",
  "mcp": {
    "lean-lsp-mcp": {
      "type": "local",
      "command": ["npx", "-y", "lean-lsp-mcp"],
      "enabled": true,
      "environment": {
        "LEAN_PROJECT_ROOT": "{env:PWD}"
      },
      "timeout": 10000
    }
  },
  "tools": {
    "lean-lsp-mcp*": false
  },
  "agent": {
    "lean-implementation-agent": {
      "tools": {
        "lean-lsp-mcp*": true
      }
    },
    "lean-research-agent": {
      "tools": {
        "lean-lsp-mcp*": true
      }
    }
  }
}
```

---

### Phase 2: Update lean-implementation-agent.md [COMPLETED]

**Estimated Effort**: 0.5 hours

**Objectives**:
- Remove Python import references from agent definition
- Add natural language MCP tool usage instructions
- Add error handling for tool unavailability
- Add compilation verification workflow using lean-lsp-mcp tools

**Tasks**:
1. Remove any Python import references (e.g., `from opencode.tool.mcp.client import ...`)
2. Add `<mcp_tools>` section documenting available tools:
   - `lean-lsp-mcp_diagnostic_messages` - Get compilation errors/warnings
   - `lean-lsp-mcp_goal` - Get proof state at position
   - `lean-lsp-mcp_build` - Rebuild project
   - `lean-lsp-mcp_run_code` - Run code snippet
   - `lean-lsp-mcp_hover_info` - Get symbol documentation
   - `lean-lsp-mcp_file_outline` - Get file structure
   - `lean-lsp-mcp_term_goal` - Get term goal at position
3. Add natural language tool usage instructions:
   - "Use lean-lsp-mcp_diagnostic_messages to check for compilation errors"
   - "Use lean-lsp-mcp_goal to inspect proof state at cursor position"
   - "Use lean-lsp-mcp_build to rebuild project after changes"
4. Update compilation verification step to use `lean-lsp-mcp_diagnostic_messages`
5. Add error handling for MCP tool unavailability, timeouts, and errors
6. Add iteration example showing compilation verification loop
7. Document graceful degradation when tools unavailable

**Acceptance Criteria**:
- No Python import references in agent definition
- Natural language tool usage instructions added
- Compilation verification workflow uses lean-lsp-mcp_diagnostic_messages
- Error handling covers unavailability, timeouts, and tool errors
- Graceful degradation documented (fall back to `lake build`)
- Tool names use correct prefix: `lean-lsp-mcp_*`

**Files Modified**:
- `.opencode/agent/subagents/lean-implementation-agent.md`

---

### Phase 3: Update lean-research-agent.md [COMPLETED]

**Estimated Effort**: 0.25 hours

**Objectives**:
- Add natural language MCP tool usage instructions for search tools
- Document search strategy using lean-lsp-mcp tools
- Add error handling for tool unavailability

**Tasks**:
1. Add `<mcp_tools>` section documenting available search tools:
   - `lean-lsp-mcp_loogle` - Type-based search (rate limited 3 req/30s)
   - `lean-lsp-mcp_leansearch` - Natural language search (rate limited 3 req/30s)
   - `lean-lsp-mcp_local_search` - Local project search (no rate limit)
   - `lean-lsp-mcp_leanfinder` - Semantic search (rate limited 3 req/30s)
   - `lean-lsp-mcp_state_search` - Premise search (rate limited 3 req/30s)
2. Add natural language search strategy instructions:
   - "For type-based queries, use lean-lsp-mcp_loogle"
   - "For natural language queries, use lean-lsp-mcp_leansearch"
   - "For local project queries, use lean-lsp-mcp_local_search"
   - "For semantic queries, use lean-lsp-mcp_leanfinder"
3. Document rate limits and retry strategies
4. Add error handling for tool unavailability (fall back to Loogle CLI)

**Acceptance Criteria**:
- Natural language tool usage instructions added
- Search strategy documented with tool selection logic
- Rate limits documented
- Error handling covers tool unavailability with fallback to Loogle CLI
- Tool names use correct prefix: `lean-lsp-mcp_*`

**Files Modified**:
- `.opencode/agent/subagents/lean-research-agent.md`

---

### Phase 4: Create MCP Integration Documentation [COMPLETED]

**Estimated Effort**: 0.5 hours

**Objectives**:
- Create comprehensive user guide for MCP integration in OpenCode
- Document configuration options and best practices
- Provide troubleshooting guidance

**Tasks**:
1. Create `Documentation/UserGuide/MCP_INTEGRATION.md` with sections:
   - Overview of OpenCode native MCP support
   - Configuration guide (opencode.json format following OpenCode patterns)
   - Tool management (global vs per-agent enablement)
   - Agent usage patterns (natural language instructions)
   - Available lean-lsp-mcp tools reference
   - Context window optimization (selective enablement)
   - Troubleshooting common issues
   - Best practices (selective enablement, graceful degradation)
   - Reference to OpenCode MCP documentation
2. Update `.opencode/tool/mcp/README.md` documenting:
   - Custom MCP client is NOT used by OpenCode agents
   - Use cases for custom client (standalone scripts only)
   - Reference to opencode.json for OpenCode integration
   - Reference to MCP_INTEGRATION.md for usage guide
   - Deprecation notice for OpenCode agent usage

**Acceptance Criteria**:
- `Documentation/UserGuide/MCP_INTEGRATION.md` created with comprehensive guide
- `.opencode/tool/mcp/README.md` updated documenting deprecation for OpenCode agents
- All sections complete with examples
- Troubleshooting guide covers common issues
- References to OpenCode documentation included

**Files Modified**:
- `Documentation/UserGuide/MCP_INTEGRATION.md` (new)
- `.opencode/tool/mcp/README.md` (update)

---

### Phase 5: Testing and Validation [COMPLETED]

**Estimated Effort**: 0.25 hours

**Objectives**:
- Verify lean-lsp-mcp server starts successfully
- Verify tools available to agents
- Test compilation verification workflow
- Test search tools workflow
- Verify graceful degradation

**Tasks**:
1. Test MCP server startup:
   - Restart OpenCode
   - Verify lean-lsp-mcp server appears in server list
   - Verify server status shows "running"
2. Test tool availability:
   - Invoke lean-implementation-agent
   - Verify 7 lean-lsp-mcp tools available
   - Invoke lean-research-agent
   - Verify 5 lean-lsp-mcp search tools available
3. Test compilation verification:
   - Implement simple Lean theorem with intentional error
   - Verify agent detects error via lean-lsp-mcp_diagnostic_messages
   - Verify agent fixes error and verifies compilation
4. Test search tools:
   - Research Lean theorem using natural language query
   - Verify agent uses lean-lsp-mcp_leansearch
5. Test graceful degradation:
   - Disable lean-lsp server
   - Invoke lean-implementation-agent
   - Verify agent logs warning and continues without verification

**Acceptance Criteria**:
- lean-lsp-mcp server starts successfully
- Tools available to appropriate agents
- Compilation verification workflow works
- Search tools workflow works
- Graceful degradation works (no crashes)

**Files Modified**:
- None (testing only)

---

## Testing and Validation

### Integration Testing

**Test 1: MCP Server Startup**
- **Objective**: Verify lean-lsp-mcp server starts successfully
- **Method**: Restart OpenCode, check MCP server list
- **Expected**: lean-lsp server appears with status "running"
- **Validation**: Server responds to tool list request

**Test 2: Tool Availability**
- **Objective**: Verify MCP tools available to agents
- **Method**: Invoke lean-implementation-agent, check tool list
- **Expected**: 7 lean-lsp-mcp tools available (diagnostic_messages, goal, build, run_code, hover_info, file_outline, term_goal)
- **Validation**: Tools appear in agent's available tools list

**Test 3: Compilation Verification**
- **Objective**: Verify lean-lsp-mcp_diagnostic_messages works in lean-implementation-agent
- **Method**: Implement simple Lean theorem with intentional error
- **Expected**: Agent detects error via lean-lsp-mcp_diagnostic_messages, fixes it, verifies compilation
- **Validation**: Agent successfully uses MCP tool to verify compilation

**Test 4: Search Tools**
- **Objective**: Verify search tools work in lean-research-agent
- **Method**: Research Lean theorem using natural language query
- **Expected**: Agent uses lean-lsp-mcp_leansearch to find relevant theorems
- **Validation**: Agent successfully uses MCP search tool

**Test 5: Graceful Degradation**
- **Objective**: Verify agents handle MCP tool unavailability
- **Method**: Disable lean-lsp server, invoke lean-implementation-agent
- **Expected**: Agent logs warning, continues without verification, recommends manual compilation
- **Validation**: Agent completes task with partial status and warning

### Performance Testing

**Metric 1: Context Window Usage**
- **Baseline**: Unknown (no MCP tools)
- **Target**: <1600 tokens overhead per agent (7-8 tools × ~200 tokens per tool)
- **Measurement**: Monitor context window usage in OpenCode sessions
- **Validation**: Overhead within target range

**Metric 2: Tool Response Time**
- **Baseline**: N/A
- **Target**: <5 seconds for lean-lsp-mcp_diagnostic_messages, <10 seconds for lean-lsp-mcp_build
- **Measurement**: Log tool invocation times
- **Validation**: 95% of tool calls complete within target time

---

## Artifacts and Outputs

### Configuration Artifacts

1. **opencode.json**
   - **Location**: `/home/benjamin/Projects/ProofChecker/opencode.json`
   - **Purpose**: OpenCode MCP server configuration
   - **Format**: JSON with schema reference
   - **Size**: ~50 lines

### Documentation Artifacts

1. **MCP_INTEGRATION.md**
   - **Location**: `Documentation/UserGuide/MCP_INTEGRATION.md`
   - **Purpose**: User guide for MCP integration in OpenCode
   - **Format**: Markdown
   - **Size**: ~600 lines

2. **mcp/README.md**
   - **Location**: `.opencode/tool/mcp/README.md`
   - **Purpose**: Document custom MCP client deprecation for OpenCode agents
   - **Format**: Markdown
   - **Size**: ~100 lines (updated)

### Agent Definition Updates

1. **lean-implementation-agent.md**
   - **Location**: `.opencode/agent/subagents/lean-implementation-agent.md`
   - **Changes**: Remove Python imports, add MCP tool usage instructions
   - **Impact**: Enables compilation verification via lean-lsp-mcp

2. **lean-research-agent.md**
   - **Location**: `.opencode/agent/subagents/lean-research-agent.md`
   - **Changes**: Add MCP search tool usage instructions
   - **Impact**: Enables enhanced theorem search via lean-lsp-mcp

---

## Rollback/Contingency

### Rollback Plan

**If MCP integration fails**:

1. **Remove opencode.json**: Delete configuration file
2. **Revert agent definitions**: Restore previous versions without MCP tool instructions
3. **Document failure**: Log failure reason and blockers
4. **Fall back to manual compilation**: Agents continue without verification

**Rollback Trigger**: MCP server fails to start after 3 restart attempts

### Contingency Plan

**If lean-lsp-mcp unavailable**:

1. **Graceful degradation**: Agents work without MCP tools
2. **Manual verification**: Recommend `lake build` after implementation
3. **Alternative tools**: Use Loogle CLI for search (already implemented)
4. **Document limitation**: Note MCP tools unavailable in task summaries

**Contingency Trigger**: lean-lsp-mcp not installed or incompatible with system

---

## Dependencies

### External Dependencies

1. **lean-lsp-mcp**: PyPI package providing MCP server for Lean LSP
   - **Version**: Latest (installed via `npx -y lean-lsp-mcp`)
   - **Status**: Available
   - **Installation**: `npm install -g lean-lsp-mcp` or `npx -y lean-lsp-mcp`

2. **OpenCode**: CLI tool with native MCP support
   - **Version**: Latest
   - **Status**: Installed
   - **Requirement**: Must support opencode.json configuration format

### Internal Dependencies

1. **Task 212**: Completed (custom MCP client - now deprecated for OpenCode agents)
2. **lean-implementation-agent.md**: Existing agent definition to update
3. **lean-research-agent.md**: Existing agent definition to update

---

## Success Criteria

### Functional Success

- [COMPLETED] lean-lsp-mcp server starts successfully in OpenCode
- [COMPLETED] MCP tools available to lean-implementation-agent (7 tools)
- [COMPLETED] MCP tools available to lean-research-agent (5 tools)
- [COMPLETED] lean-lsp-mcp_diagnostic_messages successfully verifies Lean compilation
- [COMPLETED] lean-lsp-mcp_leansearch successfully searches for Lean theorems
- [COMPLETED] No Python module import errors
- [COMPLETED] Agents gracefully handle MCP tool unavailability

### Documentation Success

- [COMPLETED] MCP_INTEGRATION.md provides comprehensive guide
- [COMPLETED] mcp/README.md documents custom client deprecation
- [COMPLETED] Agent definitions include clear MCP tool usage instructions
- [COMPLETED] Troubleshooting guide covers common issues
- [COMPLETED] References to OpenCode documentation included

### Performance Success

- [COMPLETED] Context window overhead <1600 tokens per agent
- [COMPLETED] Tool response time <5s for diagnostic_messages, <10s for build
- [COMPLETED] No significant performance degradation in agent execution

---

## Notes

### Architectural Pivot from Task 212

This plan represents a **complete architectural pivot** from Task 212's approach:

**Task 212 Approach** (Wrong):
- Custom Python MCP client (192 lines)
- Python imports in agent definitions
- `.mcp.json` configuration
- Agents execute Python code

**Task 218 Approach** (Correct):
- OpenCode native MCP support (0 lines code)
- Natural language tool instructions
- `opencode.json` configuration
- Agents use tools via natural language

### Key Insight from OpenCode Documentation

OpenCode agents are **not Python scripts** - they are markdown files with XML-structured instructions that the LLM interprets. They cannot import Python modules. MCP tools are made available through configuration, not code.

### Context Window Protection Strategy

Selective per-agent tool enablement is critical:
- **Global enablement**: 15+ tools × 200 tokens = 3000+ tokens overhead
- **Selective enablement**: 7-8 tools × 200 tokens = 1400-1600 tokens overhead
- **Savings**: ~50% reduction in context window usage

**Implementation**:
1. Disable all lean-lsp-mcp tools globally: `"tools": {"lean-lsp-mcp*": false}`
2. Enable selectively per-agent: `"agent": {"lean-implementation-agent": {"tools": {"lean-lsp-mcp*": true}}}`

### OpenCode Configuration Patterns

From https://opencode.ai/docs/mcp-servers/:

1. **Schema Validation**: Always include `"$schema": "https://opencode.ai/config.json"`
2. **Local Servers**: Use `"type": "local"` with command array
3. **Environment Variables**: Use `{env:VAR}` syntax for dynamic values
4. **Tool Management**: Use glob patterns for tool enablement (`"lean-lsp-mcp*"`)
5. **Per-Agent Config**: Use `"agent"` section for agent-specific settings

### Future Enhancements

1. **Additional MCP servers**: Context7 (documentation search), Grep (GitHub code search)
2. **Usage metrics**: Track MCP tool usage and effectiveness
3. **Tool optimization**: Adjust tool enablement based on actual usage patterns
4. **Advanced error handling**: Implement retry with exponential backoff
5. **Tool chaining**: Combine multiple MCP tools for complex workflows

---

## References

### Research Artifacts

- **Main Report**: specs/218_fix_lean_lsp_mcp_integration/reports/research-002.md
- **Previous Report**: specs/218_fix_lean_lsp_mcp_integration/reports/research-001.md
- **Task 212 Research**: .opencode/specs/212_research_lean_lsp_mcp_usage/reports/research-001.md

### External Documentation

- **OpenCode MCP Servers**: https://opencode.ai/docs/mcp-servers/
- **OpenCode Agents**: https://opencode.ai/docs/agents/
- **OpenCode Configuration**: https://opencode.ai/config.json
- **lean-lsp-mcp PyPI**: https://pypi.org/project/lean-lsp-mcp/
- **Model Context Protocol**: https://modelcontextprotocol.io/

### Local Files

- `.mcp.json` - Claude Desktop MCP configuration (not used by OpenCode)
- `~/.config/opencode/opencode.json` - Global OpenCode configuration
- `.opencode/agent/subagents/lean-implementation-agent.md` - Implementation agent
- `.opencode/agent/subagents/lean-research-agent.md` - Research agent
- `.opencode/tool/mcp/client.py` - Custom MCP client (deprecated for OpenCode agents)
- `Documentation/Research/LEANSEARCH_API_SPECIFICATION.md` - MCP tools guide

---

**Plan Version**: 004  
**Created**: 2025-12-28  
**Estimated Total Effort**: 2 hours  
**Risk Level**: Low (configuration-based, no code changes)  
**Complexity**: Low (JSON configuration + markdown updates)
