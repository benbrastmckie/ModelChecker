# Implementation Plan: Fix lean-lsp-mcp Integration and OpenCode Module Import Errors

**Task**: 218  
**Version**: 003  
**Date**: 2025-12-28  
**Status**: [NOT STARTED]  
**Estimated Effort**: 1.5 hours  
**Language**: python, markdown, json  
**Priority**: High  

---

## Metadata

**Task Number**: 218  
**Task Description**: Fix lean-lsp-mcp integration and opencode module import errors  
**Research Input**: specs/218_fix_lean_lsp_mcp_integration_and_opencode_module_import_errors/reports/research-001.md  
**Previous Plan**: specs/218_fix_lean_lsp_mcp_integration_and_opencode_module_import_errors/plans/implementation-002.md (obsolete)  
**Revision Reason**: Research discovered OpenCode has native MCP support via opencode.json configuration. Task 212's custom Python MCP client approach is architecturally incompatible. Complete pivot required from Python-based integration to configuration-based integration.  

**Key Research Findings**:
1. OpenCode uses `opencode.json` for MCP server configuration, NOT `.mcp.json`
2. OpenCode agents use natural language tool instructions, not Python imports
3. ModuleNotFoundError is symptom of wrong architectural approach, not missing files
4. Proper approach: configuration-based integration enables 15+ lean-lsp-mcp tools
5. Previous __init__.py plan obsolete - complete architectural pivot required

---

## Overview

### Problem Statement

Task 212 implemented a custom Python MCP client (`.opencode/tool/mcp/client.py`) that agents would import and use programmatically. This approach is fundamentally incompatible with OpenCode's architecture:

1. **Wrong Configuration File**: Used `.mcp.json` (for Claude Desktop) instead of `opencode.json` (for OpenCode)
2. **Wrong Integration Pattern**: Custom Python client instead of OpenCode's native MCP support
3. **Wrong Agent Pattern**: Python imports instead of natural language tool instructions
4. **Module Import Errors**: Agents cannot import Python modules - they are markdown files with XML-structured instructions

Research revealed that OpenCode has built-in MCP server support that automatically makes MCP tools available to agents once configured in `opencode.json`. No custom client code is needed.

### Scope

**In Scope**:
- Create `opencode.json` with lean-lsp-mcp server configuration
- Update `lean-implementation-agent.md` to use natural language MCP tool instructions
- Update `lean-research-agent.md` to use natural language MCP tool instructions
- Create `Documentation/UserGuide/MCP_INTEGRATION.md` user guide
- Mark `.opencode/tool/mcp/client.py` as deprecated (incompatible with OpenCode architecture)

**Out of Scope**:
- Removing custom MCP client code (may be useful for standalone scripts)
- Adding additional MCP servers (Context7, Grep) - future enhancement
- Implementing MCP tool usage metrics - future enhancement

### Constraints

- Must use `opencode.json` configuration format, not `.mcp.json`
- Must use absolute paths in environment variables
- Must enable MCP tools selectively per-agent to reduce context window usage
- Must include graceful degradation for tool unavailability
- Must preserve existing agent functionality

### Definition of Done

- [NOT STARTED] `opencode.json` created with lean-lsp-mcp server configuration
- [NOT STARTED] `lean-implementation-agent.md` updated with natural language MCP tool usage instructions
- [NOT STARTED] `lean-research-agent.md` updated with natural language MCP tool usage instructions
- [NOT STARTED] `Documentation/UserGuide/MCP_INTEGRATION.md` created with comprehensive guide
- [NOT STARTED] `.opencode/tool/mcp/README.md` created documenting deprecation for OpenCode agents
- [NOT STARTED] Test Lean task successfully uses lean-lsp-mcp tools via configuration
- [NOT STARTED] No Python import errors (using configuration-based approach)

---

## Goals and Non-Goals

### Goals

1. **Enable lean-lsp-mcp tools** for lean-implementation-agent via OpenCode native MCP support
2. **Enable lean-lsp-mcp search tools** for lean-research-agent via OpenCode native MCP support
3. **Eliminate module import errors** by removing Python import approach
4. **Reduce context window usage** through selective per-agent tool enablement
5. **Document MCP integration** for future reference and maintenance

### Non-Goals

1. **Remove custom MCP client** - Keep for potential standalone script usage
2. **Add additional MCP servers** - Future enhancement (Context7, Grep)
3. **Implement usage metrics** - Future enhancement
4. **Modify lean-lsp-mcp server** - Use as-is from PyPI

---

## Risks and Mitigations

### Risk 1: OpenCode Configuration Format Changes

**Likelihood**: Low  
**Impact**: Medium  
**Mitigation**: Use `$schema` reference to official OpenCode config schema for validation  
**Contingency**: Monitor OpenCode documentation for config format updates  

### Risk 2: MCP Server Startup Failures

**Likelihood**: Medium  
**Impact**: High  
**Mitigation**: Include comprehensive error handling and graceful degradation in agent definitions  
**Contingency**: Agents continue to work without MCP tools, recommend manual compilation  

### Risk 3: Tool Timeout Issues

**Likelihood**: Medium  
**Impact**: Medium  
**Mitigation**: Set timeout to 30 seconds (default 5s may be too short for LSP operations)  
**Contingency**: Implement retry logic with exponential backoff in agent definitions  

### Risk 4: Context Window Bloat from Too Many Tools

**Likelihood**: High (if all tools enabled globally)  
**Impact**: High  
**Mitigation**: Disable lean_* tools globally, enable selectively per-agent (7-8 tools per agent max)  
**Contingency**: Monitor context window usage and adjust tool enablement  

---

## Implementation Phases

### Phase 1: Create opencode.json Configuration [NOT STARTED]

**Estimated Effort**: 0.5 hours

**Objectives**:
- Create project-level `opencode.json` with lean-lsp-mcp server configuration
- Configure selective per-agent tool enablement
- Set appropriate timeouts and environment variables

**Tasks**:
1. Create `opencode.json` in project root with:
   - MCP server configuration for lean-lsp-mcp
   - Global tool disablement (`lean_*: false`)
   - Per-agent tool enablement for lean-implementation-agent (7 tools)
   - Per-agent tool enablement for lean-research-agent (5 tools)
   - Absolute path for LEAN_PROJECT_PATH environment variable
   - 30-second timeout for MCP tool responses
2. Validate JSON syntax and schema reference
3. Document configuration options inline with comments (if JSON5 supported)

**Acceptance Criteria**:
- `opencode.json` exists in project root
- Configuration follows OpenCode schema
- Absolute paths used for all environment variables
- Selective tool enablement configured per-agent
- Timeout set to 30000ms (30 seconds)

**Files Modified**:
- `opencode.json` (new)

---

### Phase 2: Update lean-implementation-agent.md [NOT STARTED]

**Estimated Effort**: 0.5 hours

**Objectives**:
- Remove Python import references from agent definition
- Add natural language MCP tool usage instructions
- Add error handling for tool unavailability
- Add compilation verification workflow using lean-lsp-mcp tools

**Tasks**:
1. Remove any Python import references (e.g., `from opencode.tool.mcp.client import ...`)
2. Add `<tool_usage>` section documenting available MCP tools:
   - `lean_diagnostic_messages` - Get compilation errors/warnings
   - `lean_goal` - Get proof state at position
   - `lean_build` - Rebuild project
   - `lean_run_code` - Run code snippet
   - `lean_hover_info` - Get symbol documentation
   - `lean_file_outline` - Get file structure
   - `lean_term_goal` - Get term goal at position
3. Update compilation verification step to use `lean_diagnostic_messages`
4. Add error handling for MCP tool unavailability, timeouts, and errors
5. Add iteration example showing compilation verification loop
6. Document graceful degradation when tools unavailable

**Acceptance Criteria**:
- No Python import references in agent definition
- Natural language tool usage instructions added
- Compilation verification workflow uses lean_diagnostic_messages
- Error handling covers unavailability, timeouts, and tool errors
- Graceful degradation documented

**Files Modified**:
- `.opencode/agent/subagents/lean-implementation-agent.md`

---

### Phase 3: Update lean-research-agent.md [NOT STARTED]

**Estimated Effort**: 0.25 hours

**Objectives**:
- Add natural language MCP tool usage instructions for search tools
- Document search strategy using lean-lsp-mcp tools
- Add error handling for tool unavailability

**Tasks**:
1. Add `<tool_usage>` section documenting available MCP search tools:
   - `lean_loogle` - Type-based search (rate limited 3 req/30s)
   - `lean_leansearch` - Natural language search (rate limited 3 req/30s)
   - `lean_local_search` - Local project search (no rate limit)
   - `lean_leanfinder` - Semantic search (rate limited 3 req/30s)
   - `lean_state_search` - Premise search (rate limited 3 req/30s)
2. Add search strategy workflow:
   - Type-based queries → lean_loogle
   - Natural language queries → lean_leansearch
   - Local project queries → lean_local_search
   - Semantic queries → lean_leanfinder
3. Document rate limits and retry strategies
4. Add error handling for tool unavailability (fall back to Loogle CLI)

**Acceptance Criteria**:
- Natural language tool usage instructions added
- Search strategy documented with tool selection logic
- Rate limits documented
- Error handling covers tool unavailability with fallback to Loogle CLI

**Files Modified**:
- `.opencode/agent/subagents/lean-research-agent.md`

---

### Phase 4: Create MCP Integration Documentation [NOT STARTED]

**Estimated Effort**: 0.25 hours

**Objectives**:
- Create comprehensive user guide for MCP integration in OpenCode
- Document configuration options and best practices
- Provide troubleshooting guidance

**Tasks**:
1. Create `Documentation/UserGuide/MCP_INTEGRATION.md` with sections:
   - Overview of OpenCode native MCP support
   - Configuration guide (opencode.json format)
   - Tool management (global vs per-agent enablement)
   - Agent usage patterns (natural language instructions)
   - Available lean-lsp-mcp tools reference
   - Troubleshooting common issues
   - Best practices (selective enablement, graceful degradation)
2. Create `.opencode/tool/mcp/README.md` documenting:
   - Custom MCP client is NOT used by OpenCode agents
   - Use cases for custom client (standalone scripts only)
   - Reference to opencode.json for OpenCode integration
   - Reference to MCP_INTEGRATION.md for usage guide

**Acceptance Criteria**:
- `Documentation/UserGuide/MCP_INTEGRATION.md` created with comprehensive guide
- `.opencode/tool/mcp/README.md` created documenting deprecation for OpenCode agents
- All sections complete with examples
- Troubleshooting guide covers common issues

**Files Modified**:
- `Documentation/UserGuide/MCP_INTEGRATION.md` (new)
- `.opencode/tool/mcp/README.md` (new)

---

## Testing and Validation

### Unit Testing

**Not Applicable**: Configuration-based integration has no code to unit test.

### Integration Testing

**Test 1: MCP Server Startup**
- **Objective**: Verify lean-lsp-mcp server starts successfully
- **Method**: Restart OpenCode, check MCP server list
- **Expected**: lean-lsp server appears in `opencode mcp list`
- **Validation**: Server status shows "running"

**Test 2: Tool Availability**
- **Objective**: Verify MCP tools available to agents
- **Method**: Invoke lean-implementation-agent, check tool list
- **Expected**: 7 lean-lsp-mcp tools available (diagnostic_messages, goal, build, run_code, hover_info, file_outline, term_goal)
- **Validation**: Tools appear in agent's available tools list

**Test 3: Compilation Verification**
- **Objective**: Verify lean_diagnostic_messages works in lean-implementation-agent
- **Method**: Implement simple Lean theorem with intentional error
- **Expected**: Agent detects error via lean_diagnostic_messages, fixes it, verifies compilation
- **Validation**: Agent successfully uses MCP tool to verify compilation

**Test 4: Search Tools**
- **Objective**: Verify search tools work in lean-research-agent
- **Method**: Research Lean theorem using natural language query
- **Expected**: Agent uses lean_leansearch to find relevant theorems
- **Validation**: Agent successfully uses MCP search tool

**Test 5: Graceful Degradation**
- **Objective**: Verify agents handle MCP tool unavailability
- **Method**: Disable lean-lsp server, invoke lean-implementation-agent
- **Expected**: Agent logs warning, continues without verification, recommends manual compilation
- **Validation**: Agent completes task with partial status and warning

### Performance Testing

**Metric 1: Context Window Usage**
- **Baseline**: Unknown (no MCP tools)
- **Target**: <2000 tokens overhead per agent (7-8 tools × ~200 tokens per tool)
- **Measurement**: Monitor context window usage in OpenCode sessions
- **Validation**: Overhead within target range

**Metric 2: Tool Response Time**
- **Baseline**: N/A
- **Target**: <5 seconds for lean_diagnostic_messages, <10 seconds for lean_build
- **Measurement**: Log tool invocation times
- **Validation**: 95% of tool calls complete within target time

---

## Artifacts and Outputs

### Configuration Artifacts

1. **opencode.json**
   - **Location**: `/home/benjamin/Projects/ProofChecker/opencode.json`
   - **Purpose**: OpenCode MCP server configuration
   - **Format**: JSON with schema reference
   - **Size**: ~100 lines

### Documentation Artifacts

1. **MCP_INTEGRATION.md**
   - **Location**: `Documentation/UserGuide/MCP_INTEGRATION.md`
   - **Purpose**: User guide for MCP integration in OpenCode
   - **Format**: Markdown
   - **Size**: ~500 lines

2. **mcp/README.md**
   - **Location**: `.opencode/tool/mcp/README.md`
   - **Purpose**: Document custom MCP client deprecation for OpenCode agents
   - **Format**: Markdown
   - **Size**: ~50 lines

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
   - **Version**: Latest (installed via `uvx lean-lsp-mcp`)
   - **Status**: Available
   - **Installation**: `pip install lean-lsp-mcp` or `uvx lean-lsp-mcp`

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

- [NOT STARTED] lean-lsp-mcp server starts successfully in OpenCode
- [NOT STARTED] MCP tools available to lean-implementation-agent (7 tools)
- [NOT STARTED] MCP tools available to lean-research-agent (5 tools)
- [NOT STARTED] lean_diagnostic_messages successfully verifies Lean compilation
- [NOT STARTED] lean_leansearch successfully searches for Lean theorems
- [NOT STARTED] No Python module import errors
- [NOT STARTED] Agents gracefully handle MCP tool unavailability

### Documentation Success

- [NOT STARTED] MCP_INTEGRATION.md provides comprehensive guide
- [NOT STARTED] mcp/README.md documents custom client deprecation
- [NOT STARTED] Agent definitions include clear MCP tool usage instructions
- [NOT STARTED] Troubleshooting guide covers common issues

### Performance Success

- [NOT STARTED] Context window overhead <2000 tokens per agent
- [NOT STARTED] Tool response time <5s for diagnostic_messages, <10s for build
- [NOT STARTED] No significant performance degradation in agent execution

---

## Notes

### Architectural Pivot

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

### Key Insight

OpenCode agents are **not Python scripts** - they are markdown files with XML-structured instructions that the LLM interprets. They cannot import Python modules. MCP tools are made available through configuration, not code.

### Context Window Protection

Selective per-agent tool enablement is critical:
- **Global enablement**: 15+ tools × 200 tokens = 3000+ tokens overhead
- **Selective enablement**: 7-8 tools × 200 tokens = 1400-1600 tokens overhead
- **Savings**: ~50% reduction in context window usage

### Future Enhancements

1. **Additional MCP servers**: Context7 (documentation search), Grep (GitHub code search)
2. **Usage metrics**: Track MCP tool usage and effectiveness
3. **Tool optimization**: Adjust tool enablement based on actual usage patterns
4. **Advanced error handling**: Implement retry with exponential backoff
5. **Tool chaining**: Combine multiple MCP tools for complex workflows

---

## References

### Research Artifacts

- **Main Report**: specs/218_fix_lean_lsp_mcp_integration_and_opencode_module_import_errors/reports/research-001.md
- **Task 212 Research**: .opencode/specs/212_research_lean_lsp_mcp_usage/reports/research-001.md

### External Documentation

- [OpenCode MCP Servers](https://opencode.ai/docs/mcp-servers/)
- [OpenCode Agents](https://opencode.ai/docs/agents/)
- [lean-lsp-mcp PyPI](https://pypi.org/project/lean-lsp-mcp/)
- [Model Context Protocol](https://modelcontextprotocol.io/)

### Local Files

- `.mcp.json` - Claude Desktop MCP configuration (not used by OpenCode)
- `~/.config/opencode/opencode.json` - Global OpenCode configuration
- `.opencode/agent/subagents/lean-implementation-agent.md` - Implementation agent
- `.opencode/agent/subagents/lean-research-agent.md` - Research agent
- `.opencode/tool/mcp/client.py` - Custom MCP client (deprecated for OpenCode agents)
- `Documentation/Research/LEANSEARCH_API_SPECIFICATION.md` - MCP tools guide

---

**Plan Version**: 003  
**Created**: 2025-12-28  
**Estimated Total Effort**: 1.5 hours  
**Risk Level**: Low (configuration-based, no code changes)  
**Complexity**: Low (JSON configuration + markdown updates)
