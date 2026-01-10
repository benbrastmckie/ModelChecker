# Implementation Plan: Fix lean-lsp-mcp Integration Using Official MCP SDK

- **Task**: 218 - Fix lean-lsp-mcp integration and opencode module import errors
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours (90 minutes)
- **Priority**: High
- **Dependencies**: 212 (completed)
- **Research Inputs**: 
  - Main Report: .opencode/specs/218_fix_lean_lsp_mcp_integration/reports/research-002.md
  - Previous Report: .opencode/specs/218_fix_lean_lsp_mcp_integration/reports/research-001.md
  - Summary: .opencode/specs/218_fix_lean_lsp_mcp_integration/summaries/research-summary-002.md
- **Artifacts**: plans/implementation-002.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/tasks.md
- **Language**: python
- **Lean Intent**: false
- **Plan Version**: 2 (revised based on research-002.md findings)
- **Revision Reason**: Research-002.md identified that the original plan's approach (adding __init__.py files and configuring PYTHONPATH) does not follow MCP best practices. The recommended approach uses the official MCP Python SDK with stdio transport to spawn lean-lsp-mcp as a subprocess, following the same pattern as Claude Desktop, VSCode, and other MCP clients. This approach is simpler (no PYTHONPATH configuration needed), faster (1.5 hours vs 3-4.5 hours), and more maintainable (SDK handles protocol updates).

## Overview

The current implementation plan attempts to fix import errors by adding `__init__.py` files and configuring PYTHONPATH, but this approach does not follow MCP best practices. Research-002.md reveals that MCP servers are designed to run as **separate processes** communicating via stdio transport, not as importable Python modules. The official MCP Python SDK (`mcp` package) provides all necessary functionality for client-server communication.

**Key Insight**: The problem is not "how to import the MCP client wrapper" but rather "how should OpenCode integrate with MCP servers" - and the answer is: **through the MCP protocol itself using the official SDK**, not through Python imports.

This revised plan replaces the custom wrapper approach with a proper MCP client using the official SDK, eliminating the need for `__init__.py` files, PYTHONPATH configuration, and custom protocol implementation.

## Goals & Non-Goals

**Goals**:
- Install official MCP Python SDK (`mcp` package)
- Create proper MCP client using `ClientSession` and stdio transport
- Implement synchronous convenience functions for lean-implementation-agent
- Test end-to-end integration with lean-lsp-mcp server
- Update documentation to reflect MCP SDK usage
- Preserve graceful degradation to lake build when MCP unavailable

**Non-Goals**:
- Create `__init__.py` files (not needed with MCP SDK approach)
- Configure PYTHONPATH (not needed with MCP SDK approach)
- Maintain custom MCP protocol wrapper (replaced by SDK)
- Support importing lean-lsp-mcp as Python module (not how MCP works)

## Risks & Mitigations

- **Risk**: MCP SDK may have compatibility issues with lean-lsp-mcp
  - **Mitigation**: lean-lsp-mcp uses MCP SDK v1.25.0 internally, ensuring compatibility. Test with MCP Inspector before agent integration.

- **Risk**: Async/await pattern may complicate agent code
  - **Mitigation**: Provide synchronous wrapper functions using `asyncio.run()` for simple agent usage. Document async API for advanced use cases.

- **Risk**: Subprocess spawning may fail in restricted environments
  - **Mitigation**: Implement comprehensive error handling with graceful degradation to lake build. Test in actual agent execution environment.

- **Risk**: lean-lsp-mcp may not be installed or configured
  - **Mitigation**: Check for .mcp.json configuration before attempting connection. Provide clear error messages guiding user to install lean-lsp-mcp.

## Implementation Phases

### Phase 1: Install MCP SDK and Create Client [NOT STARTED]

- **Goal**: Install official MCP SDK and create LeanMCPClient class
- **Tasks**:
  - [ ] Install MCP SDK: `uv add mcp` (or `pip install mcp`)
  - [ ] Create `.opencode/tool/mcp/lean_client.py` with `LeanMCPClient` class
  - [ ] Implement `__init__` with config auto-detection
  - [ ] Implement `connect()` method using `StdioServerParameters` and `stdio_client`
  - [ ] Implement `list_tools()` method using `session.list_tools()`
  - [ ] Implement `call_tool()` method using `session.call_tool()`
  - [ ] Implement `close()` method for cleanup
  - [ ] Add comprehensive docstrings and type hints
- **Timing**: 30 minutes
- **Acceptance Criteria**:
  - MCP SDK installed and importable
  - `LeanMCPClient` class created with all methods
  - Type hints and docstrings complete
  - No syntax errors, passes basic import test

### Phase 2: Add Synchronous Convenience Functions [NOT STARTED]

- **Goal**: Create synchronous wrapper functions for easy agent usage
- **Tasks**:
  - [ ] Implement `check_lean_diagnostics(file_path)` function
  - [ ] Implement `check_lean_goal(file_path, line, column)` function
  - [ ] Use `asyncio.run()` to wrap async client calls
  - [ ] Add comprehensive error handling (connection failures, timeouts, server errors)
  - [ ] Implement graceful degradation (return error dict on failure)
  - [ ] Add timeout parameter with default 30 seconds
  - [ ] Update `.opencode/tool/mcp/__init__.py` to export new functions
  - [ ] Add deprecation notice to old `client.py` functions
- **Timing**: 30 minutes
- **Acceptance Criteria**:
  - Synchronous functions work without async/await in caller
  - Error handling covers all failure modes
  - Timeout prevents hanging on unresponsive server
  - Functions return consistent dict format (success/error)

### Phase 3: Update Agent and Test Integration [NOT STARTED]

- **Goal**: Update lean-implementation-agent to use new client and verify end-to-end
- **Tasks**:
  - [ ] Update lean-implementation-agent.md import statements
  - [ ] Replace `check_mcp_server_configured` with config file check
  - [ ] Replace `invoke_mcp_tool` with `check_lean_diagnostics` / `check_lean_goal`
  - [ ] Add error handling and graceful degradation examples
  - [ ] Test with MCP Inspector: `npx @modelcontextprotocol/inspector uvx lean-lsp-mcp`
  - [ ] Test synchronous functions in Python REPL
  - [ ] Run /implement on simple Lean task to verify agent integration
  - [ ] Verify no import errors in agent output
  - [ ] Verify MCP client successfully connects and calls tools
  - [ ] Verify graceful degradation when lean-lsp-mcp unavailable
- **Timing**: 30 minutes
- **Acceptance Criteria**:
  - Agent successfully imports and uses new MCP client
  - MCP Inspector confirms protocol communication works
  - Real Lean task implementation uses MCP for diagnostics
  - Graceful degradation to lake build when MCP unavailable
  - No ModuleNotFoundError or import issues

## Testing & Validation

**Unit Tests**:
- [ ] Import test: `from opencode.tool.mcp.lean_client import LeanMCPClient`
- [ ] Import test: `from opencode.tool.mcp.lean_client import check_lean_diagnostics, check_lean_goal`
- [ ] Async test: `LeanMCPClient().connect("lean-lsp")` succeeds
- [ ] Async test: `client.list_tools()` returns expected tools
- [ ] Async test: `client.call_tool("lean_diagnostic_messages", {...})` returns result
- [ ] Sync test: `check_lean_diagnostics("test.lean")` returns dict
- [ ] Sync test: `check_lean_goal("test.lean", 42)` returns dict
- [ ] Error test: Connection failure returns error dict (not exception)
- [ ] Error test: Timeout after 30 seconds returns error dict

**Integration Tests**:
- [ ] MCP Inspector test: Connect to lean-lsp-mcp and list tools
- [ ] MCP Inspector test: Call `lean_diagnostic_messages` tool
- [ ] MCP Inspector test: Call `lean_goal` tool
- [ ] Agent test: Run /implement on Lean task, verify MCP usage
- [ ] Agent test: Disable lean-lsp-mcp, verify graceful degradation
- [ ] Agent test: Invalid .mcp.json, verify clear error message

**Regression Tests**:
- [ ] Existing Lean tasks still compile with lake build
- [ ] Non-Lean tasks unaffected by MCP client changes
- [ ] .mcp.json configuration still works for other tools

## Artifacts & Outputs

**Created Files**:
- `.opencode/tool/mcp/lean_client.py` - MCP client using official SDK with `LeanMCPClient` class and synchronous convenience functions

**Modified Files**:
- `.opencode/tool/mcp/__init__.py` - Export new functions, add deprecation notice to old API
- `.opencode/agent/subagents/lean-implementation-agent.md` - Update to use new MCP client API
- `.opencode/context/project/lean4/tools/mcp-tools-guide.md` - Document MCP SDK usage, remove PYTHONPATH instructions

**Deprecated Files** (not removed, but marked deprecated):
- `.opencode/tool/mcp/client.py` - Old custom wrapper (keep for backward compatibility, add deprecation warning)

**Documentation**:
- Updated mcp-tools-guide.md with MCP SDK installation and usage
- Updated lean-implementation-agent.md with new import patterns
- Added examples of error handling and graceful degradation
- Git commit message documenting migration to MCP SDK

**No Summary Artifact**: This is an implementation task, not a research task. Changes are well-documented in code and updated guides.

## Rollback/Contingency

**If MCP SDK installation fails**:
1. Check Python version (MCP SDK requires Python 3.10+)
2. Try alternative installation: `pip install mcp` instead of `uv add mcp`
3. Check for conflicting dependencies
4. Estimated additional effort: 15 minutes

**If stdio transport fails**:
1. Verify lean-lsp-mcp is installed: `uvx lean-lsp-mcp --version`
2. Test manually: `echo '{"jsonrpc":"2.0","method":"initialize","params":{},"id":1}' | uvx lean-lsp-mcp`
3. Check .mcp.json configuration format
4. Estimated additional effort: 30 minutes

**If async/await causes issues**:
1. Verify Python version supports asyncio (3.7+)
2. Check for event loop conflicts in agent execution
3. Consider using `asyncio.new_event_loop()` if needed
4. Estimated additional effort: 30 minutes

**Complete Rollback**:
- Uninstall MCP SDK: `uv remove mcp`
- Remove `lean_client.py`
- Revert agent and documentation changes
- Fall back to original plan (add `__init__.py` files)
- Estimated rollback time: 10 minutes

## Research Integration

**Key Research Findings Applied**:

1. **MCP Best Practices Identified** (research-002.md lines 24-43): MCP servers run as separate processes, communicate via stdio/SSE/HTTP, clients use MCP SDK, configuration via JSON files. This plan follows all best practices.

2. **Official MCP SDK Pattern** (research-002.md lines 46-93): Python clients use `ClientSession` with `StdioServerParameters` and `stdio_client` transport. This plan implements exact pattern from official documentation.

3. **lean-lsp-mcp Integration Pattern** (research-002.md lines 95-134): All MCP clients (VSCode, Cursor, Claude Desktop) spawn lean-lsp-mcp as subprocess via `uvx lean-lsp-mcp` command. This plan follows same pattern.

4. **Current Plan Limitations** (research-002.md lines 165-244): Original plan creates custom wrapper instead of using SDK, doesn't implement MCP protocol, requires PYTHONPATH configuration, and still needs 2-4 hours additional work to implement protocol. This plan eliminates all limitations.

5. **Effort Comparison** (research-002.md lines 496-533): Original plan: 3-4.5 hours total (45 min setup + 2-4 hours protocol implementation). MCP SDK approach: 1-2 hours total with full protocol working. This plan targets 1.5 hours (90 minutes).

6. **Comparison Table** (research-002.md lines 477-493): MCP SDK approach superior in every metric: uses official SDK, protocol fully implemented, stdio transport, separate process, no PYTHONPATH needed, no `__init__.py` needed, lower complexity, SDK maintained, MCP ecosystem compatible, built-in error handling, MCP Inspector testing, official docs.

**Research Artifacts Referenced**:
- Main Report: `.opencode/specs/218_fix_lean_lsp_mcp_integration/reports/research-002.md` (863 lines)
- Previous Report: `.opencode/specs/218_fix_lean_lsp_mcp_integration/reports/research-001.md` (897 lines)
- Summary: `.opencode/specs/218_fix_lean_lsp_mcp_integration/summaries/research-summary-002.md`

**Implementation Confidence**: Very High (95%+)
- Research confirms MCP SDK is standard approach used by all major MCP clients
- lean-lsp-mcp designed specifically for this integration pattern
- Official documentation provides complete implementation examples
- Approach eliminates all complexity from original plan (no PYTHONPATH, no `__init__.py`)
- Saves 1.5-2.5 hours compared to original plan
- Better architecture, maintainability, and future-proofing

## Benefits Over Original Plan

**Time Savings**: 1.5-2.5 hours
- Original plan: 45 min (setup) + 2-4 hours (protocol implementation) = 2.75-4.75 hours
- This plan: 1.5 hours (complete working integration)

**Architectural Improvements**:
- [PASS] No PYTHONPATH configuration needed
- [PASS] No `__init__.py` files needed
- [PASS] Process isolation (server crashes don't crash client)
- [PASS] Standard MCP protocol (works with MCP Inspector)
- [PASS] Official SDK maintenance (protocol updates automatic)

**Maintainability Improvements**:
- [PASS] Less custom code to maintain
- [PASS] Standard patterns from MCP ecosystem
- [PASS] Better error handling (SDK built-in)
- [PASS] Easier testing (MCP Inspector support)

**Standards Compliance**:
- [PASS] Follows MCP best practices
- [PASS] Compatible with MCP ecosystem tools
- [PASS] Same pattern as Claude Desktop, VSCode, Cursor
- [PASS] Future-proof (can add remote servers, multiple servers, etc.)
