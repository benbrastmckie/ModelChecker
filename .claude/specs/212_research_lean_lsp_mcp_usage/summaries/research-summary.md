# Research Summary: lean-lsp-mcp Usage

**Task**: 212  
**Date**: 2025-12-28  
**Status**: Completed  

---

## Key Findings

1. **lean-lsp-mcp is configured but not being used**
   - Properly configured in `.mcp.json` with stdio transport
   - Tool is installed and accessible via `uvx lean-lsp-mcp`
   - Provides 15+ MCP tools for Lean interaction (diagnostics, goals, search, etc.)
   - **Zero actual usage** in current agent workflows

2. **Critical infrastructure gap identified**
   - No MCP client wrapper exists for agents to invoke tools
   - Agents have no mechanism to call MCP protocol tools
   - lean-implementation-agent.md has placeholder logic only
   - No concrete tool invocation patterns documented

3. **Agent workflow gaps**
   - lean-implementation-agent step_4 says "Send Lean files for compilation" but doesn't specify HOW
   - No iteration loop implementation for error fixing
   - No tool availability check logic
   - No graceful degradation specifics

4. **Documentation inadequacy**
   - mcp-tools-guide.md describes WHAT tools do, not HOW to invoke them
   - Shows TypeScript examples, not agent integration patterns
   - No agent-specific usage examples
   - Missing troubleshooting guide

5. **Similar issues in lean-research-agent**
   - Better documentation for Loogle CLI (subprocess approach)
   - But LeanSearch/LeanExplore marked "NOT YET INTEGRATED"
   - Mixing CLI tools with MCP tools creates confusion

---

## Root Causes

### Primary Blocker
**No MCP client infrastructure** - Agents cannot invoke MCP tools because no client wrapper exists.

### Secondary Issues
1. Incomplete agent workflow definitions (placeholder logic)
2. Inadequate context documentation (describes capabilities, not integration)
3. Missing test infrastructure for MCP tool invocation
4. Confusion between CLI tools (Loogle) and MCP tools (lean-lsp-mcp)

---

## Recommended Solutions

### Phase 1: Foundation (High Priority)
**Implement MCP Client Wrapper**
- Create `.opencode/tool/mcp/client.py`
- Functions: `check_mcp_server_configured()`, `invoke_mcp_tool()`
- Handle .mcp.json loading, server connection, tool invocation
- **Estimated Effort**: 8-10 hours

### Phase 2: Agent Integration (High Priority)
**Update lean-implementation-agent.md**
- Add concrete MCP tool invocation in step_4
- Add iteration loop with error handling
- Add tool availability check logic
- Add example tool calls
- **Estimated Effort**: 6-8 hours

### Phase 3: Documentation (Medium Priority)
**Update mcp-tools-guide.md**
- Add "Agent Integration" section
- Add tool invocation examples
- Add error handling patterns
- Add troubleshooting guide
- **Estimated Effort**: 4-6 hours

### Phase 4: Testing (Medium Priority)
**Create Integration Tests**
- Test MCP client initialization
- Test tool invocation (mocked and real)
- Test error handling and timeouts
- **Estimated Effort**: 6-8 hours

**Total Estimated Effort**: 24-32 hours (3-4 days)

---

## lean-lsp-mcp Capabilities

### File Interaction Tools (LSP)
- `lean_diagnostic_messages` - Get compilation errors/warnings
- `lean_goal` - Get proof goal at position
- `lean_run_code` - Run/compile code snippet
- `lean_multi_attempt` - Try multiple proof attempts
- `lean_hover_info` - Get documentation
- `lean_completions` - Code auto-completion

### Search Tools
- `lean_local_search` - Search local project (requires ripgrep)
- `lean_leansearch` - Natural language search (leansearch.net)
- `lean_loogle` - Type-based search (loogle.lean-lang.org)
- `lean_leanfinder` - Semantic search
- `lean_state_search` - Premise search
- `lean_hammer_premise` - Hammer premise search

### Project Tools
- `lean_build` - Rebuild project and restart LSP

---

## Recommended Usage Workflow

**For Lean Implementation**:
1. Write proof tactic line
2. Call `lean_goal` to get current proof state
3. Check goals and hypotheses
4. Call `lean_diagnostic_messages` to check for errors
5. If no errors, proceed to next tactic
6. Iterate until proof complete
7. Call `lean_build` to verify full project compilation

**Benefits**:
- Real-time error detection
- Proof state inspection
- Faster iteration cycles
- Reduced compilation failures

---

## Success Criteria

1. **Tool Invocation Works**: Agent successfully calls `lean_diagnostic_messages`
2. **Compilation Checking Functional**: Agent detects and reports Lean errors
3. **Graceful Degradation**: Agent handles MCP unavailability without crashing
4. **Performance Acceptable**: MCP tool invocation adds < 5s per iteration
5. **Documentation Complete**: Developers can integrate MCP tools using docs

---

## Next Steps

1. **Immediate**: Implement MCP client wrapper (`.opencode/tool/mcp/client.py`)
2. **Week 1**: Update lean-implementation-agent.md with concrete patterns
3. **Week 2**: Update documentation and create test suite
4. **Week 3**: Validate with real Lean implementation tasks

---

## References

- [lean-lsp-mcp PyPI](https://pypi.org/project/lean-lsp-mcp/) - v0.17.2
- [lean-lsp-mcp GitHub](https://github.com/oOo0oOo/lean-lsp-mcp)
- `.mcp.json` - Current configuration (working)
- `.opencode/context/project/lean4/tools/mcp-tools-guide.md` - Tool capabilities
- `.opencode/agent/subagents/lean-implementation-agent.md` - Needs updates

---

## Impact

**Current State**: lean-lsp-mcp configured but completely unused (0% utilization)

**After Implementation**: 
- Real-time Lean compilation checking
- Proof state inspection during development
- Error detection before committing
- Faster Lean development cycles
- Reduced build failures

**Estimated Improvement**: 30-50% reduction in Lean implementation iteration time
