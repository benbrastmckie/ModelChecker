# Research Summary: Fix lean-lsp-mcp Integration and opencode Module Import Errors

**Task**: 218  
**Date**: 2025-12-28  
**Status**: Research Complete  

---

## Key Findings

**Root Cause**: The `.opencode` directory lacks `__init__.py` files in parent directories, preventing Python from recognizing it as a package. This causes `ModuleNotFoundError: No module named 'opencode'` when lean-implementation-agent attempts to import the MCP client wrapper.

**Missing Files**:
- `.opencode/__init__.py` (missing)
- `.opencode/tool/__init__.py` (missing)
- `.opencode/tool/mcp/__init__.py` (exists)

**Impact**: lean-implementation-agent cannot use lean-lsp-mcp for compilation verification, forcing degraded mode operation without type checking.

---

## MCP Client Infrastructure Status

**Task 212 Implementation**: [PASS] Correctly implemented and tested

**Available Functions**:
- `check_mcp_server_configured()` - [PASS] Working
- `find_mcp_config()` - [PASS] Working
- `get_mcp_server_config()` - [PASS] Working
- `invoke_mcp_tool()` - [WARN] Placeholder (returns "not yet implemented")

**Configuration**: [PASS] .mcp.json correctly configured for lean-lsp server via uvx

**Test Results**: [PASS] All 6 tests passing (using sys.path workaround)

---

## Recommended Solution

**Approach**: Create missing `__init__.py` files + configure PYTHONPATH

**Implementation**:
1. Create empty `.opencode/__init__.py`
2. Create empty `.opencode/tool/__init__.py`
3. Configure PYTHONPATH in agent execution environment to include project root

**Effort**: 15-30 minutes  
**Risk**: Low  
**Complexity**: Minimal (2 empty files + environment configuration)

---

## Alternative Solutions Considered

1. **Agent Execution Wrapper** (2-3 hours, medium risk)
   - Create Python wrapper that sets sys.path before executing agent code
   - Requires orchestrator modification

2. **Relative Imports** (1 hour, low risk but creates technical debt)
   - Modify agent specs to use sys.path.insert() before imports
   - Less clean than proper package structure

3. **Editable Package Install** (1 hour, medium risk)
   - Create setup.py and install with pip
   - May conflict with Nix environment

---

## Verification Plan

**Phase 1**: Package Structure
- Test import with PYTHONPATH set
- Verify all functions importable

**Phase 2**: MCP Client Functions
- Test server configuration check
- Test config retrieval

**Phase 3**: Agent Integration
- Simulate agent execution
- Verify graceful degradation

**Phase 4**: End-to-End
- Run /implement on Lean task
- Confirm no ModuleNotFoundError
- Verify degraded mode works

---

## Next Steps

**Immediate**:
1. Implement recommended solution (create __init__.py files)
2. Configure PYTHONPATH in agent execution environment
3. Run verification tests
4. Update documentation

**Short-Term**:
1. Complete MCP protocol integration in invoke_mcp_tool
2. Test with actual lean-lsp-mcp server
3. Verify diagnostic messages work end-to-end

**Medium-Term**:
1. Integrate additional tools (Loogle, LeanExplore, LeanSearch)
2. Add monitoring and metrics
3. Optimize performance

---

## Tool Availability

**Python Environment**: [PASS] Python 3.12.12 (Nix)  
**uvx**: [PASS] Available at /run/current-system/sw/bin/uvx  
**lean-lsp-mcp**: [PASS] Configured in .mcp.json  
**MCP Client Wrapper**: [PASS] Implemented (import blocked)  
**MCP Protocol Integration**: [WARN] Pending (placeholder implementation)

---

## References

- **Research Report**: `.opencode/specs/218_fix_lean_lsp_mcp_integration/reports/research-001.md`
- **MCP Client**: `.opencode/tool/mcp/client.py`
- **Agent Spec**: `.opencode/agent/subagents/lean-implementation-agent.md`
- **MCP Config**: `.mcp.json`
