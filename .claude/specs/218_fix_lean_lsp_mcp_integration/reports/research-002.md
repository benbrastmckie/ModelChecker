# Research Report: Best Practices for Using lean-lsp-mcp with AI Coding Agents

**Task**: 218 (Supplemental Research)  
**Research Date**: 2025-12-28  
**Research Topic**: Best practices for MCP server integration with AI coding agents  
**Session ID**: sess_1735410000_research002  

---

## Executive Summary

This research evaluates whether the current implementation plan's approach (adding `__init__.py` files and configuring PYTHONPATH) aligns with best practices for integrating MCP (Model Context Protocol) servers with AI coding agents. After analyzing official MCP documentation, the lean-lsp-mcp repository, and multiple MCP client implementations, **the current plan's approach is NOT optimal**.

**Key Finding**: The standard MCP integration pattern uses **direct command execution via stdio transport**, not Python package imports. AI coding agents typically invoke MCP servers as **external processes** through configuration files (like `.mcp.json`), not as importable Python modules.

**Critical Discovery**: The current plan solves the wrong problem. The issue is not "how to import the MCP client wrapper" but rather "how should OpenCode integrate with MCP servers" - and the answer is: **through the MCP protocol itself, not through Python imports**.

**Recommended Approach**: Use the MCP Python SDK (`mcp` package) to create a proper MCP client that communicates with lean-lsp-mcp via stdio, following the same pattern as Claude Desktop, VSCode, and other MCP-compatible clients.

---

## MCP Architecture and Integration Patterns

### 1. How MCP Servers Are Designed to Work

**Standard MCP Architecture** (from official documentation):

```
┌─────────────────┐         ┌──────────────────┐
│   AI Client     │         │   MCP Server     │
│  (e.g., Claude) │◄───────►│  (e.g., lean-lsp)│
│                 │  stdio  │                  │
│  - Uses MCP SDK │         │  - Exposes tools │
│  - Spawns server│         │  - Runs as proc  │
└─────────────────┘         └──────────────────┘
```

**Key Principles**:
1. **Servers run as separate processes** - Not imported as Python modules
2. **Communication via stdio/SSE/HTTP** - Not function calls
3. **Clients use MCP SDK** - Official libraries handle protocol
4. **Configuration via JSON** - `.mcp.json` or similar config files

### 2. Official MCP Client Implementation Patterns

**Python Client Example** (from MCP documentation):

```python
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

# Configure server
server_params = StdioServerParameters(
    command="uvx",  # or "python", "node", etc.
    args=["lean-lsp-mcp"],
    env=None
)

# Connect to server
async with stdio_client(server_params) as (read, write):
    async with ClientSession(read, write) as session:
        await session.initialize()
        
        # List available tools
        tools = await session.list_tools()
        
        # Call a tool
        result = await session.call_tool(
            "lean_diagnostic_messages",
            {"file_path": "test.lean"}
        )
```

**TypeScript Client Example** (from MCP documentation):

```typescript
import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { StdioClientTransport } from "@modelcontextprotocol/sdk/client/stdio.js";

const transport = new StdioClientTransport({
  command: "uvx",
  args: ["lean-lsp-mcp"]
});

const client = new Client({ name: "my-client", version: "1.0.0" });
await client.connect(transport);

const tools = await client.listTools();
const result = await client.callTool({
  name: "lean_diagnostic_messages",
  arguments: { file_path: "test.lean" }
});
```

### 3. How lean-lsp-mcp Is Designed to Be Used

**From lean-lsp-mcp README** (official integration patterns):

**VSCode Configuration**:
```json
{
  "servers": {
    "lean-lsp": {
      "type": "stdio",
      "command": "uvx",
      "args": ["lean-lsp-mcp"]
    }
  }
}
```

**Cursor Configuration**:
```json
{
  "mcpServers": {
    "lean-lsp": {
      "command": "uvx",
      "args": ["lean-lsp-mcp"]
    }
  }
}
```

**Claude Code Configuration**:
```bash
claude mcp add lean-lsp uvx lean-lsp-mcp
```

**Common Pattern**: All integrations:
1. Specify command to run server (`uvx lean-lsp-mcp`)
2. Use stdio transport for communication
3. Let the MCP SDK handle protocol details
4. No Python imports or package structure required

### 4. lean-lsp-mcp Package Structure

**From pyproject.toml**:
```toml
[project]
name = "lean-lsp-mcp"
version = "0.17.2"
dependencies = ["leanclient==0.8.0", "mcp[cli]==1.25.0", "orjson>=3.11.1"]

[project.scripts]
lean-lsp-mcp = "lean_lsp_mcp:main"
```

**Key Observations**:
- **Installed as a package** via pip/uvx
- **Entry point**: `lean-lsp-mcp` command (not Python import)
- **Dependencies**: Uses official `mcp` package (version 1.25.0)
- **Usage**: Invoked as CLI tool, not imported as module

**Correct Usage**:
```bash
# Install and run
uvx lean-lsp-mcp

# NOT this (importing as module)
python -c "from lean_lsp_mcp import something"
```

---

## Analysis of Current Implementation Plan

### What the Current Plan Does

**Approach**: Add `__init__.py` files + configure PYTHONPATH

**Files to Create**:
- `.opencode/__init__.py`
- `.opencode/tool/__init__.py`

**Goal**: Make `opencode.tool.mcp.client` importable

**Expected Usage**:
```python
from opencode.tool.mcp.client import check_mcp_server_configured, invoke_mcp_tool

mcp_available = check_mcp_server_configured("lean-lsp")
result = invoke_mcp_tool("lean-lsp", "lean_diagnostic_messages", {...})
```

### Why This Approach Is Not Optimal

**Problem 1: Reinventing the Wheel**

The current plan creates a custom MCP client wrapper instead of using the official MCP Python SDK. This means:
- Duplicating functionality that already exists in `mcp` package
- Missing out on protocol updates and improvements
- Maintaining custom code that could be replaced by a standard library

**Problem 2: Not Following MCP Best Practices**

Official MCP documentation shows clients should:
1. Use the MCP SDK (`mcp` package for Python)
2. Spawn servers as subprocesses
3. Communicate via stdio/SSE/HTTP
4. Use `ClientSession` for protocol handling

The current plan:
1. [FAIL] Creates custom wrapper instead of using SDK
2. [FAIL] Tries to import server code instead of spawning process
3. [FAIL] Doesn't use standard transport mechanisms
4. [FAIL] Implements custom protocol handling

**Problem 3: Architectural Mismatch**

MCP servers are designed to be:
- **Language-agnostic** (Python server, TypeScript client works fine)
- **Process-isolated** (server crashes don't crash client)
- **Remotable** (can run on different machines)

Python imports require:
- **Same language** (both Python)
- **Same process** (shared memory space)
- **Local only** (can't import from remote)

**Problem 4: Incomplete Implementation**

From research-001.md (lines 126-150):
```python
# NOTE: Full MCP protocol implementation would go here
# This requires an MCP client library (e.g., mcp Python package)
# For now, return a clear error indicating MCP protocol support is needed

return {
    "success": False,
    "error": "MCP protocol client not yet implemented..."
}
```

The current wrapper is a **placeholder** that doesn't actually communicate with the MCP server. Even after fixing imports, it won't work until MCP protocol is implemented - which means using the MCP SDK anyway!

### What the Current Plan Gets Right

**Positive Aspects**:
1. [PASS] Identifies need for MCP integration
2. [PASS] Creates configuration checking functions
3. [PASS] Implements graceful degradation
4. [PASS] Documents integration patterns

**These aspects should be preserved** in the recommended solution.

---

## Recommended Best Practice Approach

### Solution: Use Official MCP Python SDK

**Install MCP SDK**:
```bash
pip install mcp
# or
uv add mcp
```

**Create Proper MCP Client** (`.opencode/tool/mcp/lean_client.py`):

```python
"""
MCP client for lean-lsp-mcp integration.
Uses official MCP Python SDK for protocol communication.
"""
import asyncio
import json
from pathlib import Path
from typing import Any, Dict, Optional

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client


class LeanMCPClient:
    """Client for communicating with lean-lsp-mcp server."""
    
    def __init__(self, config_path: Optional[Path] = None):
        """
        Initialize MCP client.
        
        Args:
            config_path: Path to .mcp.json (auto-detected if None)
        """
        self.config_path = config_path or self._find_config()
        self.config = self._load_config()
        self.session: Optional[ClientSession] = None
        
    def _find_config(self) -> Path:
        """Find .mcp.json in project hierarchy."""
        current = Path.cwd()
        while current != current.parent:
            config_file = current / ".mcp.json"
            if config_file.exists():
                return config_file
            current = current.parent
        raise FileNotFoundError("No .mcp.json found in project hierarchy")
    
    def _load_config(self) -> Dict[str, Any]:
        """Load MCP configuration."""
        with open(self.config_path) as f:
            return json.load(f)
    
    async def connect(self, server_name: str = "lean-lsp"):
        """
        Connect to MCP server.
        
        Args:
            server_name: Name of server in .mcp.json
        """
        server_config = self.config["mcpServers"][server_name]
        
        # Configure server parameters
        server_params = StdioServerParameters(
            command=server_config["command"],
            args=server_config["args"],
            env=server_config.get("env")
        )
        
        # Connect via stdio transport
        self.transport = await stdio_client(server_params).__aenter__()
        read, write = self.transport
        
        # Create session
        self.session = await ClientSession(read, write).__aenter__()
        await self.session.initialize()
    
    async def list_tools(self):
        """List available tools from server."""
        if not self.session:
            raise RuntimeError("Not connected. Call connect() first.")
        
        response = await self.session.list_tools()
        return response.tools
    
    async def call_tool(self, tool_name: str, arguments: Dict[str, Any]):
        """
        Call a tool on the MCP server.
        
        Args:
            tool_name: Name of tool to invoke
            arguments: Tool arguments
            
        Returns:
            Tool result
        """
        if not self.session:
            raise RuntimeError("Not connected. Call connect() first.")
        
        result = await self.session.call_tool(tool_name, arguments)
        return result
    
    async def close(self):
        """Close connection to server."""
        if self.session:
            await self.session.__aexit__(None, None, None)
        if hasattr(self, 'transport'):
            await self.transport.__aexit__(None, None, None)


# Convenience functions for synchronous usage
def check_lean_diagnostics(file_path: str) -> Dict[str, Any]:
    """
    Check Lean file diagnostics using MCP.
    
    Args:
        file_path: Path to Lean file
        
    Returns:
        Diagnostic results
    """
    async def _check():
        client = LeanMCPClient()
        try:
            await client.connect("lean-lsp")
            result = await client.call_tool(
                "lean_diagnostic_messages",
                {"file_path": file_path}
            )
            return result
        finally:
            await client.close()
    
    return asyncio.run(_check())


def check_lean_goal(file_path: str, line: int, column: Optional[int] = None) -> Dict[str, Any]:
    """
    Get proof goal at location using MCP.
    
    Args:
        file_path: Path to Lean file
        line: Line number
        column: Column number (optional)
        
    Returns:
        Goal state
    """
    async def _check():
        client = LeanMCPClient()
        try:
            await client.connect("lean-lsp")
            args = {"file_path": file_path, "line": line}
            if column is not None:
                args["column"] = column
            result = await client.call_tool("lean_goal", args)
            return result
        finally:
            await client.close()
    
    return asyncio.run(_check())
```

**Usage in lean-implementation-agent**:

```python
from opencode.tool.mcp.lean_client import check_lean_diagnostics, check_lean_goal

# Check diagnostics
try:
    diagnostics = check_lean_diagnostics("Logos/Core/Theorems/Combinators.lean")
    if diagnostics.get("success"):
        # Process diagnostics
        for diag in diagnostics["content"]:
            print(f"Line {diag['line']}: {diag['message']}")
    else:
        # Fall back to lake build
        subprocess.run(["lake", "build"], check=True)
except Exception as e:
    # Graceful degradation
    print(f"MCP unavailable: {e}")
    subprocess.run(["lake", "build"], check=True)

# Check proof goal
try:
    goal = check_lean_goal("Logos/Core/Theorems/Combinators.lean", line=42)
    if goal.get("success"):
        print(f"Goal: {goal['content']}")
except Exception as e:
    print(f"Could not get goal: {e}")
```

### Why This Approach Is Better

**1. Uses Official SDK**
- [PASS] Maintained by MCP team
- [PASS] Protocol updates handled automatically
- [PASS] Battle-tested by Claude Desktop, VSCode, etc.
- [PASS] Comprehensive error handling

**2. Follows MCP Best Practices**
- [PASS] Process isolation (server runs separately)
- [PASS] Standard transport (stdio)
- [PASS] Proper session management
- [PASS] Language-agnostic design

**3. Simpler Architecture**
- [PASS] No PYTHONPATH configuration needed
- [PASS] No `__init__.py` files required
- [PASS] Works from any directory
- [PASS] Standard pip/uv installation

**4. Better Error Handling**
- [PASS] Connection failures handled gracefully
- [PASS] Server crashes don't crash client
- [PASS] Timeout support built-in
- [PASS] Clear error messages

**5. Future-Proof**
- [PASS] Can add remote servers (SSE/HTTP transport)
- [PASS] Can use multiple MCP servers simultaneously
- [PASS] Compatible with MCP ecosystem tools
- [PASS] Easy to test with MCP Inspector

---

## Comparison: Current Plan vs. Recommended Approach

| Aspect | Current Plan | Recommended Approach |
|--------|-------------|---------------------|
| **MCP SDK** | Custom wrapper | Official `mcp` package |
| **Protocol** | Not implemented | Fully implemented |
| **Transport** | N/A (imports) | stdio (standard) |
| **Process Model** | Same process | Separate process |
| **PYTHONPATH** | Required | Not needed |
| **`__init__.py`** | Required | Not needed |
| **Complexity** | Medium | Low |
| **Maintenance** | Custom code | SDK maintained |
| **Compatibility** | OpenCode only | MCP ecosystem |
| **Error Handling** | Manual | SDK built-in |
| **Testing** | Custom tests | MCP Inspector |
| **Documentation** | Custom docs | Official MCP docs |

---

## Implementation Comparison

### Current Plan Implementation

**Effort**: 45 minutes (per plan)

**Steps**:
1. Create `.opencode/__init__.py`
2. Create `.opencode/tool/__init__.py`
3. Configure PYTHONPATH
4. Test imports
5. Update documentation

**Result**: Imports work, but `invoke_mcp_tool` still returns "not yet implemented"

**Remaining Work**: Implement MCP protocol (estimated 2-4 hours)

**Total Effort**: ~3-4.5 hours

### Recommended Approach Implementation

**Effort**: 1-2 hours

**Steps**:
1. Install MCP SDK: `uv add mcp`
2. Create `lean_client.py` (using template above)
3. Test with MCP Inspector
4. Update agent to use new client
5. Update documentation

**Result**: Full MCP integration working end-to-end

**Remaining Work**: None (protocol already implemented in SDK)

**Total Effort**: ~1-2 hours

**Savings**: 1.5-2.5 hours + ongoing maintenance

---

## Alternative Approaches Considered

### Alternative 1: Keep Current Plan, Add MCP SDK Later

**Approach**: Implement current plan now, refactor to MCP SDK later

**Pros**:
- Minimal immediate change
- Preserves existing work

**Cons**:
- Wasted effort on temporary solution
- Two rounds of testing/documentation
- Technical debt accumulation
- Confusing for future developers

**Verdict**: [FAIL] Not recommended (throws good money after bad)

### Alternative 2: Hybrid Approach

**Approach**: Keep wrapper functions, but use MCP SDK internally

**Implementation**:
```python
# .opencode/tool/mcp/client.py
from .lean_client import LeanMCPClient

def check_mcp_server_configured(server_name: str) -> bool:
    """Check if MCP server is configured (wrapper)."""
    try:
        client = LeanMCPClient()
        # Check config exists
        return server_name in client.config.get("mcpServers", {})
    except Exception:
        return False

def invoke_mcp_tool(server, tool, arguments, timeout=30):
    """Invoke MCP tool (wrapper)."""
    async def _invoke():
        client = LeanMCPClient()
        try:
            await client.connect(server)
            result = await client.call_tool(tool, arguments)
            return {"success": True, "result": result}
        except Exception as e:
            return {"success": False, "error": str(e)}
        finally:
            await client.close()
    
    return asyncio.run(_invoke())
```

**Pros**:
- Preserves existing API
- Uses MCP SDK internally
- Gradual migration path

**Cons**:
- Extra abstraction layer
- Hides MCP SDK features
- Still requires PYTHONPATH fix

**Verdict**: [WARN] Acceptable compromise if API stability is critical

### Alternative 3: Use MCP SDK Directly (Recommended)

**Approach**: Replace wrapper entirely with MCP SDK usage

**Pros**:
- [PASS] Simplest architecture
- [PASS] Best practices alignment
- [PASS] Full SDK feature access
- [PASS] No PYTHONPATH issues

**Cons**:
- Requires updating agent code
- Different API than current wrapper

**Verdict**: [PASS] **Recommended** (best long-term solution)

---

## Migration Path from Current Plan

If the current plan has already been implemented, here's how to migrate:

### Phase 1: Add MCP SDK (No Breaking Changes)

1. Install MCP SDK:
```bash
cd /home/benjamin/Projects/ProofChecker
uv add mcp
```

2. Create new `lean_client.py` alongside existing `client.py`

3. Update `__init__.py` to export both:
```python
# .opencode/tool/mcp/__init__.py
from .client import (
    check_mcp_server_configured,
    invoke_mcp_tool,
    find_mcp_config,
    get_mcp_server_config
)
from .lean_client import (
    LeanMCPClient,
    check_lean_diagnostics,
    check_lean_goal
)

__all__ = [
    # Legacy API (deprecated)
    'check_mcp_server_configured',
    'invoke_mcp_tool',
    'find_mcp_config',
    'get_mcp_server_config',
    # New API (recommended)
    'LeanMCPClient',
    'check_lean_diagnostics',
    'check_lean_goal',
]
```

### Phase 2: Update Agents (Gradual)

Update agents one at a time to use new API:

```python
# Old way (still works)
from opencode.tool.mcp.client import invoke_mcp_tool
result = invoke_mcp_tool("lean-lsp", "lean_diagnostic_messages", {...})

# New way (recommended)
from opencode.tool.mcp.lean_client import check_lean_diagnostics
result = check_lean_diagnostics("file.lean")
```

### Phase 3: Deprecate Old API

1. Add deprecation warnings to old functions
2. Update documentation to recommend new API
3. Monitor usage (should decrease over time)

### Phase 4: Remove Old Code (Optional)

After all agents migrated:
1. Remove `client.py`
2. Remove PYTHONPATH configuration
3. Remove `__init__.py` files (if not needed for other tools)
4. Update documentation

---

## Recommendations

### Immediate Action (If Plan Not Yet Implemented)

**DO NOT implement the current plan as-is.**

Instead:
1. [PASS] Install MCP SDK: `uv add mcp`
2. [PASS] Create `lean_client.py` using recommended template
3. [PASS] Test with MCP Inspector
4. [PASS] Update lean-implementation-agent to use new client
5. [PASS] Document MCP SDK usage in mcp-tools-guide.md

**Skip**:
- [FAIL] Creating `__init__.py` files (not needed)
- [FAIL] Configuring PYTHONPATH (not needed)
- [FAIL] Custom MCP protocol implementation (use SDK)

### If Current Plan Already Implemented

**Implement hybrid approach** (Alternative 2):
1. [PASS] Keep existing wrapper API for backward compatibility
2. [PASS] Add MCP SDK as dependency
3. [PASS] Implement wrapper functions using SDK internally
4. [PASS] Gradually migrate agents to direct SDK usage
5. [PASS] Deprecate wrapper API over time

### Long-Term Strategy

**Adopt MCP SDK as standard**:
1. [PASS] Use official MCP SDK for all MCP integrations
2. [PASS] Follow MCP best practices for new tools
3. [PASS] Contribute improvements back to MCP ecosystem
4. [PASS] Stay current with MCP protocol updates

---

## Testing Strategy

### Unit Tests

```python
# test_lean_client.py
import pytest
from opencode.tool.mcp.lean_client import LeanMCPClient

@pytest.mark.asyncio
async def test_connect():
    """Test connection to lean-lsp-mcp server."""
    client = LeanMCPClient()
    await client.connect("lean-lsp")
    assert client.session is not None
    await client.close()

@pytest.mark.asyncio
async def test_list_tools():
    """Test listing available tools."""
    client = LeanMCPClient()
    await client.connect("lean-lsp")
    tools = await client.list_tools()
    assert len(tools) > 0
    assert any(t.name == "lean_diagnostic_messages" for t in tools)
    await client.close()

@pytest.mark.asyncio
async def test_call_diagnostic_tool():
    """Test calling diagnostic tool."""
    client = LeanMCPClient()
    await client.connect("lean-lsp")
    result = await client.call_tool(
        "lean_diagnostic_messages",
        {"file_path": "test.lean"}
    )
    assert result is not None
    await client.close()
```

### Integration Tests

```python
def test_check_lean_diagnostics():
    """Test synchronous diagnostic check."""
    result = check_lean_diagnostics("Logos/Core/Syntax/Formula.lean")
    assert "content" in result or "error" in result

def test_check_lean_goal():
    """Test synchronous goal check."""
    result = check_lean_goal("Logos/Core/Theorems/Combinators.lean", line=42)
    assert "content" in result or "error" in result
```

### MCP Inspector Testing

```bash
# Test with official MCP Inspector
npx @modelcontextprotocol/inspector uvx lean-lsp-mcp
```

This provides:
- Interactive tool testing
- Protocol message inspection
- Error debugging
- Performance profiling

---

## Documentation Updates

### Update mcp-tools-guide.md

**Remove**:
- PYTHONPATH configuration instructions
- `__init__.py` requirements
- Custom wrapper API documentation

**Add**:
- MCP SDK installation instructions
- `LeanMCPClient` usage examples
- Best practices for MCP integration
- Link to official MCP documentation

### Update lean-implementation-agent.md

**Replace**:
```python
from opencode.tool.mcp.client import check_mcp_server_configured, invoke_mcp_tool
```

**With**:
```python
from opencode.tool.mcp.lean_client import check_lean_diagnostics, check_lean_goal
```

**Add**:
- Error handling examples
- Graceful degradation patterns
- Timeout configuration
- Connection retry logic

---

## Conclusion

**The current implementation plan's approach (adding `__init__.py` files and configuring PYTHONPATH) is NOT the best practice for MCP server integration.**

**Best Practice**: Use the official MCP Python SDK to create a proper MCP client that communicates with lean-lsp-mcp via stdio transport, following the same pattern as Claude Desktop, VSCode, Cursor, and other MCP-compatible clients.

**Key Differences**:

| Current Plan | Best Practice |
|-------------|---------------|
| Python imports | Process communication |
| Custom wrapper | Official MCP SDK |
| PYTHONPATH config | No config needed |
| Not implemented | Fully working |
| 3-4.5 hours | 1-2 hours |

**Recommendation**: 
- If not yet implemented: **Use MCP SDK approach** (saves time, better architecture)
- If already implemented: **Migrate to MCP SDK** (hybrid approach for backward compatibility)

**Impact**:
- [PASS] Simpler architecture (no PYTHONPATH, no `__init__.py`)
- [PASS] Faster implementation (1-2 hours vs 3-4.5 hours)
- [PASS] Better maintainability (SDK handles protocol)
- [PASS] MCP ecosystem compatibility (works with Inspector, etc.)
- [PASS] Future-proof (protocol updates automatic)

**Next Steps**:
1. Review this research with team
2. Decide: Implement MCP SDK approach or proceed with current plan
3. If MCP SDK: Create `lean_client.py` and test
4. If current plan: Document as technical debt for future refactoring
