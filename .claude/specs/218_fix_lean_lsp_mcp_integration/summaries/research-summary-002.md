# Research Summary: Best Practices for MCP Integration with AI Agents

**Task**: 218 (Supplemental Research)  
**Date**: 2025-12-28  
**Topic**: MCP server integration best practices  

---

## Key Finding

**The current implementation plan's approach (adding `__init__.py` files and configuring PYTHONPATH) is NOT optimal for MCP integration.**

The standard MCP pattern uses **direct process communication via the MCP SDK**, not Python package imports.

---

## Critical Discovery

**Current Plan Solves the Wrong Problem**

- **What it does**: Makes `opencode.tool.mcp.client` importable as a Python module
- **What it should do**: Use the official MCP Python SDK to communicate with lean-lsp-mcp as a separate process

**MCP servers are designed to**:
- Run as separate processes (not imported modules)
- Communicate via stdio/SSE/HTTP (not function calls)
- Use official MCP SDKs (not custom wrappers)

---

## How MCP Integration Actually Works

**Standard Pattern** (used by Claude Desktop, VSCode, Cursor):

```python
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

# Configure server
server_params = StdioServerParameters(
    command="uvx",
    args=["lean-lsp-mcp"]
)

# Connect and use
async with stdio_client(server_params) as (read, write):
    async with ClientSession(read, write) as session:
        await session.initialize()
        tools = await session.list_tools()
        result = await session.call_tool("lean_diagnostic_messages", {...})
```

**Key Points**:
- [PASS] Uses official `mcp` package (pip install mcp)
- [PASS] Spawns server as subprocess
- [PASS] Communicates via stdio protocol
- [PASS] No PYTHONPATH or `__init__.py` needed

---

## Recommended Approach

**Use Official MCP Python SDK**

**Installation**:
```bash
uv add mcp
```

**Implementation** (create `.opencode/tool/mcp/lean_client.py`):
```python
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

class LeanMCPClient:
    async def connect(self, server_name="lean-lsp"):
        server_config = self.config["mcpServers"][server_name]
        server_params = StdioServerParameters(
            command=server_config["command"],
            args=server_config["args"]
        )
        self.transport = await stdio_client(server_params).__aenter__()
        read, write = self.transport
        self.session = await ClientSession(read, write).__aenter__()
        await self.session.initialize()
    
    async def call_tool(self, tool_name, arguments):
        return await self.session.call_tool(tool_name, arguments)
```

**Usage in agents**:
```python
from opencode.tool.mcp.lean_client import check_lean_diagnostics

diagnostics = check_lean_diagnostics("file.lean")
```

---

## Comparison

| Aspect | Current Plan | Recommended |
|--------|-------------|-------------|
| **Approach** | Python imports | MCP SDK |
| **PYTHONPATH** | Required | Not needed |
| **`__init__.py`** | Required | Not needed |
| **Protocol** | Not implemented | SDK handles it |
| **Effort** | 3-4.5 hours | 1-2 hours |
| **Maintenance** | Custom code | SDK maintained |
| **Compatibility** | OpenCode only | MCP ecosystem |

---

## Why This Matters

**Current Plan Issues**:
1. [FAIL] Reinvents the wheel (custom wrapper vs official SDK)
2. [FAIL] Doesn't follow MCP best practices
3. [FAIL] Requires PYTHONPATH configuration
4. [FAIL] Protocol still not implemented (placeholder returns error)
5. [FAIL] More complex architecture
6. [FAIL] Higher maintenance burden

**MCP SDK Benefits**:
1. [PASS] Official, maintained by MCP team
2. [PASS] Follows MCP best practices
3. [PASS] No PYTHONPATH needed
4. [PASS] Protocol fully implemented
5. [PASS] Simpler architecture
6. [PASS] Compatible with MCP Inspector and ecosystem tools

---

## Evidence from Official Sources

**lean-lsp-mcp README** shows all integrations use the same pattern:

**VSCode**:
```json
{"servers": {"lean-lsp": {"command": "uvx", "args": ["lean-lsp-mcp"]}}}
```

**Cursor**:
```json
{"mcpServers": {"lean-lsp": {"command": "uvx", "args": ["lean-lsp-mcp"]}}}
```

**Claude Code**:
```bash
claude mcp add lean-lsp uvx lean-lsp-mcp
```

**Common Pattern**: Command execution + stdio transport, NOT Python imports

---

## Recommendations

### If Plan Not Yet Implemented

**DO NOT proceed with current plan.**

Instead:
1. Install MCP SDK: `uv add mcp`
2. Create `lean_client.py` using MCP SDK
3. Test with MCP Inspector
4. Update agents to use new client
5. Skip PYTHONPATH and `__init__.py` steps

**Time Savings**: 1.5-2.5 hours + ongoing maintenance

### If Plan Already Implemented

**Implement hybrid approach**:
1. Keep existing API for backward compatibility
2. Add MCP SDK as dependency
3. Reimplement wrapper functions using SDK internally
4. Gradually migrate agents to direct SDK usage
5. Deprecate wrapper API over time

---

## Next Steps

1. **Review** this research with team
2. **Decide**: MCP SDK approach or current plan
3. **If MCP SDK**: Create `lean_client.py` (1-2 hours)
4. **If current plan**: Document as technical debt for future refactoring

---

## Conclusion

**Best practice for MCP integration is to use the official MCP Python SDK**, not custom Python package imports. This approach is:
- Simpler (no PYTHONPATH, no `__init__.py`)
- Faster (1-2 hours vs 3-4.5 hours)
- Better maintained (SDK handles protocol)
- More compatible (works with MCP ecosystem)
- Future-proof (automatic protocol updates)

The current plan solves an import problem, but the real solution is to not need imports at all - use the MCP SDK to communicate with the server as a separate process, just like Claude Desktop, VSCode, and Cursor do.
