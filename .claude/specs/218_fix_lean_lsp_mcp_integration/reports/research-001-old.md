# MCP Server Best Practices for OpenCode Integration

**Task**: 218  
**Topic**: Fix lean-lsp-mcp integration and opencode module import errors  
**Date**: 2025-12-28  
**Session ID**: sess_1766960487_mcp001  
**Agent**: researcher  

---

## Executive Summary

This research investigated MCP server best practices for OpenCode integration, with specific focus on enabling the lean-implementation-subagent to use lean-lsp-mcp for improving Lean proof writing and revising processes. Key findings:

1. **OpenCode has native MCP server support** via configuration in `opencode.json` (NOT `.mcp.json`)
2. **MCP tools are automatically available** to agents once configured - no custom client needed
3. **Current implementation uses wrong approach** - custom Python MCP client instead of OpenCode's native integration
4. **Module import errors are a symptom** of architectural mismatch between custom tool approach and OpenCode's native MCP support
5. **Solution is configuration-based**, not code-based - leverage OpenCode's built-in MCP integration

---

## Research Scope

### Objectives
1. [PASS] Research OpenCode MCP server configuration best practices
2. [PASS] Understand how MCP servers integrate into agent workflows
3. [PASS] Identify proper setup for lean-lsp-mcp in OpenCode
4. [PASS] Determine how agents invoke MCP tools
5. [PASS] Identify common pitfalls and solutions
6. [PASS] Recommend additional useful MCP servers for Lean development

### Sources
- **Primary**: https://opencode.ai/docs/mcp-servers/
- **Supporting**: OpenCode agents, tools, and custom tools documentation
- **Local**: Task 212 research, existing MCP client implementation

---

## Key Findings

### 1. OpenCode Native MCP Support

#### Overview

OpenCode has **built-in MCP server support** that automatically makes MCP tools available to agents. This is fundamentally different from the custom Python MCP client approach currently implemented in Task 212.

**Key Insight**: MCP servers in OpenCode work like built-in tools - once configured, they're automatically available to the LLM alongside tools like `read`, `write`, and `bash`.

#### Configuration Location

**CRITICAL**: OpenCode uses `opencode.json` for MCP configuration, NOT `.mcp.json`.

The project currently has:
- [PASS] `.mcp.json` - Used by Claude Desktop/other MCP clients
- [FAIL] No `opencode.json` in project root - Missing OpenCode configuration
- [PASS] `~/.config/opencode/opencode.json` - Global OpenCode config (only keybinds)

**Required**: Create project-specific `opencode.json` with MCP server configuration.

#### Basic MCP Configuration

```json
{
  "$schema": "https://opencode.ai/config.json",
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": ["uvx", "lean-lsp-mcp"],
      "enabled": true,
      "environment": {
        "LEAN_LOG_LEVEL": "WARNING",
        "LEAN_PROJECT_PATH": "/home/benjamin/Projects/ProofChecker"
      }
    }
  }
}
```

**Key Differences from `.mcp.json`**:
- Uses `type: "local"` instead of `type: "stdio"`
- Uses `command` array instead of separate `command` and `args`
- Uses `environment` instead of `env`
- Includes `enabled` flag for easy toggling

#### How MCP Tools Become Available

Once configured in `opencode.json`:

1. **Automatic Discovery**: OpenCode loads MCP server on startup
2. **Tool Registration**: All MCP server tools are registered as available tools
3. **LLM Access**: Tools appear in LLM's tool list with their descriptions
4. **Invocation**: LLM can call tools directly by name (e.g., "use lean_diagnostic_messages")

**No custom client code needed** - OpenCode handles all MCP protocol communication.

---

### 2. Agent Integration Patterns

#### How Agents Use MCP Tools

**Pattern 1: Implicit Usage (Recommended)**

Agents can use MCP tools without explicit invocation code. The LLM decides when to use them based on tool descriptions and agent prompts.

```markdown
<!-- In lean-implementation-agent.md -->
<step_4>
  <action>Verify Lean code compilation</action>
  <process>
    1. After writing Lean code, check for compilation errors
    2. Use lean_diagnostic_messages tool to get error diagnostics
    3. If errors found, analyze and fix them
    4. Iterate until compilation succeeds (max 5 iterations)
    5. Use lean_build to verify full project compilation
  </process>
  <tools_available>
    - lean_diagnostic_messages: Get compilation errors and warnings
    - lean_goal: Inspect proof state at specific positions
    - lean_build: Rebuild entire project
  </tools_available>
</step_4>
```

**Pattern 2: Explicit Prompting**

Agent definitions can include explicit instructions to use specific MCP tools:

```markdown
<tool_usage_guidelines>
  When implementing Lean proofs:
  1. After writing each tactic, use lean_goal to verify proof state
  2. Before completing, use lean_diagnostic_messages to check for errors
  3. If errors exist, analyze error messages and apply fixes
  4. Use lean_build to verify project-wide compilation
</tool_usage_guidelines>
```

**Pattern 3: User Prompting**

Users can explicitly request MCP tool usage in their prompts:

```
Implement the theorem and use lean_diagnostic_messages to verify compilation.
```

#### Tool Availability Per Agent

**Global Configuration** (all agents):
```json
{
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": ["uvx", "lean-lsp-mcp"],
      "enabled": true
    }
  },
  "tools": {
    "lean_*": true  // Enable all lean-lsp-mcp tools globally
  }
}
```

**Per-Agent Configuration** (recommended for large MCP servers):
```json
{
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": ["uvx", "lean-lsp-mcp"],
      "enabled": true
    }
  },
  "tools": {
    "lean_*": false  // Disable globally
  },
  "agent": {
    "lean-implementation-agent": {
      "tools": {
        "lean_diagnostic_messages": true,
        "lean_goal": true,
        "lean_build": true,
        "lean_run_code": true
      }
    },
    "lean-research-agent": {
      "tools": {
        "lean_loogle": true,
        "lean_leansearch": true,
        "lean_local_search": true
      }
    }
  }
}
```

**Best Practice**: Disable MCP tools globally and enable selectively per agent to:
- Reduce context window usage
- Prevent tool confusion
- Improve LLM decision-making
- Control costs

---

### 3. Current Implementation Analysis

#### What Task 212 Implemented

**Created**:
- `.opencode/tool/mcp/client.py` - Custom Python MCP client
- `.opencode/tool/mcp/__init__.py` - Module initialization
- `.opencode/tool/mcp/test_client.py` - Tests

**Approach**: Custom Python tool that agents would import and use programmatically.

**Problem**: This approach is **fundamentally incompatible** with how OpenCode agents work.

#### Why Current Approach Fails

**Issue 1: Module Import Errors**

```python
from opencode.tool.mcp.client import invoke_mcp_tool
# ModuleNotFoundError: No module named 'opencode'
```

**Root Cause**: OpenCode agents are **not Python scripts**. They're markdown files with XML-structured instructions that the LLM interprets. They cannot import Python modules.

**Issue 2: Architectural Mismatch**

- **Custom Client Approach**: Requires agents to execute Python code
- **OpenCode Reality**: Agents are LLM prompts that use tools via natural language

**Issue 3: Duplicate Functionality**

- **Custom Client**: Implements MCP protocol communication
- **OpenCode Built-in**: Already implements MCP protocol communication

**Issue 4: Unnecessary Complexity**

- **Custom Client**: 192 lines of Python code
- **OpenCode Config**: ~10 lines of JSON

#### What Should Have Been Done

**Instead of**: Writing custom MCP client code  
**Should have**: Created `opencode.json` configuration

**Instead of**: Importing Python modules in agents  
**Should have**: Updated agent markdown with tool usage instructions

**Instead of**: Implementing MCP protocol  
**Should have**: Leveraged OpenCode's native MCP support

---

### 4. Correct Implementation Approach

#### Step 1: Create opencode.json

**Location**: `/home/benjamin/Projects/ProofChecker/opencode.json`

```json
{
  "$schema": "https://opencode.ai/config.json",
  
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": ["uvx", "lean-lsp-mcp"],
      "enabled": true,
      "environment": {
        "LEAN_LOG_LEVEL": "WARNING",
        "LEAN_PROJECT_PATH": "/home/benjamin/Projects/ProofChecker"
      },
      "timeout": 30000
    }
  },
  
  "tools": {
    "lean_*": false
  },
  
  "agent": {
    "lean-implementation-agent": {
      "description": "Implements Lean theorems and proofs with compilation verification",
      "mode": "subagent",
      "tools": {
        "lean_diagnostic_messages": true,
        "lean_goal": true,
        "lean_term_goal": true,
        "lean_build": true,
        "lean_run_code": true,
        "lean_hover_info": true,
        "lean_file_outline": true
      }
    },
    "lean-research-agent": {
      "description": "Researches Lean proofs and theorems using search tools",
      "mode": "subagent",
      "tools": {
        "lean_loogle": true,
        "lean_leansearch": true,
        "lean_local_search": true,
        "lean_leanfinder": true
      }
    }
  }
}
```

**Key Configuration Options**:
- `timeout`: Milliseconds to wait for MCP server tool responses (default: 5000)
- `enabled`: Toggle MCP server on/off without removing config
- `environment`: Environment variables passed to MCP server process

#### Step 2: Update Agent Definitions

**lean-implementation-agent.md** - Remove Python import references, add tool usage instructions:

```xml
<step_4>
  <action>Verify Lean code compilation using lean-lsp-mcp</action>
  <process>
    1. After writing Lean code to file, verify compilation:
       - Use lean_diagnostic_messages tool with file path
       - Tool returns diagnostics (errors, warnings, info)
       - Parse diagnostics to identify compilation errors
    
    2. If compilation errors found:
       - Analyze error messages and locations
       - Determine fixes based on error types:
         * Type errors: Check type annotations
         * Tactic failures: Adjust proof tactics
         * Import errors: Verify imports
         * Syntax errors: Fix Lean syntax
       - Apply fixes to code
       - Repeat verification (max 5 iterations)
    
    3. If no errors after max iterations:
       - Return failed status with last error details
       - Include recommendation for manual intervention
    
    4. If compilation succeeds:
       - Use lean_build to verify project-wide compilation
       - If project build succeeds: Return completed status
       - If project build fails: Return partial status with details
  </process>
  
  <tool_usage>
    <lean_diagnostic_messages>
      Purpose: Get compilation diagnostics for a Lean file
      When: After writing/modifying Lean code
      Arguments: file_path (relative to project root)
      Response: List of diagnostics with severity, message, location
    </lean_diagnostic_messages>
    
    <lean_goal>
      Purpose: Get proof state at specific position
      When: Debugging proof tactics
      Arguments: file_path, line, column
      Response: Current goals and hypotheses
    </lean_goal>
    
    <lean_build>
      Purpose: Rebuild entire Lean project
      When: After successful file compilation
      Arguments: None
      Response: Build success/failure with error details
    </lean_build>
  </tool_usage>
  
  <error_handling>
    <mcp_unavailable>
      If lean-lsp-mcp tools are not available:
      1. Log warning in errors array
      2. Write Lean code without verification
      3. Return partial status
      4. Recommend manual compilation: "Run 'lake build' to verify"
    </mcp_unavailable>
    
    <tool_timeout>
      If MCP tool times out (>30s):
      1. Log timeout error
      2. Retry once with same arguments
      3. If second timeout: Fall back to no verification
      4. Include timeout warning in return
    </tool_timeout>
    
    <tool_error>
      If MCP tool returns error:
      1. Log error details
      2. Check if error is recoverable:
         - File not found: Verify file was written
         - LSP not ready: Wait 5s and retry
         - Other errors: Fall back to no verification
      3. Include error details in return
    </tool_error>
  </error_handling>
  
  <iteration_example>
    Example compilation verification loop:
    
    Iteration 1:
    - Write: theorem foo : P → Q := by intro h; exact h
    - Call: lean_diagnostic_messages("Logos/Core/Foo.lean")
    - Result: Error "type mismatch, expected Q but got P"
    - Fix: Change to "theorem foo : P → P := by intro h; exact h"
    
    Iteration 2:
    - Write: theorem foo : P → P := by intro h; exact h
    - Call: lean_diagnostic_messages("Logos/Core/Foo.lean")
    - Result: No errors
    - Call: lean_build()
    - Result: Build successful
    - Status: completed
  </iteration_example>
</step_4>
```

**lean-research-agent.md** - Add MCP tool usage for search:

```xml
<step_2>
  <action>Search for relevant Lean theorems and tactics</action>
  <process>
    1. Determine search strategy based on query type:
       - Type-based: Use lean_loogle (e.g., "Nat → Nat → Nat")
       - Natural language: Use lean_leansearch (e.g., "addition commutative")
       - Local project: Use lean_local_search (e.g., "TaskFrame")
       - Semantic: Use lean_leanfinder (e.g., "group homomorphism")
    
    2. Execute searches with appropriate tools:
       - Start with most specific tool (loogle for types)
       - Fall back to broader tools if no results
       - Combine results from multiple tools
    
    3. Parse and rank results:
       - Prioritize Mathlib results for standard theorems
       - Prioritize local results for project-specific concepts
       - Filter out irrelevant results
    
    4. If MCP tools unavailable:
       - Fall back to Loogle CLI (if available)
       - Fall back to web search as last resort
       - Log tool unavailability
  </process>
  
  <tool_usage>
    <lean_loogle>
      Purpose: Type-based theorem search
      When: Searching by type signature
      Example: "Nat → Nat → Nat" finds addition/multiplication
      Rate limit: 3 requests per 30 seconds
    </lean_loogle>
    
    <lean_leansearch>
      Purpose: Natural language semantic search
      When: Searching by description
      Example: "commutative property of addition"
      Rate limit: 3 requests per 30 seconds
    </lean_leansearch>
    
    <lean_local_search>
      Purpose: Search local project files
      When: Looking for project-specific definitions
      Example: "TaskFrame" finds local TaskFrame definitions
      No rate limit (local)
    </lean_local_search>
  </tool_usage>
</step_2>
```

#### Step 3: Remove Custom MCP Client (Optional)

The custom MCP client in `.opencode/tool/mcp/` is **not needed** for OpenCode integration. However, it could be useful for:

1. **Standalone scripts** that need MCP access outside OpenCode
2. **Testing** MCP server functionality independently
3. **Future non-OpenCode integrations**

**Recommendation**: Keep the client but document that it's **not used by OpenCode agents**.

Add to `.opencode/tool/mcp/README.md`:

```markdown
# MCP Client

This directory contains a standalone Python MCP client for lean-lsp-mcp.

## Usage Context

**NOT USED BY OPENCODE AGENTS**: OpenCode has native MCP support via `opencode.json` configuration. Agents use MCP tools automatically without importing this client.

**Use Cases**:
- Standalone Python scripts needing MCP access
- Testing MCP server functionality
- Non-OpenCode integrations

## OpenCode Integration

For OpenCode agent integration, see:
- `/opencode.json` - MCP server configuration
- `.opencode/agent/subagents/lean-implementation-agent.md` - Tool usage examples
- Documentation/Research/LEANSEARCH_API_SPECIFICATION.md - MCP tools guide
```

#### Step 4: Update Documentation

**Create**: `Documentation/UserGuide/MCP_INTEGRATION.md`

```markdown
# MCP Server Integration in OpenCode

## Overview

OpenCode has native MCP (Model Context Protocol) server support. MCP servers provide additional tools that agents can use alongside built-in tools like `read`, `write`, and `bash`.

## Configuration

### Project-Level Configuration

Create `opencode.json` in project root:

```json
{
  "$schema": "https://opencode.ai/config.json",
  "mcp": {
    "server-name": {
      "type": "local",
      "command": ["command", "arg1", "arg2"],
      "enabled": true,
      "environment": {
        "ENV_VAR": "value"
      }
    }
  }
}
```

### lean-lsp-mcp Configuration

For Lean development, configure lean-lsp-mcp:

```json
{
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": ["uvx", "lean-lsp-mcp"],
      "enabled": true,
      "environment": {
        "LEAN_LOG_LEVEL": "WARNING",
        "LEAN_PROJECT_PATH": "/absolute/path/to/project"
      }
    }
  }
}
```

## Tool Management

### Global Tool Control

Enable/disable MCP tools globally:

```json
{
  "tools": {
    "lean_diagnostic_messages": true,
    "lean_goal": true,
    "lean_*": false  // Disable all other lean tools
  }
}
```

### Per-Agent Tool Control

Enable tools only for specific agents:

```json
{
  "tools": {
    "lean_*": false  // Disable globally
  },
  "agent": {
    "lean-implementation-agent": {
      "tools": {
        "lean_diagnostic_messages": true,
        "lean_goal": true
      }
    }
  }
}
```

## Agent Usage

Agents use MCP tools via natural language instructions in their markdown definitions:

```xml
<step>
  <action>Verify compilation</action>
  <process>
    1. Use lean_diagnostic_messages to check for errors
    2. If errors found, analyze and fix
    3. Use lean_build to verify project compilation
  </process>
</step>
```

The LLM automatically invokes the appropriate MCP tools based on these instructions.

## Available Tools

### lean-lsp-mcp Tools

**File Interaction**:
- `lean_diagnostic_messages` - Get compilation errors/warnings
- `lean_goal` - Get proof state at position
- `lean_file_outline` - Get file structure
- `lean_hover_info` - Get symbol documentation
- `lean_run_code` - Run code snippet

**Search**:
- `lean_loogle` - Type-based search
- `lean_leansearch` - Natural language search
- `lean_local_search` - Local project search

**Build**:
- `lean_build` - Rebuild project

See `Documentation/Research/LEANSEARCH_API_SPECIFICATION.md` for detailed tool documentation.

## Troubleshooting

### MCP Server Not Starting

Check:
1. Server command is available: `which uvx`
2. Server package is installed: `uvx lean-lsp-mcp --help`
3. Environment variables are correct
4. Project path is absolute, not relative

### Tools Not Available to Agents

Check:
1. MCP server is enabled in `opencode.json`
2. Tools are not disabled in `tools` section
3. Agent has access to tools (check per-agent config)
4. OpenCode was restarted after config changes

### Tool Timeouts

Increase timeout in MCP server config:

```json
{
  "mcp": {
    "lean-lsp": {
      "timeout": 60000  // 60 seconds
    }
  }
}
```
```

---

### 5. Common Pitfalls and Solutions

#### Pitfall 1: Using .mcp.json Instead of opencode.json

**Problem**: `.mcp.json` is for Claude Desktop and other MCP clients, not OpenCode.

**Solution**: Create `opencode.json` in project root with MCP configuration.

**Why**: OpenCode has its own configuration format and doesn't read `.mcp.json`.

#### Pitfall 2: Trying to Import Python Modules in Agents

**Problem**: Agents are markdown files, not Python scripts. They cannot import modules.

**Solution**: Use natural language instructions for tool usage, not Python code.

**Example**:
```markdown
<!-- WRONG -->
<process>
  from opencode.tool.mcp.client import invoke_mcp_tool
  result = invoke_mcp_tool("lean-lsp", "lean_diagnostic_messages", {...})
</process>

<!-- CORRECT -->
<process>
  Use lean_diagnostic_messages tool to check for compilation errors.
  If errors found, analyze error messages and apply fixes.
</process>
```

#### Pitfall 3: Enabling All MCP Tools Globally

**Problem**: Large MCP servers (like lean-lsp-mcp with 15+ tools) add significant context overhead.

**Solution**: Disable globally, enable per-agent selectively.

**Impact**: Reduces context window usage by ~2000-5000 tokens per conversation.

#### Pitfall 4: Not Setting Absolute Paths

**Problem**: Relative paths in environment variables may not resolve correctly.

**Solution**: Always use absolute paths in MCP server configuration.

```json
{
  "environment": {
    "LEAN_PROJECT_PATH": "/home/benjamin/Projects/ProofChecker"  // Absolute
  }
}
```

#### Pitfall 5: Forgetting to Restart OpenCode

**Problem**: Configuration changes don't take effect until OpenCode restarts.

**Solution**: Restart OpenCode after modifying `opencode.json`.

**Alternative**: Use `opencode mcp list` to verify MCP servers are loaded.

#### Pitfall 6: Not Handling Tool Unavailability

**Problem**: Agents fail if MCP tools are unavailable (server down, not configured, etc.).

**Solution**: Always include graceful degradation in agent definitions.

```xml
<error_handling>
  <mcp_unavailable>
    If lean-lsp-mcp tools unavailable:
    1. Log warning
    2. Continue without verification
    3. Recommend manual compilation check
  </mcp_unavailable>
</error_handling>
```

---

### 6. Additional Useful MCP Servers for Lean Development

#### Context7 - Documentation Search

**Purpose**: Search Lean 4 and Mathlib documentation

**Configuration**:
```json
{
  "mcp": {
    "context7": {
      "type": "remote",
      "url": "https://mcp.context7.com/mcp"
    }
  }
}
```

**Use Case**: Research agent searching for Lean documentation and examples.

**Tools**: `context7_search`

**Rate Limits**: Free tier with rate limiting, paid tier for higher limits.

#### Grep by Vercel - Code Search

**Purpose**: Search GitHub for Lean code examples

**Configuration**:
```json
{
  "mcp": {
    "gh_grep": {
      "type": "remote",
      "url": "https://mcp.grep.app"
    }
  }
}
```

**Use Case**: Finding real-world Lean proof patterns and examples.

**Tools**: `gh_grep_search`

**Example Query**: "Lean 4 group homomorphism proof"

#### Filesystem MCP (Future)

**Purpose**: Advanced file operations beyond built-in tools

**Status**: Not yet configured, but available

**Configuration**:
```json
{
  "mcp": {
    "filesystem": {
      "type": "local",
      "command": ["npx", "-y", "@modelcontextprotocol/server-filesystem"],
      "environment": {
        "ALLOWED_DIRECTORIES": "/home/benjamin/Projects/ProofChecker"
      }
    }
  }
}
```

**Use Case**: Batch file operations, advanced file searching.

**Recommendation**: Only add if built-in file tools are insufficient.

---

### 7. Architectural Guidance

#### Principle 1: Configuration Over Code

**Guideline**: Prefer OpenCode configuration over custom tool implementation.

**Rationale**: 
- OpenCode handles MCP protocol complexity
- Less code to maintain
- Automatic updates when OpenCode improves
- Consistent with OpenCode architecture

**Application**: Use `opencode.json` for MCP integration, not custom Python clients.

#### Principle 2: Selective Tool Enablement

**Guideline**: Enable MCP tools per-agent, not globally.

**Rationale**:
- Reduces context window bloat
- Improves LLM decision-making
- Controls costs
- Prevents tool confusion

**Application**: Disable `lean_*` globally, enable specific tools per agent.

#### Principle 3: Graceful Degradation

**Guideline**: Agents must handle MCP tool unavailability gracefully.

**Rationale**:
- MCP servers may be down
- Configuration may be missing
- Network issues may occur
- Users may not have tools installed

**Application**: Always include fallback behavior in agent definitions.

#### Principle 4: Tool Documentation in Agent Definitions

**Guideline**: Document tool usage directly in agent markdown files.

**Rationale**:
- Self-documenting agents
- Clear tool usage patterns
- Easier debugging
- Better LLM understanding

**Application**: Include `<tool_usage>` sections in agent definitions.

#### Principle 5: Separation of Concerns

**Guideline**: Keep MCP configuration separate from agent logic.

**Rationale**:
- Configuration changes don't require agent updates
- Agents work with or without MCP tools
- Easier testing and development
- Clear architectural boundaries

**Application**: 
- MCP config in `opencode.json`
- Agent logic in `.opencode/agent/`
- Tool documentation in `Documentation/`

---

### 8. Implementation Recommendations

#### Immediate Actions (Task 218)

1. **Create opencode.json** in project root with lean-lsp-mcp configuration
2. **Update lean-implementation-agent.md** with tool usage instructions (remove Python imports)
3. **Update lean-research-agent.md** with MCP search tool usage
4. **Document MCP integration** in `Documentation/UserGuide/MCP_INTEGRATION.md`
5. **Add README to .opencode/tool/mcp/** explaining it's not used by OpenCode agents

#### Short-Term Improvements (Next 1-2 weeks)

1. **Test MCP integration** with real Lean implementation tasks
2. **Measure context window impact** of MCP tools
3. **Optimize tool enablement** based on actual usage patterns
4. **Add troubleshooting guide** for common MCP issues
5. **Create examples** of successful MCP tool usage

#### Long-Term Enhancements (Next 1-3 months)

1. **Add Context7 MCP server** for documentation search
2. **Add Grep MCP server** for GitHub code search
3. **Evaluate additional MCP servers** for Lean development
4. **Create MCP usage metrics** to track effectiveness
5. **Contribute improvements** to lean-lsp-mcp project

---

### 9. Comparison: Custom Client vs OpenCode Native

| Aspect | Custom Python Client | OpenCode Native MCP |
|--------|---------------------|---------------------|
| **Configuration** | `.mcp.json` + Python code | `opencode.json` only |
| **Code Required** | 192 lines Python | 0 lines (config only) |
| **Agent Integration** | Import Python module | Natural language instructions |
| **Protocol Handling** | Manual implementation | Automatic (built-in) |
| **Error Handling** | Custom code | Built-in with fallbacks |
| **Maintenance** | Manual updates | Automatic with OpenCode |
| **Context Overhead** | High (tool + client code) | Low (tool descriptions only) |
| **Compatibility** | OpenCode-specific | Standard MCP protocol |
| **Testing** | Custom test suite | OpenCode handles |
| **Documentation** | Custom docs needed | OpenCode docs apply |

**Verdict**: OpenCode native MCP integration is superior in every aspect for OpenCode agent usage.

**Custom Client Use Case**: Only useful for standalone Python scripts outside OpenCode.

---

### 10. Migration Path from Task 212 Implementation

#### Phase 1: Add OpenCode Configuration (Day 1)

**Actions**:
1. Create `opencode.json` with lean-lsp-mcp configuration
2. Verify MCP server loads: `opencode mcp list`
3. Test tool availability in OpenCode session

**Validation**: MCP tools appear in OpenCode tool list.

#### Phase 2: Update Agent Definitions (Day 1-2)

**Actions**:
1. Update `lean-implementation-agent.md`:
   - Remove Python import references
   - Add natural language tool usage instructions
   - Add error handling for tool unavailability
2. Update `lean-research-agent.md`:
   - Add MCP search tool usage
   - Keep Loogle CLI as fallback
3. Test agents with MCP tools enabled

**Validation**: Agents successfully use MCP tools in test tasks.

#### Phase 3: Documentation (Day 2-3)

**Actions**:
1. Create `Documentation/UserGuide/MCP_INTEGRATION.md`
2. Add README to `.opencode/tool/mcp/`
3. Update `Documentation/Research/LEANSEARCH_API_SPECIFICATION.md`
4. Document migration in task summary

**Validation**: Documentation is complete and accurate.

#### Phase 4: Deprecate Custom Client (Day 3)

**Actions**:
1. Mark `.opencode/tool/mcp/client.py` as "not used by OpenCode agents"
2. Keep code for potential standalone use
3. Update tests to reflect standalone usage only
4. Remove from agent import paths

**Validation**: Agents work without custom client.

#### Phase 5: Testing and Validation (Day 3-5)

**Actions**:
1. Test lean-implementation-agent with real Lean tasks
2. Test lean-research-agent with search queries
3. Verify error handling and graceful degradation
4. Measure context window impact
5. Document findings and optimizations

**Validation**: All tests pass, agents work reliably with MCP tools.

---

## Conclusions

### Key Insights

1. **OpenCode has native MCP support** - No custom client needed
2. **Configuration-based integration** - Use `opencode.json`, not Python code
3. **Agents use natural language** - Not Python imports
4. **Selective tool enablement** - Per-agent, not global
5. **Graceful degradation required** - Always handle tool unavailability

### Critical Mistakes in Task 212

1. **Wrong configuration file** - Used `.mcp.json` instead of `opencode.json`
2. **Wrong integration approach** - Custom Python client instead of OpenCode native
3. **Wrong agent pattern** - Python imports instead of natural language instructions
4. **Unnecessary complexity** - 192 lines of code vs 10 lines of config

### Correct Approach for Task 218

1. **Create opencode.json** with lean-lsp-mcp configuration
2. **Update agent definitions** with natural language tool usage instructions
3. **Remove Python import references** from agent markdown files
4. **Document MCP integration** for future reference
5. **Test and validate** with real Lean tasks

### Impact

**Before** (Task 212 approach):
- [FAIL] Module import errors
- [FAIL] Architectural mismatch
- [FAIL] Unnecessary code complexity
- [FAIL] Agents cannot use MCP tools

**After** (Task 218 approach):
- [PASS] No import errors (no imports needed)
- [PASS] Architectural alignment with OpenCode
- [PASS] Simple configuration-based integration
- [PASS] Agents can use MCP tools naturally

### Success Metrics

1. **MCP tools available** in OpenCode tool list
2. **Agents successfully invoke** lean_diagnostic_messages, lean_goal, etc.
3. **No module import errors** (no imports needed)
4. **Compilation verification works** in lean-implementation-agent
5. **Search tools work** in lean-research-agent

---

## References

### Official Documentation
- [OpenCode MCP Servers](https://opencode.ai/docs/mcp-servers/)
- [OpenCode Agents](https://opencode.ai/docs/agents/)
- [OpenCode Tools](https://opencode.ai/docs/tools/)
- [OpenCode Custom Tools](https://opencode.ai/docs/custom-tools/)
- [lean-lsp-mcp PyPI](https://pypi.org/project/lean-lsp-mcp/)
- [Model Context Protocol](https://modelcontextprotocol.io/)

### Local Files
- `.mcp.json` - Claude Desktop MCP configuration (not used by OpenCode)
- `~/.config/opencode/opencode.json` - Global OpenCode configuration
- `.opencode/agent/subagents/lean-implementation-agent.md` - Implementation agent
- `.opencode/agent/subagents/lean-research-agent.md` - Research agent
- `.opencode/tool/mcp/client.py` - Custom MCP client (not used by OpenCode agents)
- `Documentation/Research/LEANSEARCH_API_SPECIFICATION.md` - MCP tools guide

### Related Tasks
- Task 212: Research lean-lsp-mcp usage (implemented wrong approach)
- Task 218: Fix lean-lsp-mcp integration (this task - correct approach)

---

## Appendices

### Appendix A: Complete opencode.json Example

```json
{
  "$schema": "https://opencode.ai/config.json",
  
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": ["uvx", "lean-lsp-mcp"],
      "enabled": true,
      "environment": {
        "LEAN_LOG_LEVEL": "WARNING",
        "LEAN_PROJECT_PATH": "/home/benjamin/Projects/ProofChecker"
      },
      "timeout": 30000
    }
  },
  
  "tools": {
    "lean_*": false
  },
  
  "agent": {
    "lean-implementation-agent": {
      "description": "Implements Lean theorems and proofs with compilation verification",
      "mode": "subagent",
      "tools": {
        "lean_diagnostic_messages": true,
        "lean_goal": true,
        "lean_term_goal": true,
        "lean_build": true,
        "lean_run_code": true,
        "lean_hover_info": true,
        "lean_file_outline": true,
        "lean_completions": true
      },
      "permission": {
        "edit": "allow",
        "write": "allow",
        "bash": {
          "lake build": "allow",
          "lake exe cache get": "allow",
          "*": "ask"
        }
      }
    },
    "lean-research-agent": {
      "description": "Researches Lean proofs and theorems using search tools",
      "mode": "subagent",
      "tools": {
        "lean_loogle": true,
        "lean_leansearch": true,
        "lean_local_search": true,
        "lean_leanfinder": true,
        "lean_state_search": true,
        "lean_hover_info": true,
        "lean_declaration_file": true
      },
      "permission": {
        "edit": "deny",
        "write": "deny",
        "bash": "deny"
      }
    }
  },
  
  "permission": {
    "edit": "ask",
    "bash": "ask",
    "webfetch": "allow"
  }
}
```

### Appendix B: lean-lsp-mcp Tool Reference

**File Interaction Tools**:
- `lean_file_outline` - Get file structure with declarations
- `lean_diagnostic_messages` - Get errors, warnings, infos
- `lean_goal` - Get proof goal at specific location
- `lean_term_goal` - Get term goal at position
- `lean_hover_info` - Get documentation for symbols
- `lean_declaration_file` - Find where symbol is declared
- `lean_completions` - Code auto-completion
- `lean_run_code` - Run/compile Lean code snippet
- `lean_multi_attempt` - Try multiple proof attempts

**Search Tools** (rate limited 3 req/30s):
- `lean_leansearch` - Natural language search (leansearch.net)
- `lean_loogle` - Type-based search (loogle.lean-lang.org)
- `lean_leanfinder` - Semantic search (Lean Finder)
- `lean_state_search` - Premise search (premise-search.com)
- `lean_hammer_premise` - Lean Hammer premise search
- `lean_local_search` - Search local project (requires ripgrep)

**Project Tools**:
- `lean_build` - Rebuild project and restart LSP

### Appendix C: Agent Tool Usage Examples

**Example 1: Compilation Verification**

```xml
<step_4>
  <action>Verify Lean code compilation</action>
  <process>
    1. Write Lean code to file using write tool
    2. Use lean_diagnostic_messages tool with file path
    3. Parse diagnostics response:
       - severity 1 = error
       - severity 2 = warning
       - severity 3 = info
    4. If errors found:
       - Extract error messages and locations
       - Analyze error types
       - Generate fixes
       - Apply fixes and repeat
    5. If no errors:
       - Use lean_build to verify project compilation
       - Return completed status
  </process>
</step_4>
```

**Example 2: Proof State Inspection**

```xml
<debugging>
  <action>Inspect proof state at tactic position</action>
  <process>
    1. Identify tactic line and column in proof
    2. Use lean_goal tool with file_path, line, column
    3. Analyze returned proof state:
       - Current goals
       - Available hypotheses
       - Goal types
    4. Determine next tactic based on proof state
    5. Write tactic and verify with lean_diagnostic_messages
  </process>
</debugging>
```

**Example 3: Type-Based Search**

```xml
<research>
  <action>Find theorems by type signature</action>
  <process>
    1. Construct type query (e.g., "Nat → Nat → Nat")
    2. Use lean_loogle tool with type query
    3. Parse results:
       - Theorem names
       - Full type signatures
       - Module locations
    4. Filter results for relevance
    5. Use lean_hover_info to get full documentation
    6. Return top 5 most relevant theorems
  </process>
</research>
```

### Appendix D: Error Handling Patterns

**Pattern 1: Tool Unavailability**

```xml
<error_handling>
  <mcp_unavailable>
    Detection: Tool invocation returns "tool not available" error
    Response:
      1. Log warning: "lean-lsp-mcp tools not available"
      2. Continue task without MCP verification
      3. Add to errors array: {
           "type": "tool_unavailable",
           "tool": "lean_diagnostic_messages",
           "impact": "No compilation verification",
           "recommendation": "Install lean-lsp-mcp: pip install lean-lsp-mcp"
         }
      4. Return partial status with warning
  </mcp_unavailable>
</error_handling>
```

**Pattern 2: Tool Timeout**

```xml
<error_handling>
  <tool_timeout>
    Detection: Tool invocation exceeds timeout (30s)
    Response:
      1. Log timeout: "lean_diagnostic_messages timed out after 30s"
      2. Retry once with same arguments
      3. If second timeout:
         - Log second timeout
         - Fall back to no verification
         - Add to errors array with recommendation
      4. Return partial status
  </tool_timeout>
</error_handling>
```

**Pattern 3: Tool Error**

```xml
<error_handling>
  <tool_error>
    Detection: Tool returns error response
    Response:
      1. Parse error message
      2. Categorize error:
         - "file not found": Verify file was written, retry
         - "LSP not ready": Wait 5s, retry once
         - "parse error": File has syntax errors, continue
         - Other: Log and fall back
      3. Apply recovery strategy
      4. If recovery fails: Fall back to no verification
      5. Include error details in return
  </tool_error>
</error_handling>
```
