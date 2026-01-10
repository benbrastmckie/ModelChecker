# Lean LSP MCP Usage Research Report

**Task**: 212  
**Topic**: Research and improve lean-lsp-mcp usage in Lean implementation agent  
**Date**: 2025-12-28  
**Session ID**: sess_1735417200_lsp001  
**Agent**: lean-research-agent  

---

## Executive Summary

This research investigated how `lean-lsp-mcp` is intended to be used and identified critical gaps preventing its usage in the Lean implementation agent. The tool is **configured but not being invoked** during Lean implementation tasks. Key findings:

1. **lean-lsp-mcp is properly configured** in `.mcp.json` and is available via `uvx lean-lsp-mcp`
2. **lean-implementation-agent.md has placeholder logic** but lacks concrete MCP tool invocation patterns
3. **No MCP tool invocation mechanism exists** in the current agent workflow
4. **Context files describe capabilities** but don't explain how to invoke MCP tools from agents
5. **Similar issues exist in lean-research-agent** for Loogle integration

---

## Research Scope

### Objectives
1. [PASS] Research lean-lsp-mcp tool usage best practices
2. [PASS] Understand how to invoke lean-lsp-mcp in agent workflows
3. [PASS] Identify gaps in lean-implementation-agent preventing tool usage
4. [PASS] Determine context file improvements needed
5. [PASS] Review lean-research-agent for similar issues

### Tools Used
- **Web Research**: PyPI documentation, GitHub repository
- **File Analysis**: Agent definitions, context files, MCP configuration
- **Command Testing**: `uvx lean-lsp-mcp --help`

---

## Findings

### 1. lean-lsp-mcp Capabilities

#### Overview
`lean-lsp-mcp` (v0.17.2) is a Model Context Protocol server that provides agentic interaction with the Lean theorem prover via LSP. It's maintained by Oliver Dressler and available on PyPI.

#### Key Features

**File Interactions (LSP)**:
- `lean_file_outline` - Get file structure with declarations
- `lean_diagnostic_messages` - Get errors, warnings, infos
- `lean_goal` - Get proof goal at specific location
- `lean_term_goal` - Get term goal at position
- `lean_hover_info` - Get documentation for symbols
- `lean_declaration_file` - Find where symbol is declared
- `lean_completions` - Code auto-completion
- `lean_run_code` - Run/compile Lean code snippet
- `lean_multi_attempt` - Try multiple proof attempts

**Local Search Tools**:
- `lean_local_search` - Search local project (requires ripgrep)

**External Search Tools** (rate limited 3 req/30s):
- `lean_leansearch` - Natural language search (leansearch.net)
- `lean_loogle` - Type-based search (loogle.lean-lang.org)
- `lean_leanfinder` - Semantic search (Lean Finder)
- `lean_state_search` - Premise search (premise-search.com)
- `lean_hammer_premise` - Lean Hammer premise search

**Project Tools**:
- `lean_build` - Rebuild project and restart LSP

#### Configuration

**Basic Setup** (already configured in `.mcp.json`):
```json
{
  "mcpServers": {
    "lean-lsp": {
      "type": "stdio",
      "command": "uvx",
      "args": ["lean-lsp-mcp"],
      "env": {
        "LEAN_LOG_LEVEL": "WARNING",
        "LEAN_PROJECT_PATH": "/home/benjamin/Documents/Philosophy/Projects/ProofChecker"
      }
    }
  }
}
```

**Environment Variables**:
- `LEAN_LOG_LEVEL`: "INFO", "WARNING", "ERROR", "NONE" (default: "INFO")
- `LEAN_PROJECT_PATH`: Project root path
- `LEAN_LSP_MCP_TOKEN`: Bearer auth token (for HTTP/SSE transport)
- `LEAN_STATE_SEARCH_URL`: Self-hosted premise-search URL
- `LEAN_HAMMER_URL`: Self-hosted Lean Hammer URL
- `LEAN_LOOGLE_LOCAL`: Enable local loogle (avoids rate limits)
- `LEAN_LOOGLE_CACHE_DIR`: Override loogle cache dir

**Transport Methods**:
- `stdio` (default) - Standard input/output
- `streamable-http` - HTTP streaming
- `sse` - Server-sent events (legacy)

#### Usage Workflow

**Recommended Workflow for Proof Implementation**:
1. Write proof tactic line
2. Call `lean_goal` to get current proof state
3. Check goals and hypotheses
4. Call `lean_diagnostic_messages` to check for errors
5. If no errors, proceed to next tactic
6. Iterate until proof complete
7. Call `lean_build` to verify full project compilation

**Example Usage Pattern**:
```
1. Write: `intro h`
2. Call: lean_goal(file="Theorem.lean", line=45, column=10)
3. Response: Shows updated goals after intro
4. Call: lean_diagnostic_messages(file="Theorem.lean")
5. Response: No errors
6. Continue with next tactic
```

---

### 2. Current Configuration Status

#### .mcp.json Analysis

**Status**: [PASS] Properly configured

The `.mcp.json` file correctly configures lean-lsp-mcp:
- Server name: "lean-lsp"
- Transport: stdio
- Command: uvx lean-lsp-mcp
- Environment variables set (LEAN_LOG_LEVEL, LEAN_PROJECT_PATH)

**Verification**:
```bash
$ uvx lean-lsp-mcp --help
usage: lean-lsp-mcp [-h] [--transport {stdio,streamable-http,sse}]
                    [--host HOST] [--port PORT] [--loogle-local]
                    [--loogle-cache-dir LOOGLE_CACHE_DIR]

Lean LSP MCP Server
```

Tool is installed and accessible.

#### Context Files Analysis

**mcp-tools-guide.md** (Status: [YELLOW] Partial):
- [PASS] Documents lean-lsp-mcp capabilities
- [PASS] Describes when to use each tool
- [PASS] Provides example usage patterns
- [FAIL] Does NOT explain how to invoke MCP tools from agents
- [FAIL] Shows TypeScript examples, not agent invocation patterns
- [FAIL] No concrete integration instructions

**lsp-integration.md** (Status: [YELLOW] Partial):
- [PASS] Documents LSP protocol details
- [PASS] Describes connection management
- [PASS] Provides message format examples
- [FAIL] Focused on low-level LSP protocol, not MCP tool usage
- [FAIL] No agent integration patterns

**Key Gap**: Context files describe WHAT the tools do, but not HOW agents should invoke them.

---

### 3. lean-implementation-agent.md Analysis

#### Current State

**File Location**: `.opencode/agent/subagents/lean-implementation-agent.md`

**Step 4 Analysis** (Check compilation using lean-lsp-mcp):

```xml
<step_4>
  <action>Check compilation using lean-lsp-mcp</action>
  <process>
    1. If lean-lsp-mcp available:
       a. Send Lean files for compilation
       b. Receive diagnostics (errors, warnings)
       c. If errors: Analyze and fix
       d. Iterate until compilation succeeds
       e. Max iterations: 5
    2. If lean-lsp-mcp unavailable:
       a. Log tool unavailability to errors.json
       b. Write files without compilation check
       c. Include warning in return
       d. Recommend manual compilation check
  </process>
  <tool_integration>
    lean-lsp-mcp provides:
    - Compilation checking
    - Type error diagnostics
    - Tactic suggestions
    - Proof state inspection
  </tool_integration>
</step_4>
```

#### Critical Gaps Identified

**Gap 1: No MCP Tool Invocation Mechanism**
- Process says "Send Lean files for compilation"
- But HOW to send files is not specified
- No tool invocation syntax provided
- No example of calling MCP tools

**Gap 2: Vague Tool Availability Check**
- Says "If lean-lsp-mcp available"
- But doesn't specify how to check availability
- No code for checking .mcp.json
- No fallback detection logic

**Gap 3: Missing Iteration Logic**
- Says "Iterate until compilation succeeds"
- But no concrete iteration pattern
- No error parsing logic
- No fix generation strategy

**Gap 4: No Concrete Examples**
- No example of calling `lean_diagnostic_messages`
- No example of calling `lean_goal`
- No example of parsing responses
- No example of error handling

**Gap 5: Graceful Degradation Incomplete**
- Says "Log tool unavailability"
- But no specification of error format
- No guidance on partial results
- No recovery recommendations

#### What's Missing

**Missing Section 1: MCP Tool Invocation**
```xml
<mcp_tool_invocation>
  <method>Use MCP protocol to invoke tools</method>
  <syntax>
    # Check availability
    mcp_available = check_mcp_server("lean-lsp")
    
    # Invoke diagnostic check
    result = invoke_mcp_tool(
      server="lean-lsp",
      tool="lean_diagnostic_messages",
      arguments={
        "file_path": "Logos/Core/NewTheorem.lean"
      }
    )
    
    # Parse response
    diagnostics = result["diagnostics"]
    errors = [d for d in diagnostics if d["severity"] == 1]
  </syntax>
</mcp_tool_invocation>
```

**Missing Section 2: Iterative Compilation Loop**
```xml
<compilation_loop>
  <max_iterations>5</max_iterations>
  <process>
    for iteration in range(max_iterations):
      1. Write current Lean code to file
      2. Call lean_diagnostic_messages(file_path)
      3. Parse diagnostics for errors
      4. If no errors: break (success)
      5. If errors:
         a. Analyze error messages
         b. Generate fixes based on error types
         c. Apply fixes to code
         d. Continue to next iteration
      6. If iteration == max_iterations - 1:
         - Return failed status
         - Include last error messages
         - Recommend manual intervention
  </process>
</compilation_loop>
```

**Missing Section 3: Tool Availability Detection**
```xml
<tool_availability_check>
  <method>Check .mcp.json for lean-lsp server</method>
  <implementation>
    import json
    
    def check_lean_lsp_available():
      try:
        with open('.mcp.json', 'r') as f:
          config = json.load(f)
        
        if 'mcpServers' in config:
          if 'lean-lsp' in config['mcpServers']:
            server = config['mcpServers']['lean-lsp']
            # Verify command exists
            if server['command'] == 'uvx':
              # Check uvx available
              result = subprocess.run(['which', 'uvx'], 
                                     capture_output=True)
              return result.returncode == 0
        
        return False
      except:
        return False
  </implementation>
</tool_availability_check>
```

---

### 4. lean-research-agent.md Analysis

#### Current State

**File Location**: `.opencode/agent/subagents/lean-research-agent.md`

**Loogle Integration Status**: [GREEN] Better than lean-implementation-agent

The lean-research-agent has MORE detailed integration for Loogle CLI:
- [PASS] Detailed Loogle client implementation
- [PASS] Process startup logic
- [PASS] Query execution patterns
- [PASS] Error handling specifics
- [PASS] Graceful degradation

**However**: Loogle CLI is different from lean-lsp-mcp MCP tools:
- Loogle: Direct CLI process (subprocess.Popen)
- lean-lsp-mcp: MCP protocol (requires MCP client)

**Key Difference**:
```python
# Loogle (CLI process)
process = subprocess.Popen(
  [binary_path, "--json", "--interactive"],
  stdin=subprocess.PIPE,
  stdout=subprocess.PIPE
)

# lean-lsp-mcp (MCP protocol)
result = mcp_client.call_tool(
  server="lean-lsp",
  tool="lean_diagnostic_messages",
  arguments={"file_path": "file.lean"}
)
```

#### Similar Gaps

**Gap 1: No MCP Tool Invocation for LeanSearch/LeanExplore**
- lean-research-agent mentions LeanSearch and LeanExplore
- But these are marked "NOT YET INTEGRATED"
- No MCP invocation patterns provided
- Would need similar MCP client usage

**Gap 2: Mixed Tool Types**
- Loogle: CLI tool (subprocess)
- LeanSearch: REST API (HTTP)
- LeanExplore: Unknown (needs research)
- lean-lsp-mcp: MCP protocol

Different integration patterns needed for each.

---

### 5. MCP Tool Invocation Patterns

#### How MCP Tools Should Be Invoked

Based on MCP protocol and lean-lsp-mcp documentation:

**Pattern 1: Direct MCP Client Usage**
```python
from mcp import Client

# Initialize MCP client
client = Client()

# Connect to server
await client.connect_stdio(
  command="uvx",
  args=["lean-lsp-mcp"],
  env={
    "LEAN_LOG_LEVEL": "WARNING",
    "LEAN_PROJECT_PATH": "/path/to/project"
  }
)

# Call tool
result = await client.call_tool(
  name="lean_diagnostic_messages",
  arguments={
    "file_path": "Logos/Core/Theorem.lean"
  }
)

# Parse result
diagnostics = result.content[0].text
```

**Pattern 2: Via Claude Code MCP Integration**

If running in Claude Code environment with MCP configured:
```
# Agent can request MCP tool usage via special syntax
Use the lean_diagnostic_messages tool to check file.lean for errors.

# Claude Code runtime handles:
1. Routing to configured MCP server
2. Invoking tool with arguments
3. Returning results to agent
```

**Pattern 3: Via Task Tool (Recommended for Agents)**

Agents should use a task tool wrapper:
```python
# In agent workflow
result = task_tool(
  action="invoke_mcp_tool",
  server="lean-lsp",
  tool="lean_diagnostic_messages",
  arguments={
    "file_path": "Logos/Core/Theorem.lean"
  }
)

# task_tool handles:
# - MCP client initialization
# - Server connection
# - Tool invocation
# - Error handling
# - Result formatting
```

#### Current Implementation Gap

**Problem**: No task tool or MCP client wrapper exists for agents to use.

**Evidence**:
- No `invoke_mcp_tool` task tool defined
- No MCP client initialization in agent workflows
- No examples of MCP tool invocation in any agent
- Agents have no mechanism to call MCP tools

**Impact**: lean-lsp-mcp is configured but completely unused.

---

### 6. Integration Requirements

#### Requirement 1: MCP Client Wrapper

**Need**: Task tool or utility function for MCP tool invocation

**Specification**:
```python
def invoke_mcp_tool(
  server: str,           # "lean-lsp"
  tool: str,             # "lean_diagnostic_messages"
  arguments: dict,       # {"file_path": "..."}
  timeout: int = 30      # seconds
) -> dict:
  """
  Invoke an MCP tool on a configured server.
  
  Returns:
    {
      "success": bool,
      "result": dict | str,
      "error": str | None
    }
  """
  # 1. Load .mcp.json configuration
  # 2. Initialize MCP client for server
  # 3. Connect to server (stdio/http/sse)
  # 4. Call tool with arguments
  # 5. Handle timeout
  # 6. Parse and return result
  # 7. Handle errors gracefully
```

**Location**: `.opencode/tool/mcp/client.py` (new file)

#### Requirement 2: Agent Workflow Updates

**lean-implementation-agent.md needs**:

1. **Import MCP client wrapper**:
   ```xml
   <imports>
     from opencode.tool.mcp.client import invoke_mcp_tool
   </imports>
   ```

2. **Concrete tool invocation in step_4**:
   ```xml
   <step_4>
     <action>Check compilation using lean-lsp-mcp</action>
     <process>
       1. Check tool availability:
          mcp_available = check_mcp_server_configured("lean-lsp")
       
       2. If mcp_available:
          for iteration in range(5):
            a. Write Lean code to file
            b. Invoke diagnostic check:
               result = invoke_mcp_tool(
                 server="lean-lsp",
                 tool="lean_diagnostic_messages",
                 arguments={"file_path": lean_file_path}
               )
            c. Parse diagnostics:
               diagnostics = parse_diagnostics(result)
               errors = [d for d in diagnostics if d.severity == 1]
            d. If no errors: break (success)
            e. If errors:
               - Analyze error messages
               - Generate fixes
               - Apply fixes
               - Continue iteration
          
          If iteration == 4 and errors:
            - Return failed status
            - Include error details
       
       3. If not mcp_available:
          - Log to errors.json
          - Return partial status
          - Recommend installing lean-lsp-mcp
     </process>
   </step_4>
   ```

3. **Error handling patterns**:
   ```xml
   <error_handling>
     <mcp_timeout>
       If invoke_mcp_tool times out:
       - Log timeout error
       - Fall back to file write without verification
       - Return partial status
       - Recommend manual lake build
     </mcp_timeout>
     
     <mcp_error>
       If invoke_mcp_tool returns error:
       - Log error details
       - Check if recoverable
       - If recoverable: retry once
       - If not: fall back to file write
     </mcp_error>
   </error_handling>
   ```

#### Requirement 3: Context File Updates

**mcp-tools-guide.md needs**:

1. **Agent Integration Section**:
   ```markdown
   ## Agent Integration
   
   ### Invoking MCP Tools from Agents
   
   Agents invoke MCP tools using the `invoke_mcp_tool` utility:
   
   ```python
   from opencode.tool.mcp.client import invoke_mcp_tool
   
   # Check diagnostics
   result = invoke_mcp_tool(
     server="lean-lsp",
     tool="lean_diagnostic_messages",
     arguments={"file_path": "Logos/Core/Theorem.lean"}
   )
   
   if result["success"]:
     diagnostics = result["result"]
     # Process diagnostics
   else:
     # Handle error
     error = result["error"]
   ```
   
   ### Available Tools by Agent
   
   **lean-implementation-agent**:
   - `lean_diagnostic_messages` - Check for compilation errors
   - `lean_goal` - Get proof state at position
   - `lean_run_code` - Test code snippet
   - `lean_build` - Rebuild project
   
   **lean-research-agent**:
   - `lean_loogle` - Type-based search (if not using local CLI)
   - `lean_leansearch` - Natural language search
   - `lean_local_search` - Local project search
   ```

2. **Tool Invocation Examples**:
   ```markdown
   ## Tool Invocation Examples
   
   ### Example 1: Check Compilation Errors
   
   ```python
   result = invoke_mcp_tool(
     server="lean-lsp",
     tool="lean_diagnostic_messages",
     arguments={"file_path": "Logos/Core/Theorem.lean"}
   )
   
   diagnostics = result["result"]["diagnostics"]
   errors = [d for d in diagnostics if d["severity"] == 1]
   
   if errors:
     print(f"Found {len(errors)} errors:")
     for error in errors:
       print(f"  Line {error['range']['start']['line']}: {error['message']}")
   ```
   
   ### Example 2: Get Proof Goal
   
   ```python
   result = invoke_mcp_tool(
     server="lean-lsp",
     tool="lean_goal",
     arguments={
       "file_path": "Logos/Core/Theorem.lean",
       "line": 45,
       "column": 10
     }
   )
   
   goal_state = result["result"]
   print(f"Goals: {goal_state['goals']}")
   print(f"Hypotheses: {goal_state['hypotheses']}")
   ```
   ```

#### Requirement 4: Testing Infrastructure

**Need**: Test suite for MCP tool invocation

**Tests Required**:
1. Test MCP client initialization
2. Test tool invocation (mocked)
3. Test error handling
4. Test timeout handling
5. Test graceful degradation
6. Integration test with real lean-lsp-mcp server

**Test File**: `.opencode/tool/mcp/test_client.py`

---

### 7. Comparison with Loogle Integration

#### Loogle CLI Integration (lean-research-agent)

**Status**: [PASS] Well-documented and implemented

**Approach**: Direct subprocess management
- Binary path: `/home/benjamin/.cache/loogle/.lake/build/bin/loogle`
- Mode: Interactive with JSON output
- Communication: stdin/stdout
- Lifecycle: Start → Query → Parse → Close

**Strengths**:
- Detailed implementation guide
- Error handling specified
- Graceful degradation defined
- Fallback to web search

**Code Example**:
```python
class LoogleClient:
  def start(self, timeout=180):
    cmd = [self.binary_path, "--json", "--interactive"]
    self.process = subprocess.Popen(
      cmd,
      stdin=subprocess.PIPE,
      stdout=subprocess.PIPE,
      stderr=subprocess.PIPE,
      text=True,
      bufsize=1
    )
    # Wait for "Loogle is ready.\n"
  
  def query(self, query_string, timeout=10):
    self.process.stdin.write(query_string + "\n")
    self.process.stdin.flush()
    response_line = self.process.stdout.readline()
    return json.loads(response_line)
```

#### lean-lsp-mcp Integration (lean-implementation-agent)

**Status**: [FAIL] Not implemented

**Approach**: Should use MCP protocol
- Server: lean-lsp (configured in .mcp.json)
- Mode: MCP stdio transport
- Communication: MCP protocol messages
- Lifecycle: Connect → Call Tool → Parse → Disconnect

**Gaps**:
- No MCP client implementation
- No tool invocation examples
- No error handling patterns
- No graceful degradation specifics

**What's Needed**:
```python
class MCPClient:
  def connect(self, server_name):
    # Load .mcp.json
    # Get server config
    # Initialize MCP connection
    # Return client
  
  def call_tool(self, tool_name, arguments, timeout=30):
    # Send MCP tool call request
    # Wait for response
    # Parse result
    # Return formatted result
  
  def disconnect(self):
    # Close MCP connection
    # Cleanup resources
```

#### Key Differences

| Aspect | Loogle CLI | lean-lsp-mcp |
|--------|-----------|--------------|
| Protocol | Custom (JSON lines) | MCP standard |
| Transport | Direct subprocess | stdio/http/sse |
| Configuration | Hardcoded paths | .mcp.json |
| Initialization | Start process | Connect to server |
| Communication | stdin/stdout | MCP messages |
| Response Format | JSON lines | MCP tool response |
| Error Handling | Parse stderr | MCP error format |
| Lifecycle | Manual process mgmt | MCP client handles |

**Recommendation**: lean-lsp-mcp integration should follow MCP protocol patterns, not copy Loogle's subprocess approach.

---

### 8. Root Cause Analysis

#### Why lean-lsp-mcp Is Not Being Used

**Root Cause 1: No MCP Client Infrastructure**
- No MCP client library integrated
- No wrapper functions for tool invocation
- Agents have no way to call MCP tools
- **Impact**: Complete blocker for any MCP tool usage

**Root Cause 2: Agent Workflow Gaps**
- lean-implementation-agent.md has placeholder logic
- No concrete tool invocation syntax
- No iteration patterns specified
- **Impact**: Even if MCP client existed, agents wouldn't know how to use it

**Root Cause 3: Context File Inadequacy**
- mcp-tools-guide.md describes capabilities, not integration
- No agent-specific usage examples
- No invocation patterns documented
- **Impact**: Developers don't know how to integrate MCP tools

**Root Cause 4: Missing Testing**
- No tests for MCP tool invocation
- No integration tests with lean-lsp-mcp
- No validation of tool responses
- **Impact**: Can't verify integration works

**Root Cause 5: Confusion About Tool Types**
- Mixing CLI tools (Loogle) with MCP tools (lean-lsp-mcp)
- Different integration patterns needed
- No clear guidance on which approach for which tool
- **Impact**: Developers unsure how to proceed

---

### 9. Recommended Solutions

#### Solution 1: Implement MCP Client Wrapper (High Priority)

**Deliverable**: `.opencode/tool/mcp/client.py`

**Functionality**:
- Load .mcp.json configuration
- Initialize MCP client for server
- Invoke tools with arguments
- Handle timeouts and errors
- Return standardized results

**API**:
```python
def check_mcp_server_configured(server_name: str) -> bool:
  """Check if MCP server is configured in .mcp.json"""

def invoke_mcp_tool(
  server: str,
  tool: str,
  arguments: dict,
  timeout: int = 30
) -> dict:
  """Invoke MCP tool and return result"""
```

**Estimated Effort**: 4-6 hours

#### Solution 2: Update lean-implementation-agent.md (High Priority)

**Changes Required**:
1. Add concrete MCP tool invocation in step_4
2. Add iteration loop with error handling
3. Add tool availability check logic
4. Add graceful degradation specifics
5. Add example tool calls

**Estimated Effort**: 2-3 hours

#### Solution 3: Update mcp-tools-guide.md (Medium Priority)

**Changes Required**:
1. Add "Agent Integration" section
2. Add tool invocation examples
3. Add error handling patterns
4. Add agent-specific tool recommendations
5. Add troubleshooting guide

**Estimated Effort**: 2-3 hours

#### Solution 4: Create Integration Tests (Medium Priority)

**Deliverable**: `.opencode/tool/mcp/test_client.py`

**Tests**:
1. Test MCP client initialization
2. Test tool invocation (mocked)
3. Test error handling
4. Test timeout handling
5. Integration test with lean-lsp-mcp

**Estimated Effort**: 3-4 hours

#### Solution 5: Update lean-research-agent.md (Low Priority)

**Changes Required**:
1. Document LeanSearch/LeanExplore as future MCP tools
2. Add MCP invocation patterns for when integrated
3. Clarify difference between CLI (Loogle) and MCP tools

**Estimated Effort**: 1-2 hours

---

### 10. Implementation Roadmap

#### Phase 1: Foundation (Week 1)

**Tasks**:
1. Implement MCP client wrapper (`.opencode/tool/mcp/client.py`)
2. Create basic tests for MCP client
3. Verify integration with lean-lsp-mcp server

**Deliverables**:
- Working MCP client
- Basic test suite
- Integration verified

**Estimated Effort**: 8-10 hours

#### Phase 2: Agent Integration (Week 1-2)

**Tasks**:
1. Update lean-implementation-agent.md with concrete patterns
2. Add tool invocation examples
3. Add error handling logic
4. Test with real Lean implementation task

**Deliverables**:
- Updated agent definition
- Working tool invocation in /implement
- Verified compilation checking

**Estimated Effort**: 6-8 hours

#### Phase 3: Documentation (Week 2)

**Tasks**:
1. Update mcp-tools-guide.md with agent integration
2. Add troubleshooting guide
3. Create usage examples
4. Document best practices

**Deliverables**:
- Complete agent integration guide
- Troubleshooting documentation
- Usage examples

**Estimated Effort**: 4-6 hours

#### Phase 4: Testing & Validation (Week 2-3)

**Tasks**:
1. Create comprehensive test suite
2. Test with multiple Lean tasks
3. Validate error handling
4. Measure performance impact

**Deliverables**:
- Complete test coverage
- Performance benchmarks
- Validation report

**Estimated Effort**: 6-8 hours

**Total Estimated Effort**: 24-32 hours (3-4 days)

---

### 11. Risk Assessment

#### Risk 1: MCP Protocol Complexity

**Risk**: MCP protocol may be more complex than expected
**Likelihood**: Medium
**Impact**: High (could delay implementation)
**Mitigation**: 
- Start with simple tool invocation
- Use existing MCP client libraries
- Test incrementally

#### Risk 2: lean-lsp-mcp Server Issues

**Risk**: lean-lsp-mcp server may have bugs or limitations
**Likelihood**: Low
**Impact**: Medium (could require workarounds)
**Mitigation**:
- Test thoroughly with real server
- Have fallback to direct lake build
- Report issues to maintainer

#### Risk 3: Performance Impact

**Risk**: MCP tool invocation may slow down implementation
**Likelihood**: Medium
**Impact**: Low (acceptable tradeoff for verification)
**Mitigation**:
- Measure performance impact
- Add timeout controls
- Make tool usage optional

#### Risk 4: Integration Complexity

**Risk**: Integrating MCP client into agent workflow may be complex
**Likelihood**: Low
**Impact**: Medium (could require refactoring)
**Mitigation**:
- Design clean API
- Keep integration minimal
- Test thoroughly

---

### 12. Success Criteria

#### Criterion 1: Tool Invocation Works

**Measure**: Agent successfully calls lean_diagnostic_messages
**Verification**: Run /implement on Lean task, verify MCP tool called
**Target**: 100% success rate

#### Criterion 2: Compilation Checking Functional

**Measure**: Agent detects and reports Lean compilation errors
**Verification**: Introduce intentional error, verify detection
**Target**: All errors detected

#### Criterion 3: Graceful Degradation

**Measure**: Agent handles MCP unavailability gracefully
**Verification**: Disable MCP server, verify fallback works
**Target**: No crashes, clear warning message

#### Criterion 4: Performance Acceptable

**Measure**: MCP tool invocation adds < 5s per iteration
**Verification**: Benchmark with/without MCP
**Target**: < 5s overhead

#### Criterion 5: Documentation Complete

**Measure**: Developers can integrate MCP tools using docs
**Verification**: New developer follows docs successfully
**Target**: 100% success rate

---

## References

### Documentation
- [lean-lsp-mcp PyPI](https://pypi.org/project/lean-lsp-mcp/)
- [lean-lsp-mcp GitHub](https://github.com/oOo0oOo/lean-lsp-mcp)
- [Model Context Protocol](https://modelcontextprotocol.io/)
- [Lean 4 LSP](https://github.com/leanprover/lean4/tree/master/src/Lean/Server)

### Local Files
- `.mcp.json` - MCP server configuration
- `.opencode/context/project/lean4/tools/mcp-tools-guide.md` - Tool capabilities
- `.opencode/context/project/lean4/tools/lsp-integration.md` - LSP protocol details
- `.opencode/agent/subagents/lean-implementation-agent.md` - Implementation agent
- `.opencode/agent/subagents/lean-research-agent.md` - Research agent

### Related Tasks
- Task 197: Integrate Loogle CLI tool (completed)
- Task 210: Fix Lean subagents (related)
- Task 211: Standardize command lifecycle (related)

---

## Appendices

### Appendix A: lean-lsp-mcp Tool Reference

**File Interaction Tools**:
- `lean_file_outline` - Get file structure
- `lean_diagnostic_messages` - Get diagnostics
- `lean_goal` - Get proof goal
- `lean_term_goal` - Get term goal
- `lean_hover_info` - Get hover documentation
- `lean_declaration_file` - Find declaration
- `lean_completions` - Get completions
- `lean_run_code` - Run code snippet
- `lean_multi_attempt` - Try multiple attempts

**Search Tools**:
- `lean_local_search` - Local search (requires ripgrep)
- `lean_leansearch` - Natural language search
- `lean_loogle` - Type-based search
- `lean_leanfinder` - Semantic search
- `lean_state_search` - Premise search
- `lean_hammer_premise` - Hammer premise search

**Project Tools**:
- `lean_build` - Rebuild project

### Appendix B: MCP Configuration Examples

**Basic Configuration** (current):
```json
{
  "mcpServers": {
    "lean-lsp": {
      "type": "stdio",
      "command": "uvx",
      "args": ["lean-lsp-mcp"],
      "env": {
        "LEAN_LOG_LEVEL": "WARNING",
        "LEAN_PROJECT_PATH": "/home/benjamin/Documents/Philosophy/Projects/ProofChecker"
      }
    }
  }
}
```

**Advanced Configuration** (with local loogle):
```json
{
  "mcpServers": {
    "lean-lsp": {
      "type": "stdio",
      "command": "uvx",
      "args": ["lean-lsp-mcp", "--loogle-local"],
      "env": {
        "LEAN_LOG_LEVEL": "ERROR",
        "LEAN_PROJECT_PATH": "/home/benjamin/Documents/Philosophy/Projects/ProofChecker",
        "LEAN_LOOGLE_LOCAL": "true",
        "LEAN_LOOGLE_CACHE_DIR": "~/.cache/lean-lsp-mcp/loogle"
      }
    }
  }
}
```

### Appendix C: Error Codes

**MCP Client Errors**:
- `MCP_SERVER_NOT_CONFIGURED` - Server not in .mcp.json
- `MCP_CONNECTION_FAILED` - Failed to connect to server
- `MCP_TOOL_NOT_FOUND` - Tool not available on server
- `MCP_TIMEOUT` - Tool invocation timed out
- `MCP_INVALID_ARGUMENTS` - Invalid tool arguments
- `MCP_SERVER_ERROR` - Server returned error

**lean-lsp-mcp Errors**:
- `LSP_SERVER_NOT_RUNNING` - Lean LSP server not started
- `LSP_FILE_NOT_FOUND` - Lean file not found
- `LSP_PARSE_ERROR` - Failed to parse Lean file
- `LSP_BUILD_FAILED` - Lake build failed

---

## Conclusion

lean-lsp-mcp is a powerful tool that is **configured but completely unused** in the current system. The primary blocker is the **lack of MCP client infrastructure** to invoke tools from agents. Secondary issues include **incomplete agent workflow definitions** and **inadequate context documentation**.

Implementing the recommended solutions will enable:
1. Real-time compilation checking during Lean implementation
2. Proof state inspection for debugging
3. Error detection before committing code
4. Faster iteration cycles for Lean development

The estimated effort is **24-32 hours** (3-4 days) to fully integrate lean-lsp-mcp into the Lean implementation workflow.

**Next Steps**:
1. Implement MCP client wrapper (Phase 1)
2. Update lean-implementation-agent.md (Phase 2)
3. Update documentation (Phase 3)
4. Create test suite (Phase 4)
