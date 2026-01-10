# Implementation Plan: Improve lean-lsp-mcp Usage in Lean Implementation Agent

- **Task**: 212 - Research and improve lean-lsp-mcp usage in Lean implementation agent
- **Status**: [COMPLETED]
- **Effort**: 14 hours
- **Priority**: High
- **Dependencies**: None
- **Research Inputs**: 
  - Main Report: .opencode/specs/212_research_lean_lsp_mcp_usage/reports/research-001.md
  - Summary: .opencode/specs/212_research_lean_lsp_mcp_usage/summaries/research-summary.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/tasks.md
- **Language**: markdown
- **Lean Intent**: false

## Overview

Research identified that lean-lsp-mcp is properly configured in .mcp.json but completely unused due to missing MCP client infrastructure. This plan implements the MCP client wrapper, updates lean-implementation-agent.md with concrete tool invocation patterns, improves context documentation, and creates integration tests. The goal is to enable real-time Lean compilation checking and proof state inspection during implementation tasks.

## Goals & Non-Goals

**Goals**:
- Implement MCP client wrapper for invoking lean-lsp-mcp tools from agents
- Update lean-implementation-agent.md with concrete MCP tool invocation patterns
- Add iteration loop with error handling for compilation checking
- Update mcp-tools-guide.md with agent integration examples
- Create integration tests for MCP tool invocation
- Enable real-time compilation checking during /implement for Lean tasks

**Non-Goals**:
- Implementing all 15+ lean-lsp-mcp tools (focus on diagnostic checking and goal inspection)
- Replacing Loogle CLI integration (different tool type, already working)
- Integrating LeanSearch/LeanExplore (future work, marked NOT YET INTEGRATED)
- Modifying .mcp.json configuration (already correct)
- Creating new MCP servers (lean-lsp-mcp already exists)

## Risks & Mitigations

**Risk 1: MCP Protocol Complexity**
- **Likelihood**: Medium
- **Impact**: High (could delay implementation)
- **Mitigation**: Start with simple tool invocation, use existing MCP client libraries, test incrementally

**Risk 2: lean-lsp-mcp Server Issues**
- **Likelihood**: Low
- **Impact**: Medium (could require workarounds)
- **Mitigation**: Test thoroughly with real server, have fallback to direct lake build, report issues to maintainer

**Risk 3: Performance Impact**
- **Likelihood**: Medium
- **Impact**: Low (acceptable tradeoff for verification)
- **Mitigation**: Measure performance impact, add timeout controls, make tool usage optional

**Risk 4: Integration Complexity**
- **Likelihood**: Low
- **Impact**: Medium (could require refactoring)
- **Mitigation**: Design clean API, keep integration minimal, test thoroughly

## Implementation Phases

### Phase 1: Implement MCP Client Wrapper [COMPLETED]

- **Goal**: Create reusable MCP client infrastructure for invoking lean-lsp-mcp tools
- **Tasks**:
  - [ ] Create .opencode/tool/mcp/ directory structure
  - [ ] Implement check_mcp_server_configured() function to validate .mcp.json
  - [ ] Implement invoke_mcp_tool() function with MCP protocol support
  - [ ] Add timeout handling (default 30s)
  - [ ] Add error handling for connection failures, tool not found, invalid arguments
  - [ ] Add graceful degradation when MCP server unavailable
  - [ ] Return standardized result format: {success, result, error}
  - [ ] Test with lean_diagnostic_messages tool on sample Lean file
- **Timing**: 4 hours
- **Acceptance Criteria**:
  - MCP client can connect to lean-lsp server from .mcp.json
  - invoke_mcp_tool successfully calls lean_diagnostic_messages
  - Errors are handled gracefully with clear error messages
  - Timeout prevents hanging on unresponsive server

### Phase 2: Update lean-implementation-agent.md [COMPLETED]

- **Goal**: Add concrete MCP tool invocation patterns to lean-implementation-agent workflow
- **Tasks**:
  - [ ] Add MCP client import to step_4 process
  - [ ] Replace placeholder "Send Lean files for compilation" with concrete invoke_mcp_tool call
  - [ ] Implement iteration loop (max 5 iterations) for error fixing
  - [ ] Add tool availability check using check_mcp_server_configured()
  - [ ] Add diagnostic parsing logic to extract errors from MCP response
  - [ ] Add error analysis and fix generation strategy
  - [ ] Add graceful degradation specifics (log to errors.json, return partial status)
  - [ ] Add example tool calls for lean_diagnostic_messages and lean_goal
  - [ ] Document timeout handling and retry logic
- **Timing**: 3 hours
- **Acceptance Criteria**:
  - step_4 has concrete MCP tool invocation code
  - Iteration loop is fully specified with error handling
  - Tool availability check prevents crashes when MCP unavailable
  - Graceful degradation path is clear and actionable

### Phase 3: Update mcp-tools-guide.md [COMPLETED]

- **Goal**: Add agent integration documentation to mcp-tools-guide.md
- **Tasks**:
  - [ ] Add "Agent Integration" section with overview
  - [ ] Document invoke_mcp_tool API with parameters and return format
  - [ ] Add example: Check compilation errors with lean_diagnostic_messages
  - [ ] Add example: Get proof goal with lean_goal
  - [ ] Add example: Run code snippet with lean_run_code
  - [ ] Document error handling patterns for MCP tool failures
  - [ ] Add "Available Tools by Agent" section (lean-implementation-agent vs lean-research-agent)
  - [ ] Add troubleshooting guide for common MCP issues
  - [ ] Clarify difference between CLI tools (Loogle) and MCP tools (lean-lsp-mcp)
- **Timing**: 2.5 hours
- **Acceptance Criteria**:
  - Agent integration section is clear and actionable
  - Examples show concrete tool invocation patterns
  - Troubleshooting guide covers common issues
  - Difference between CLI and MCP tools is explained

### Phase 4: Create Integration Tests [COMPLETED]

- **Goal**: Validate MCP client wrapper and agent integration with automated tests
- **Tasks**:
  - [ ] Create .opencode/tool/mcp/test_client.py
  - [ ] Test check_mcp_server_configured() with valid and invalid .mcp.json
  - [ ] Test invoke_mcp_tool() with mocked MCP server
  - [ ] Test timeout handling (mock slow server)
  - [ ] Test error handling (mock server errors, connection failures)
  - [ ] Test graceful degradation (MCP server not configured)
  - [ ] Integration test with real lean-lsp-mcp server and sample Lean file
  - [ ] Verify diagnostic parsing extracts errors correctly
  - [ ] Measure performance impact (baseline vs with MCP)
- **Timing**: 3 hours
- **Acceptance Criteria**:
  - All unit tests pass (mocked MCP server)
  - Integration test passes with real lean-lsp-mcp server
  - Timeout and error handling verified
  - Performance impact measured and acceptable (< 5s overhead)

### Phase 5: Validation and Documentation [COMPLETED]

- **Goal**: Validate end-to-end workflow and update project documentation
- **Tasks**:
  - [ ] Test /implement command on real Lean task with intentional error
  - [ ] Verify lean-implementation-agent invokes lean_diagnostic_messages
  - [ ] Verify error detection and reporting works
  - [ ] Verify graceful degradation when MCP unavailable (disable server in .mcp.json)
  - [ ] Update TODO.md task 212 status to [COMPLETED]
  - [ ] Create implementation summary artifact
  - [ ] Document lessons learned and future improvements
  - [ ] Update IMPLEMENTATION_STATUS.md if needed
- **Timing**: 1.5 hours
- **Acceptance Criteria**:
  - /implement successfully uses lean-lsp-mcp for Lean tasks
  - Errors are detected and reported correctly
  - Graceful degradation works without crashes
  - All documentation updated

## Testing & Validation

**Unit Tests**:
- [ ] check_mcp_server_configured() returns true for valid .mcp.json
- [ ] check_mcp_server_configured() returns false for missing/invalid config
- [ ] invoke_mcp_tool() successfully calls mocked MCP tool
- [ ] invoke_mcp_tool() handles timeout correctly
- [ ] invoke_mcp_tool() handles connection errors gracefully
- [ ] invoke_mcp_tool() handles invalid arguments error

**Integration Tests**:
- [ ] invoke_mcp_tool() successfully calls real lean_diagnostic_messages
- [ ] Diagnostic parsing extracts errors from MCP response
- [ ] lean-implementation-agent step_4 invokes MCP tools during /implement
- [ ] Error detection works with intentional Lean syntax error
- [ ] Graceful degradation works when MCP server disabled

**Performance Tests**:
- [ ] MCP tool invocation adds < 5s overhead per iteration
- [ ] Timeout prevents hanging on unresponsive server
- [ ] Multiple iterations complete within reasonable time

**End-to-End Validation**:
- [ ] Run /implement on Lean task with correct code - should succeed
- [ ] Run /implement on Lean task with syntax error - should detect and report
- [ ] Run /implement with MCP disabled - should fall back gracefully
- [ ] Verify compilation checking improves iteration speed

## Artifacts & Outputs

**Code Artifacts**:
- .opencode/tool/mcp/client.py (MCP client wrapper)
- .opencode/tool/mcp/test_client.py (integration tests)
- .opencode/tool/mcp/__init__.py (package init)

**Documentation Artifacts**:
- .opencode/agent/subagents/lean-implementation-agent.md (updated)
- .opencode/context/project/lean4/tools/mcp-tools-guide.md (updated)
- .opencode/specs/212_research_lean_lsp_mcp_usage/plans/implementation-001.md (this file)
- .opencode/specs/212_research_lean_lsp_mcp_usage/summaries/implementation-summary-YYYYMMDD.md

**Project Documentation**:
- TODO.md (task 212 status updated to [COMPLETED])
- Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md (if needed)

## Rollback/Contingency

**If MCP client implementation fails**:
- Revert .opencode/tool/mcp/ directory
- Revert lean-implementation-agent.md changes
- Keep research artifacts for future attempts
- Document blockers in task 212

**If integration tests fail**:
- Disable MCP tool invocation in lean-implementation-agent.md
- Keep MCP client code for manual testing
- Fall back to file write without compilation checking
- Document issues for future resolution

**If performance unacceptable**:
- Add configuration flag to disable MCP tool usage
- Make MCP tool invocation optional (opt-in)
- Optimize timeout values
- Consider async/parallel tool invocation

**Graceful Degradation Strategy**:
- All MCP tool usage is optional
- Agent falls back to file write if MCP unavailable
- Clear warnings logged when MCP not used
- Manual compilation check recommended in warnings
- No crashes or failures when MCP disabled

## Success Metrics

**Primary Metrics**:
- lean-implementation-agent successfully invokes lean_diagnostic_messages during /implement
- Compilation errors detected before file commit
- Zero crashes when MCP unavailable (graceful degradation)

**Secondary Metrics**:
- MCP tool invocation overhead < 5s per iteration
- Error detection accuracy: 100% for syntax errors
- Documentation completeness: developers can integrate MCP tools using docs

**Impact Metrics**:
- Estimated 30-50% reduction in Lean implementation iteration time
- Reduced build failures from undetected compilation errors
- Improved developer experience with real-time feedback
