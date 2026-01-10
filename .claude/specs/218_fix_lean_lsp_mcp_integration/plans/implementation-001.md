# Implementation Plan: Fix lean-lsp-mcp Integration and opencode Module Import Errors

- **Task**: 218 - Fix lean-lsp-mcp integration and opencode module import errors
- **Status**: [NOT STARTED]
- **Effort**: 0.75 hours (45 minutes)
- **Priority**: High
- **Dependencies**: 212 (completed)
- **Research Inputs**: 
  - Main Report: .opencode/specs/218_fix_lean_lsp_mcp_integration/reports/research-001.md
  - Summary: .opencode/specs/218_fix_lean_lsp_mcp_integration/summaries/research-summary.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**:
  - .opencode/context/core/standards/plan.md
  - .opencode/context/core/standards/status-markers.md
  - .opencode/context/core/system/artifact-management.md
  - .opencode/context/core/standards/tasks.md
- **Language**: python
- **Lean Intent**: false

## Overview

The `.opencode` directory lacks `__init__.py` files in parent directories, preventing Python from recognizing it as a package. This causes `ModuleNotFoundError: No module named 'opencode'` when lean-implementation-agent attempts to import the MCP client wrapper created in task 212. The fix requires creating 2 empty `__init__.py` files and configuring PYTHONPATH in the agent execution environment. This is a minimal, low-risk change that enables lean-lsp-mcp integration for Lean proof verification.

## Goals & Non-Goals

**Goals**:
- Create missing `__init__.py` files to establish proper Python package structure
- Configure PYTHONPATH in agent execution environment to include project root
- Verify imports work correctly with PYTHONPATH configuration
- Test MCP client availability check in simulated agent context
- Document PYTHONPATH setup requirements for future reference

**Non-Goals**:
- Complete MCP protocol integration (invoke_mcp_tool implementation remains placeholder)
- Modify MCP client wrapper code (task 212 implementation is correct)
- Change import paths in agent specifications (current paths are correct)
- Create setup.py or install as editable package (overkill for this use case)

## Risks & Mitigations

- **Risk**: PYTHONPATH configuration may not persist across agent executions
  - **Mitigation**: Document configuration in multiple locations (mcp-tools-guide.md, lean-implementation-agent.md). Test with actual /implement command to verify persistence.

- **Risk**: Nix environment may override PYTHONPATH settings
  - **Mitigation**: Test PYTHONPATH configuration in Nix environment. If issues arise, fall back to sys.path modification in agent wrapper (Solution 2 from research).

- **Risk**: Empty `__init__.py` files may be accidentally deleted
  - **Mitigation**: Add comment in each file explaining purpose. Include in git commit with clear commit message.

- **Risk**: Agent orchestrator may not support PYTHONPATH configuration
  - **Mitigation**: Research orchestrator implementation if PYTHONPATH approach fails. Prepare fallback to agent wrapper solution (2-3 hours additional effort).

## Implementation Phases

### Phase 1: Create Python Package Structure [NOT STARTED]

- **Goal**: Add missing `__init__.py` files to make `.opencode` a valid Python package
- **Tasks**:
  - [ ] Create `.opencode/__init__.py` with explanatory comment
  - [ ] Create `.opencode/tool/__init__.py` with explanatory comment
  - [ ] Verify `.opencode/tool/mcp/__init__.py` exists (should already exist from task 212)
  - [ ] Test import with PYTHONPATH set: `PYTHONPATH=/home/benjamin/Projects/ProofChecker python3 -c "from opencode.tool.mcp.client import check_mcp_server_configured; print('SUCCESS')"`
  - [ ] Verify all MCP client functions are importable
- **Timing**: 15 minutes
- **Acceptance Criteria**:
  - Both `__init__.py` files created with explanatory comments
  - Import test succeeds with PYTHONPATH configuration
  - No ModuleNotFoundError when importing from opencode.tool.mcp.client

### Phase 2: Configure PYTHONPATH and Verify Integration [NOT STARTED]

- **Goal**: Configure PYTHONPATH in agent execution environment and verify MCP client integration
- **Tasks**:
  - [ ] Research how agents are executed (orchestrator implementation)
  - [ ] Identify where to set PYTHONPATH (environment variable, shell script, service file, or subprocess spawn)
  - [ ] Configure PYTHONPATH to include `/home/benjamin/Projects/ProofChecker`
  - [ ] Test MCP client functions with PYTHONPATH: check_mcp_server_configured('lean-lsp')
  - [ ] Test get_mcp_server_config('lean-lsp') returns correct configuration
  - [ ] Simulate agent execution pattern from lean-implementation-agent.md
  - [ ] Verify graceful degradation when invoke_mcp_tool returns "not yet implemented"
- **Timing**: 15 minutes
- **Acceptance Criteria**:
  - PYTHONPATH configured in agent execution environment
  - MCP server availability check returns True for 'lean-lsp'
  - Server config retrieval works correctly
  - Simulated agent code executes without import errors
  - Graceful degradation to lake build works when MCP protocol unavailable

### Phase 3: Testing and Documentation [NOT STARTED]

- **Goal**: Verify fix with real Lean task and update documentation
- **Tasks**:
  - [ ] Run /implement on a simple Lean task to test end-to-end integration
  - [ ] Verify no ModuleNotFoundError in agent output
  - [ ] Verify MCP availability check succeeds
  - [ ] Verify agent falls back to lake build (since invoke_mcp_tool is placeholder)
  - [ ] Update mcp-tools-guide.md with __init__.py requirement
  - [ ] Update mcp-tools-guide.md with PYTHONPATH setup instructions
  - [ ] Update lean-implementation-agent.md with verification steps
  - [ ] Document known limitation: invoke_mcp_tool returns "not yet implemented"
  - [ ] Create git commit with all changes
- **Timing**: 15 minutes
- **Acceptance Criteria**:
  - Real Lean task implementation completes without import errors
  - MCP client integration works as expected (availability check succeeds, invocation returns placeholder error)
  - Documentation updated with setup requirements
  - Git commit created with clear message
  - No regression in existing functionality

## Testing & Validation

**Unit Tests**:
- [ ] Import test: `from opencode.tool.mcp.client import check_mcp_server_configured`
- [ ] Import test: `from opencode.tool.mcp.client import invoke_mcp_tool, find_mcp_config, get_mcp_server_config`
- [ ] Function test: `check_mcp_server_configured('lean-lsp')` returns True
- [ ] Function test: `check_mcp_server_configured('nonexistent')` returns False
- [ ] Function test: `get_mcp_server_config('lean-lsp')` returns valid config dict
- [ ] Function test: `invoke_mcp_tool('lean-lsp', 'test', {})` returns "not yet implemented" error

**Integration Tests**:
- [ ] Simulated agent execution: Import MCP client, check availability, invoke tool
- [ ] Real agent execution: Run /implement on Lean task, verify no import errors
- [ ] Graceful degradation: Verify agent falls back to lake build when MCP protocol unavailable
- [ ] PYTHONPATH persistence: Verify configuration persists across multiple agent invocations

**Regression Tests**:
- [ ] Existing MCP client tests still pass: `python3 .opencode/tool/mcp/test_client.py`
- [ ] No impact on non-Lean tasks
- [ ] No impact on other .opencode tools or agents

## Artifacts & Outputs

**Created Files**:
- `.opencode/__init__.py` - Empty file with explanatory comment marking directory as Python package
- `.opencode/tool/__init__.py` - Empty file with explanatory comment marking directory as Python package

**Modified Files**:
- `.opencode/context/project/lean4/tools/mcp-tools-guide.md` - Add __init__.py requirement and PYTHONPATH setup instructions
- `.opencode/agent/subagents/lean-implementation-agent.md` - Add verification steps for MCP client import

**Documentation**:
- Updated mcp-tools-guide.md with package structure requirements
- Updated lean-implementation-agent.md with import verification steps
- Git commit message documenting fix

**No Summary Artifact**: This is an implementation task, not a research task. Changes are minimal and self-documenting.

## Rollback/Contingency

**If PYTHONPATH configuration fails**:
1. Remove PYTHONPATH configuration
2. Implement Solution 2 from research: Agent execution wrapper with sys.path modification
3. Create `.opencode/tool/agent_wrapper.py` with sys.path setup
4. Update orchestrator to use wrapper when executing Python code
5. Estimated additional effort: 2-3 hours

**If __init__.py files cause issues**:
1. Remove `.opencode/__init__.py` and `.opencode/tool/__init__.py`
2. Revert to sys.path workaround pattern from test_client.py
3. Update lean-implementation-agent.md to use sys.path.insert() before imports
4. Estimated additional effort: 1 hour

**If Nix environment conflicts**:
1. Investigate Nix Python environment configuration
2. Consider using nix-shell with custom PYTHONPATH
3. Document Nix-specific setup requirements
4. Estimated additional effort: 1-2 hours

**Complete Rollback**:
- Remove 2 `__init__.py` files
- Remove PYTHONPATH configuration
- Revert documentation changes
- Document as known limitation: MCP client import requires manual sys.path setup
- Estimated rollback time: 5 minutes

## Research Integration

**Key Research Findings Applied**:

1. **Root Cause Identified**: Missing `__init__.py` files in `.opencode/` and `.opencode/tool/` directories prevent Python package recognition (research report lines 24-48)

2. **MCP Client Status Confirmed**: Task 212 implementation is correct and fully tested. Import failure is environmental, not a code issue (research report lines 122-196)

3. **Solution Selected**: Solution 1 (minimal fix) - Create 2 empty `__init__.py` files + configure PYTHONPATH. Lowest risk, fastest implementation, standard Python practice (research report lines 460-484)

4. **Verification Approach**: 4-phase verification plan from research (lines 649-760) ensures thorough testing from package structure to end-to-end agent integration

5. **Fallback Options**: Research identified 3 alternative solutions if primary approach fails, with effort estimates and risk assessments (research report lines 486-609)

**Research Artifacts Referenced**:
- Main Report: `.opencode/specs/218_fix_lean_lsp_mcp_integration/reports/research-001.md` (897 lines)
- Summary: `.opencode/specs/218_fix_lean_lsp_mcp_integration/summaries/research-summary.md` (126 lines)

**Implementation Confidence**: High (95%+)
- Research thoroughly analyzed root cause with concrete evidence
- Solution is minimal, standard Python practice
- Multiple fallback options documented if primary approach fails
- MCP client infrastructure confirmed working via test suite
