# Implementation Plan: Task 214 (Revision 002)

**Project Number**: 214  
**Type**: Enhancement  
**Priority**: High  
**Language**: markdown  
**Created**: 2025-12-28  
**Revised**: 2025-12-28  
**Estimated Hours**: 1.5  
**Phases**: 2

---

## Revision Notes

**Version**: 002  
**Previous Plan**: implementation-001.md  
**Revision Reason**: Remove AGENTS.md documentation work - research already concluded AGENTS.md approach does NOT work  
**Changes**:
- Removed AGENTS.md documentation section from Phase 2 (saved 15 minutes)
- Reduced total effort from 2.25 hours to 1.5 hours
- Kept 2-phase structure: Phase 1 (FIX removal) and Phase 2 (XML styling)
- Focus purely on: (a) Removing historical comparisons, (b) Applying XML styling

---

## Overview

Complete two related improvements to orchestrator.md: (1) Address FIX comment on line 14 by removing historical comparisons and describing current system capabilities directly, (2) Apply XML styling consistent with error-diagnostics-agent.md for better maintainability.

**Research Integrated**: Task 214 research findings confirm:
- FIX comment requests rewriting "Key Improvements Over v1" and "Problems Solved" sections to describe current capabilities without historical references
- All subagents use consistent XML tags (<context>, <role>, <task>, <process_flow>, <constraints>, <output_specification>, <validation_checks>, <principles>)
- CRITICAL: AGENTS.md is for custom instructions/rules, NOT agent definitions - renaming orchestrator.md to AGENTS.md would break the orchestrator (documented in research, no implementation needed)
- XML styling is backward compatible with existing command workflows
- Total implementation: 1.5 hours (30 min rewrite + 1.25 hours XML styling)

---

## Phase 1: Remove Historical Comparisons (30 minutes)

**Goal**: Address FIX comment by rewriting sections to describe current system without v1 references

**Tasks**:

1. **Rewrite "Key Improvements Over v1" section (15 minutes)**
   - Remove section header "Key Improvements Over v1"
   - Create new section header "Core Capabilities"
   - Rewrite bullet points as direct capability statements:
     - OLD: "Delegation registry for active tracking"
     - NEW: "Maintains delegation registry for active tracking of all subagent invocations"
     - OLD: "Cycle detection (max depth 3)"
     - NEW: "Prevents infinite loops through cycle detection with maximum delegation depth of 3"
     - OLD: "Session ID tracking"
     - NEW: "Tracks all delegations with unique session IDs for debugging and monitoring"
     - OLD: "Language-based routing"
     - NEW: "Routes tasks to appropriate agents based on language field (lean, markdown, python, general)"
     - OLD: "Timeout enforcement"
     - NEW: "Enforces timeouts on all delegations to prevent indefinite hangs"
     - OLD: "Standardized return validation"
     - NEW: "Validates all subagent returns against standardized format"

2. **Rewrite "Problems Solved (Task 191)" section (15 minutes)**
   - Remove section header "Problems Solved (Task 191)"
   - Create new section header "Delegation Safety Features"
   - Rewrite bullet points as feature descriptions:
     - OLD: "Root Cause #1: Missing return paths (explicit receive/validate stages)"
     - NEW: "Explicit receive and validate stages ensure all subagent returns are captured and validated"
     - OLD: "Root Cause #2: Infinite loops (cycle detection)"
     - NEW: "Cycle detection prevents infinite delegation loops by checking delegation path before routing"
     - OLD: "Root Cause #3: Async/sync mismatch (timeout handling)"
     - NEW: "Timeout handling with graceful degradation returns partial results when operations exceed time limits"
     - OLD: "Root Cause #4: Missing error handling (comprehensive error handling)"
     - NEW: "Comprehensive error handling logs all failures to errors.json with recovery recommendations"
     - OLD: "Root Cause #5: Coordination gaps (delegation registry)"
     - NEW: "Delegation registry provides central coordination for all active subagent invocations"

**Acceptance Criteria**:
- [ ] "Key Improvements Over v1" section removed
- [ ] "Core Capabilities" section added with 6 capability statements
- [ ] "Problems Solved (Task 191)" section removed
- [ ] "Delegation Safety Features" section added with 5 feature descriptions
- [ ] No mentions of "v1", "improvements over", "root cause", "Task 191" in new sections
- [ ] All capability statements describe current system directly
- [ ] File remains valid markdown and compiles successfully

**Validation**:
- Read new sections to verify no historical comparisons
- Grep for "v1", "improvements over", "root cause" patterns
- Verify all 11 capabilities from old sections preserved in new format

---

## Phase 2: Apply XML Styling (1.25 hours)

**Goal**: Restructure orchestrator.md with XML tags matching error-diagnostics-agent.md pattern

**Tasks**:

1. **Add XML front matter (15 minutes)**
   - Add YAML front matter section at top:
     ```yaml
     ---
     description: "Central coordination with delegation safety and language-based routing"
     mode: orchestrator
     temperature: 0.3
     ---
     ```
   - Keep existing header: # Orchestrator Agent
   - Keep existing metadata: Version, Type, Purpose, Created

2. **Restructure Overview section with <context> tag (15 minutes)**
   - Wrap "Overview" content in <context> tag:
     ```xml
     <context>
       <system_domain>Central coordination for .opencode system</system_domain>
       <coordination_scope>User request routing, subagent delegation, safety enforcement</coordination_scope>
       <safety_features>Session tracking, cycle detection, timeout enforcement, return validation</safety_features>
     </context>
     ```
   - Move "Core Capabilities" (from Phase 1) into <context> as capabilities list
   - Move "Delegation Safety Features" (from Phase 1) into <context> as safety_features

3. **Add <role> tag (5 minutes)**
   - After <context>, add:
     ```xml
     <role>
       Primary coordination agent routing user requests to appropriate subagents with delegation safety
     </role>
     ```

4. **Add <task> tag (5 minutes)**
   - After <role>, add:
     ```xml
     <task>
       Receive user requests, analyze complexity, route to appropriate agents, monitor delegations, validate returns
     </task>
     ```

5. **Restructure Context Loading section (10 minutes)**
   - Keep "Context Loading" header
   - Wrap context levels in <context_allocation> tag:
     ```xml
     <context_allocation>
       <level_1>
         <coverage>80% of requests</coverage>
         <scope>Common standards (return format, status markers), common workflows (delegation guide)</scope>
       </level_1>
       <level_2>
         <coverage>20% of requests</coverage>
         <scope>Level 1 + Project-specific context based on language (lean: project/lean4/, markdown: project/repo/)</scope>
       </level_2>
       <level_3>
         <coverage>Rare, complex requests</coverage>
         <scope>All context loaded</scope>
       </level_3>
     </context_allocation>
     ```

6. **Restructure Delegation Registry section (10 minutes)**
   - Keep "Delegation Registry" header
   - Wrap content in <delegation_registry> tag:
     ```xml
     <delegation_registry>
       <description>In-memory registry tracking all active delegations</description>
       <entry_schema>
         <!-- Existing registry schema -->
       </entry_schema>
       <operations>
         <operation>Register: On delegation start</operation>
         <operation>Monitor: Periodic timeout checks</operation>
         <operation>Update: On status changes</operation>
         <operation>Complete: On delegation completion</operation>
         <operation>Cleanup: On timeout or error</operation>
       </operations>
     </delegation_registry>
     ```

7. **Restructure Workflow Stages section with <process_flow> (30 minutes)**
   - Replace "Workflow Stages" header with <process_flow> tag
   - Restructure each stage (1-13) with <step_N> pattern:
     ```xml
     <process_flow>
       <step_1 name="AnalyzeRequest">
         <action>Parse and understand the user request</action>
         <process>
           1. Extract command type (task, research, plan, implement, etc.)
           2. Load command file from .opencode/command/{command}.md
           ... (existing process steps)
         </process>
         <validation>Command loaded and ready for execution</validation>
         <output>Command loaded with validated arguments</output>
       </step_1>
       
       <step_2 name="DetermineComplexity">
         <action>Assess request complexity for context allocation</action>
         <process>
           ... (existing process)
         </process>
         <output>Complexity level and context level</output>
       </step_2>
       
       ... (continue for all 13 stages)
     </process_flow>
     ```

8. **Restructure Helper Functions section (10 minutes)**
   - Wrap in <helper_functions> tag:
     ```xml
     <helper_functions>
       <function name="generate_session_id">
         <description>Generate unique session ID for delegation tracking</description>
         <implementation>
           <!-- Existing code block -->
         </implementation>
       </function>
       
       <function name="determine_timeout">
         <description>Determine timeout based on command type</description>
         <implementation>
           <!-- Existing code block -->
         </implementation>
       </function>
       
       <function name="log_error">
         <description>Log error to errors.json with metadata</description>
         <implementation>
           <!-- Existing code block -->
         </implementation>
       </function>
     </helper_functions>
     ```

9. **Restructure Error Handling section (10 minutes)**
   - Wrap in <error_handling> tag:
     ```xml
     <error_handling>
       <scenario name="delegation_cycle">
         <description>Cycle detected in delegation path</description>
         <handler>
           <!-- Existing code block -->
         </handler>
       </scenario>
       
       <scenario name="max_depth_exceeded">
         <description>Delegation depth exceeds maximum (3)</description>
         <handler>
           <!-- Existing code block -->
         </handler>
       </scenario>
       
       ... (continue for timeout, validation_failure)
     </error_handling>
     ```

10. **Restructure Testing section (10 minutes)**
    - Wrap in <validation_checks> tag:
      ```xml
      <validation_checks>
        <test name="simple_delegation">
          <description>Test simple command routing to subagent</description>
          <scenario>/task "Create test task"</scenario>
          <expected>Routes to atomic-task-numberer, returns task number</expected>
        </test>
        
        <test name="language_routing">
          <description>Test Lean task routes to lean-research-agent</description>
          <scenario>/research 195 (task with Language: lean)</scenario>
          <expected>Routes to lean-research-agent, not general researcher</expected>
        </test>
        
        ... (continue for all 5 tests)
      </validation_checks>
      ```

11. **Update Related Documentation section (5 minutes)**
    - Keep "Related Documentation" header
    - Wrap links in <references> tag:
      ```xml
      <references>
        <reference type="workflow">Delegation Guide: .opencode/context/core/workflows/subagent-delegation-guide.md</reference>
        <reference type="standard">Return Format: .opencode/context/core/standards/subagent-return-format.md</reference>
        <reference type="system">Status Markers: .opencode/context/core/standards/status-markers.md</reference>
        <reference type="research">Task 191 Research: .opencode/specs/191_fix_subagent_delegation_hang/reports/research-001.md</reference>
      </references>
      ```

**Acceptance Criteria**:
- [ ] YAML front matter added at top
- [ ] <context> tag wraps overview with system_domain, coordination_scope, safety_features
- [ ] <role> tag added describing orchestrator role
- [ ] <task> tag added describing orchestrator task
- [ ] <context_allocation> tag wraps context loading levels
- [ ] <delegation_registry> tag wraps registry documentation
- [ ] <process_flow> tag with <step_1> through <step_13> wraps all workflow stages
- [ ] <helper_functions> tag wraps all 3 helper function definitions
- [ ] <error_handling> tag wraps all 4 error scenarios
- [ ] <validation_checks> tag wraps all 5 test cases
- [ ] <references> tag wraps Related Documentation links
- [ ] File remains valid markdown
- [ ] All existing content preserved (only structure changes)
- [ ] XML tags match error-diagnostics-agent.md pattern

**Validation**:
- Read entire file to verify XML structure is correct
- Check all XML tags are properly opened and closed
- Verify no content was lost during restructuring
- Test that orchestrator still works with existing command workflows
- Confirm backward compatibility (commands still load orchestrator.md correctly)

---

## Success Criteria

**Phase 1 Complete**:
1. FIX comment on line 14 addressed - all historical comparisons removed
2. "Core Capabilities" section describes current system features directly
3. "Delegation Safety Features" section describes current safety mechanisms directly
4. No mentions of "v1", "improvements over", "root cause", or "Task 191" in rewritten sections
5. All 11 capabilities from old sections preserved in new format

**Phase 2 Complete**:
1. orchestrator.md uses XML styling consistent with error-diagnostics-agent.md
2. All 10 XML tags applied: <context>, <role>, <task>, <context_allocation>, <delegation_registry>, <process_flow>, <step_N>, <helper_functions>, <error_handling>, <validation_checks>, <references>
3. Backward compatibility maintained - orchestrator works with existing commands
4. File structure improved for maintainability

**Overall Acceptance Criteria Met**:
- [x] Research completed on AGENTS.md approach (research phase confirmed - does NOT work)
- [ ] FIX comment on line 14 addressed - removed historical comparisons to v1
- [ ] "Key Improvements Over v1" section rewritten as "Core Capabilities" describing current features
- [ ] "Problems Solved (Task 191)" section rewritten as "Delegation Safety Features" describing current safeguards
- [ ] No mentions of "v1", "improvements over", or historical comparisons throughout file
- [ ] Entire orchestrator.md restructured with XML styling matching error-diagnostics-agent.md pattern
- [ ] XML tags used: <context>, <role>, <task>, <process_flow>, <step_N>, <validation_checks>, <references>, and others
- [ ] All changes maintain backward compatibility with existing command workflows
- [ ] orchestrator.md remains fully functional after XML styling conversion

---

## Risk Assessment

**Low Risk**:
- Phase 1 (rewriting sections): Low risk - only content changes, no structural impact
- XML styling: Low risk - backward compatible, purely structural

**Mitigation**:
- Test orchestrator after each phase to verify functionality
- Keep backup of original file before changes
- Validate XML structure before committing
- Verify no commands break after changes

---

## Dependencies

**None**: This task is self-contained

**Blocks**: None (improvement task)

---

## Testing Plan

**Phase 1 Testing**:
1. Read rewritten sections to verify clarity and completeness
2. Grep for "v1", "improvements over", "root cause" to confirm removal
3. Verify all 11 capabilities preserved in new format

**Phase 2 Testing**:
1. Validate XML structure (all tags opened and closed correctly)
2. Test orchestrator with sample commands:
   - /research 195 (Lean task - should route to lean-research-agent)
   - /implement 192 (Lean task with plan - should route to lean-implementation-agent)
   - /plan 214 (markdown task - should route to planner)
3. Verify no functionality regression
4. Check backward compatibility with all commands

**Manual Testing**:
- Run /research, /plan, /implement commands to verify orchestrator still works
- Check console output for correct routing decisions
- Verify no errors or warnings introduced

---

## Implementation Notes

**Phase 1 Priority**: Address FIX comment first - quick win (30 minutes)

**Phase 2 Approach**: Systematic XML conversion following error-diagnostics-agent.md pattern

**AGENTS.md Research**: Already documented in research findings - no implementation needed. Research confirmed AGENTS.md is for custom instructions, NOT agent definitions. Renaming orchestrator.md to AGENTS.md would break the orchestrator.

**Backward Compatibility**: All XML changes are structural only - no functional changes

**Validation**: Test after each phase, not just at end

---

## Related Documentation

- Research Report: `.opencode/specs/214_orchestrator_improvements/reports/research-001.md`
- Research Summary: `.opencode/specs/214_orchestrator_improvements/summaries/research-summary.md`
- Reference Agent (XML pattern): `.opencode/agent/subagents/error-diagnostics-agent.md`
- Orchestrator (current): `.opencode/agent/orchestrator.md`

---

## Effort Breakdown

| Phase | Task | Estimated Time |
|-------|------|----------------|
| 1 | Rewrite "Key Improvements Over v1" section | 15 minutes |
| 1 | Rewrite "Problems Solved (Task 191)" section | 15 minutes |
| **Phase 1 Total** | **Remove Historical Comparisons** | **30 minutes** |
| 2 | Add XML front matter | 15 minutes |
| 2 | Restructure Overview with <context> | 15 minutes |
| 2 | Add <role> and <task> tags | 10 minutes |
| 2 | Restructure Context Loading with <context_allocation> | 10 minutes |
| 2 | Restructure Delegation Registry | 10 minutes |
| 2 | Restructure Workflow Stages with <process_flow> | 30 minutes |
| 2 | Restructure Helper Functions | 10 minutes |
| 2 | Restructure Error Handling | 10 minutes |
| 2 | Restructure Testing with <validation_checks> | 10 minutes |
| 2 | Update Related Documentation with <references> | 5 minutes |
| **Phase 2 Total** | **Apply XML Styling** | **1.25 hours** |
| **Total** | **All Phases** | **1.5 hours** |

---

## Completion Checklist

- [ ] Phase 1: Historical comparisons removed
- [ ] Phase 1: "Core Capabilities" section created
- [ ] Phase 1: "Delegation Safety Features" section created
- [ ] Phase 1: All v1 references removed
- [ ] Phase 1: File validated and tested
- [ ] Phase 2: XML front matter added
- [ ] Phase 2: All 10 XML tags applied
- [ ] Phase 2: Backward compatibility verified
- [ ] Phase 2: File validated and tested
- [ ] Final: All acceptance criteria met
- [ ] Final: orchestrator.md committed to repository
- [ ] Final: Task 214 marked [COMPLETED]
