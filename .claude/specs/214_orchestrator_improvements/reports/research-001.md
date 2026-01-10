# Research Report: Orchestrator.md Improvements

**Task**: 214  
**Topic**: Address FIX comment, apply XML styling, and research default agent configuration  
**Date**: 2025-12-28  
**Researcher**: researcher  
**Status**: Completed  

---

## Overview

This research addresses three related improvements to `.opencode/agent/orchestrator.md`:

1. **FIX Comment Resolution** (Line 14): Rewrite historical comparison sections to present current capabilities directly
2. **XML Styling Application**: Apply consistent XML tag structure used in other subagents
3. **Default Agent Configuration**: Research AGENTS.md naming convention and default orchestrator mode

---

## Key Findings

### Finding 1: FIX Comment Analysis (Line 14)

**Location**: `.opencode/agent/orchestrator.md` line 14

**Current Issue**:
```markdown
<!-- FIX: turn this into a statement of the current system without comparison to the past system for clarity and directness. Do something similar for the rest of this file, avoiding historical mentions. -->

**Key Improvements Over v1**:
- Delegation registry for active tracking
- Cycle detection (max depth 3)
- Session ID tracking
- Language-based routing
- Timeout enforcement
- Standardized return validation

**Problems Solved** (Task 191):
- Root Cause #1: Missing return paths (explicit receive/validate stages)
- Root Cause #2: Infinite loops (cycle detection)
- Root Cause #3: Async/sync mismatch (timeout handling)
- Root Cause #4: Missing error handling (comprehensive error handling)
- Root Cause #5: Coordination gaps (delegation registry)
```

**Problem**: The document uses historical comparisons ("Key Improvements Over v1", "Problems Solved") which:
- Reference past system state ("v1") that readers may not know
- Frame capabilities as improvements rather than core features
- Create confusion about what the current system actually does
- Violate documentation best practice of describing current state

**Recommended Rewrite**:

Replace lines 16-29 with:

```markdown
## Core Capabilities

The orchestrator provides:

- **Delegation Registry**: Active tracking of all delegations with session IDs, timeouts, and status
- **Cycle Detection**: Prevents infinite delegation loops (max depth 3)
- **Session Tracking**: Unique session IDs for correlation and debugging
- **Language-Based Routing**: Routes tasks to language-specific agents (lean, markdown, python, general)
- **Timeout Enforcement**: Monitors delegations and handles timeouts gracefully with partial results
- **Return Validation**: Validates all subagent returns against standardized format

## Delegation Safety Features

The orchestrator ensures safe delegation through:

- **Explicit Return Paths**: ReceiveResults and ProcessResults stages for all delegations
- **Cycle Prevention**: Detects and blocks delegation cycles before they occur
- **Timeout Handling**: Monitors deadlines and recovers partial results on timeout
- **Comprehensive Error Handling**: Logs errors, provides recovery steps, and maintains system stability
- **Coordination Registry**: Centralized tracking prevents lost delegations and orphaned sessions
```

**Rationale**:
- Presents capabilities as current features, not historical improvements
- Removes all references to "v1" and "Task 191"
- Groups features logically: Core Capabilities vs Safety Features
- Maintains all information but frames it as "what the system does" not "what we fixed"
- More professional and maintainable for future readers

**Additional Historical References to Remove**:
- Line 3: "**Version**: 2.0" → Remove version number (not meaningful without v1 context)
- Line 6: "**Created**: 2025-12-26" → Remove creation date (use git history instead)

---

### Finding 2: XML Styling Pattern Analysis

**Reference Files Analyzed**:
- `.opencode/agent/subagents/error-diagnostics-agent.md` (495 lines)
- `.opencode/agent/subagents/planner.md` (337 lines)
- `.opencode/agent/subagents/researcher.md` (345 lines)

**XML Tag Patterns Identified**:

All subagent files use consistent XML structure:

```xml
<context>
  <specialist_domain>...</specialist_domain>
  <task_scope>...</task_scope>
  <integration>...</integration>
  <lifecycle_integration>...</lifecycle_integration>
</context>

<role>...</role>

<task>...</task>

<inputs_required>
  <parameter name="..." type="...">...</parameter>
</inputs_required>

<inputs_forbidden>
  <forbidden>...</forbidden>
</inputs_forbidden>

<process_flow>
  <step_1>
    <action>...</action>
    <process>...</process>
    <validation>...</validation>
    <output>...</output>
  </step_1>
  ...
</process_flow>

<constraints>
  <must>...</must>
  <must_not>...</must_not>
</constraints>

<output_specification>
  <format>...</format>
  <example>...</example>
  <error_handling>...</error_handling>
</output_specification>

<validation_checks>
  <pre_execution>...</pre_execution>
  <post_execution>...</post_execution>
</validation_checks>

<{agent_type}_principles>
  <principle_1>...</principle_1>
  ...
</{agent_type}_principles>
```

**Current Orchestrator.md Structure**:

The orchestrator.md file uses markdown headers exclusively:
- `## Overview`
- `## Context Loading`
- `## Delegation Registry`
- `## Workflow Stages` → `### Stage 1: AnalyzeRequest`
- `## Helper Functions`
- `## Error Handling`
- `## Registry Maintenance`
- `## Testing`
- `## Related Documentation`

**Mapping Orchestrator Sections to XML Tags**:

| Current Section | Recommended XML Tag | Notes |
|----------------|---------------------|-------|
| Overview | `<context>` + `<role>` + `<task>` | Split into structured metadata |
| Context Loading | `<context_loading>` | New tag for orchestrator-specific feature |
| Delegation Registry | `<delegation_registry>` | New tag for orchestrator-specific feature |
| Workflow Stages | `<process_flow>` with `<stage_N>` | Rename "Stage" to align with subagent pattern |
| Helper Functions | `<helper_functions>` | Keep as separate section |
| Error Handling | `<error_handling>` within `<output_specification>` | Align with subagent pattern |
| Registry Maintenance | `<registry_maintenance>` | New tag for orchestrator-specific feature |
| Testing | `<testing>` | Keep as separate section |
| Related Documentation | Remove or move to `<context>` | Not needed in XML structure |

**Recommended XML Structure for Orchestrator**:

```xml
<context>
  <specialist_domain>Central coordination and delegation management</specialist_domain>
  <task_scope>Route requests, manage delegations, enforce safety, validate returns</task_scope>
  <integration>Primary entry point for all user commands</integration>
  <context_loading>
    <level_1>Common standards (80% of requests)</level_1>
    <level_2>Filtered by language (20% of requests)</level_2>
    <level_3>Full context (rare, complex requests)</level_3>
  </context_loading>
</context>

<role>
  Central orchestrator managing command routing and delegation lifecycle
</role>

<task>
  Receive user commands, route to appropriate agents, monitor delegations, validate returns
</task>

<delegation_registry>
  <!-- Registry structure and operations -->
</delegation_registry>

<process_flow>
  <stage_1>
    <name>AnalyzeRequest</name>
    <action>...</action>
    <process>...</process>
    <output>...</output>
  </stage_1>
  ...
</process_flow>

<helper_functions>
  <!-- Helper function definitions -->
</helper_functions>

<error_handling>
  <!-- Error handling patterns -->
</error_handling>

<registry_maintenance>
  <!-- Registry cleanup and export -->
</registry_maintenance>

<testing>
  <!-- Test cases -->
</testing>

<orchestrator_principles>
  <principle_1>Language-based routing: Always extract language from TODO.md</principle_1>
  <principle_2>Delegation safety: Enforce cycle detection and depth limits</principle_2>
  <principle_3>Timeout handling: Monitor deadlines and recover partial results</principle_3>
  <principle_4>Return validation: Validate all returns against standard format</principle_4>
  <principle_5>Registry tracking: Maintain active delegation state</principle_5>
</orchestrator_principles>
```

**Structural Changes Required**:

1. **Add YAML frontmatter** (like subagents):
   ```yaml
   ---
   description: "Central orchestrator for command routing and delegation management"
   mode: primary
   temperature: 0.2
   ---
   ```

2. **Wrap Overview in XML tags**: Split into `<context>`, `<role>`, `<task>`

3. **Rename "Workflow Stages" to "Process Flow"**: Use `<process_flow>` with `<stage_N>` tags

4. **Wrap each stage in XML**: 
   ```xml
   <stage_1>
     <name>AnalyzeRequest</name>
     <action>Parse and understand the user request</action>
     <process>...</process>
     <output>...</output>
   </stage_1>
   ```

5. **Add orchestrator-specific tags**: `<delegation_registry>`, `<context_loading>`, `<registry_maintenance>`

6. **Add principles section**: `<orchestrator_principles>` at end

7. **Remove version and date metadata**: Use git history instead

**Backward Compatibility**:

The XML styling changes are **backward compatible** with existing command workflows because:
- Commands reference the orchestrator by file path, not by parsing its structure
- The orchestrator's behavior is defined by its content, not its formatting
- XML tags are semantic markers for human readers and LLM context, not executable code
- All existing workflow stages remain intact, just wrapped in XML tags

**Benefits of XML Styling**:

1. **Consistency**: All agents use same structure (easier to maintain)
2. **Clarity**: XML tags make sections explicit and machine-parseable
3. **Extensibility**: Easy to add new sections without breaking structure
4. **LLM Context**: XML tags help LLMs understand document structure better
5. **Validation**: Can validate structure against schema if needed

---

### Finding 3: Default Agent Configuration Research

**Research Question**: Does renaming `orchestrator.md` to `AGENTS.md` enable default orchestrator mode in OpenCode?

**Sources**:
- OpenCode Rules Documentation: https://opencode.ai/docs/rules/
- OpenCode Agents Documentation: https://opencode.ai/docs/agents/

**Key Findings**:

#### AGENTS.md Purpose

From OpenCode documentation:

> "You can provide custom instructions to opencode by creating an `AGENTS.md` file. This is similar to `CLAUDE.md` or Cursor's rules. It contains instructions that will be included in the LLM's context to customize its behavior for your specific project."

**AGENTS.md is NOT for defining agents** - it's for **custom instructions** (rules).

#### AGENTS.md Locations

OpenCode looks for AGENTS.md in two locations:

1. **Project-specific**: `AGENTS.md` in project root (committed to git, shared with team)
2. **Global**: `~/.config/opencode/AGENTS.md` (personal rules, not shared)

**Precedence**: OpenCode combines both files if present.

#### Agent Definition Locations

Agents are defined in **different locations** than AGENTS.md:

1. **JSON Configuration**: `opencode.json` or `~/.config/opencode/opencode.json`
   ```json
   {
     "agent": {
       "build": { "mode": "primary", ... },
       "plan": { "mode": "primary", ... }
     }
   }
   ```

2. **Markdown Files**:
   - Global: `~/.config/opencode/agent/*.md`
   - Project: `.opencode/agent/*.md`

**File name becomes agent name**: `review.md` → `review` agent

#### Default Agent Behavior

From OpenCode documentation:

> "Build is the **default** primary agent with all tools enabled. This is the standard agent for development work where you need full access to file operations and system commands."

**Default agent is hardcoded to "build"** - not configurable via AGENTS.md.

#### Switching Agents

Users can switch between primary agents:
- **Tab key**: Cycle through primary agents
- **@ mention**: Invoke specific subagent (e.g., `@general help me search`)

#### Orchestrator.md Location

Current location: `.opencode/agent/orchestrator.md`

This is **correct** for a custom agent definition. The orchestrator is:
- A **primary agent** (mode: primary)
- Defined in project-specific location (`.opencode/agent/`)
- Named `orchestrator` (from filename `orchestrator.md`)

**Renaming to AGENTS.md would BREAK the orchestrator** because:
1. AGENTS.md is for custom instructions, not agent definitions
2. The orchestrator would no longer be recognized as an agent
3. Users would lose the ability to invoke the orchestrator

#### Correct Approach for Default Orchestrator

To make orchestrator the default agent, use `opencode.json`:

```json
{
  "$schema": "https://opencode.ai/config.json",
  "agent": {
    "orchestrator": {
      "mode": "primary",
      "description": "Central orchestrator for command routing and delegation",
      "prompt": "{file:./.opencode/agent/orchestrator.md}",
      "temperature": 0.2
    }
  },
  "defaultAgent": "orchestrator"
}
```

**Note**: The `defaultAgent` field is **not documented** in OpenCode docs. This may not be supported.

**Alternative**: Use OpenCode's built-in agent switching:
- Keep orchestrator as a primary agent in `.opencode/agent/orchestrator.md`
- Users press **Tab** to switch to orchestrator when needed
- Or invoke with `@orchestrator` mention

**Recommendation**: 
1. **Keep orchestrator.md in current location** (`.opencode/agent/orchestrator.md`)
2. **Do NOT rename to AGENTS.md** (would break agent definition)
3. **Add to opencode.json** if you want to configure it:
   ```json
   {
     "agent": {
       "orchestrator": {
         "mode": "primary",
         "prompt": "{file:./.opencode/agent/orchestrator.md}"
       }
     }
   }
   ```
4. **Document usage**: Tell users to press Tab or use `@orchestrator` to invoke

---

## Detailed Analysis

### FIX Comment Rewrite Strategy

**Sections to Rewrite**:

1. **Lines 16-22** (Key Improvements Over v1):
   - Remove "Over v1" comparison
   - Reframe as "Core Capabilities"
   - Present as current features, not improvements

2. **Lines 24-29** (Problems Solved):
   - Remove "Task 191" reference
   - Reframe as "Delegation Safety Features"
   - Present as current safety mechanisms, not fixes

3. **Line 3** (Version 2.0):
   - Remove version number
   - Use git history for versioning instead

4. **Line 6** (Created date):
   - Remove creation date
   - Use git history for creation tracking

**Rewrite Principles**:
- **Present tense**: "The orchestrator provides" not "We added"
- **Feature-focused**: Describe what it does, not what it fixed
- **No historical context**: Assume reader doesn't know v1 or Task 191
- **Logical grouping**: Group related features together
- **Professional tone**: Documentation, not changelog

### XML Styling Implementation Plan

**Phase 1: Add YAML Frontmatter** (5 minutes)
```yaml
---
description: "Central orchestrator for command routing and delegation management"
mode: primary
temperature: 0.2
---
```

**Phase 2: Wrap Overview in XML** (15 minutes)
- Split Overview into `<context>`, `<role>`, `<task>`
- Move Context Loading into `<context><context_loading>`
- Remove version and date metadata

**Phase 3: Rename and Wrap Workflow Stages** (30 minutes)
- Rename "Workflow Stages" to "Process Flow"
- Wrap in `<process_flow>` tag
- Wrap each stage in `<stage_N>` tag with `<name>`, `<action>`, `<process>`, `<output>`

**Phase 4: Wrap Delegation Registry** (10 minutes)
- Wrap in `<delegation_registry>` tag
- Keep existing content structure

**Phase 5: Wrap Helper Functions** (5 minutes)
- Wrap in `<helper_functions>` tag

**Phase 6: Wrap Error Handling** (10 minutes)
- Wrap in `<error_handling>` tag

**Phase 7: Wrap Registry Maintenance** (5 minutes)
- Wrap in `<registry_maintenance>` tag

**Phase 8: Wrap Testing** (5 minutes)
- Wrap in `<testing>` tag

**Phase 9: Add Orchestrator Principles** (15 minutes)
- Create `<orchestrator_principles>` section
- Extract key principles from document
- Format as `<principle_N>` tags

**Total Estimated Effort**: 1.5 hours

### Default Agent Configuration Options

**Option 1: Keep Current Setup** (Recommended)
- Orchestrator remains at `.opencode/agent/orchestrator.md`
- Users invoke with Tab key or `@orchestrator`
- No configuration changes needed
- **Pros**: Simple, no breaking changes
- **Cons**: Not default agent (users must switch)

**Option 2: Configure in opencode.json**
- Add orchestrator to `opencode.json` agent config
- Potentially set as default (if supported)
- **Pros**: Centralized configuration
- **Cons**: `defaultAgent` field not documented (may not work)

**Option 3: Replace Build Agent**
- Rename orchestrator.md to build.md
- Override built-in build agent
- **Pros**: Becomes default automatically
- **Cons**: Loses built-in build agent, confusing naming

**Recommendation**: **Option 1** - Keep current setup, document usage clearly

---

## Code Examples

### Example 1: Rewritten Overview Section

**Before**:
```markdown
## Overview

The orchestrator is the primary coordination agent for the .opencode system. It receives user requests, analyzes them, routes to appropriate subagents, and manages delegation safety through session tracking, cycle detection, and timeout enforcement.

<!-- FIX: turn this into a statement of the current system without comparison to the past system for clarity and directness. Do something similar for the rest of this file, avoiding historical mentions. -->

**Key Improvements Over v1**:
- Delegation registry for active tracking
- Cycle detection (max depth 3)
- Session ID tracking
- Language-based routing
- Timeout enforcement
- Standardized return validation

**Problems Solved** (Task 191):
- Root Cause #1: Missing return paths (explicit receive/validate stages)
- Root Cause #2: Infinite loops (cycle detection)
- Root Cause #3: Async/sync mismatch (timeout handling)
- Root Cause #4: Missing error handling (comprehensive error handling)
- Root Cause #5: Coordination gaps (delegation registry)
```

**After**:
```markdown
## Overview

The orchestrator is the primary coordination agent for the .opencode system. It receives user requests, analyzes them, routes to appropriate subagents, and manages delegation safety through session tracking, cycle detection, and timeout enforcement.

## Core Capabilities

The orchestrator provides:

- **Delegation Registry**: Active tracking of all delegations with session IDs, timeouts, and status
- **Cycle Detection**: Prevents infinite delegation loops (max depth 3)
- **Session Tracking**: Unique session IDs for correlation and debugging
- **Language-Based Routing**: Routes tasks to language-specific agents (lean, markdown, python, general)
- **Timeout Enforcement**: Monitors delegations and handles timeouts gracefully with partial results
- **Return Validation**: Validates all subagent returns against standardized format

## Delegation Safety Features

The orchestrator ensures safe delegation through:

- **Explicit Return Paths**: ReceiveResults and ProcessResults stages for all delegations
- **Cycle Prevention**: Detects and blocks delegation cycles before they occur
- **Timeout Handling**: Monitors deadlines and recovers partial results on timeout
- **Comprehensive Error Handling**: Logs errors, provides recovery steps, and maintains system stability
- **Coordination Registry**: Centralized tracking prevents lost delegations and orphaned sessions
```

### Example 2: XML-Styled Stage

**Before**:
```markdown
### Stage 1: AnalyzeRequest

**Action**: Parse and understand the user request

**Process**:
1. Extract command type (task, research, plan, implement, etc.)
2. Load command file from .opencode/command/{command}.md
3. Command file contains $ARGUMENTS which OpenCode substitutes with actual user arguments
4. Read <argument_parsing> section from command file for validation rules
5. Workflow Stage 1 in command file will parse and validate $ARGUMENTS
6. If command has no arguments, proceed directly to workflow execution

**Output**: Command loaded and ready for execution
```

**After**:
```xml
<stage_1>
  <name>AnalyzeRequest</name>
  <action>Parse and understand the user request</action>
  <process>
    1. Extract command type (task, research, plan, implement, etc.)
    2. Load command file from .opencode/command/{command}.md
    3. Command file contains $ARGUMENTS which OpenCode substitutes with actual user arguments
    4. Read <argument_parsing> section from command file for validation rules
    5. Workflow Stage 1 in command file will parse and validate $ARGUMENTS
    6. If command has no arguments, proceed directly to workflow execution
  </process>
  <output>Command loaded and ready for execution</output>
</stage_1>
```

### Example 3: opencode.json Configuration

```json
{
  "$schema": "https://opencode.ai/config.json",
  "agent": {
    "orchestrator": {
      "description": "Central orchestrator for command routing and delegation management",
      "mode": "primary",
      "prompt": "{file:./.opencode/agent/orchestrator.md}",
      "temperature": 0.2,
      "tools": {
        "write": true,
        "edit": true,
        "bash": true,
        "read": true
      }
    }
  }
}
```

---

## Recommendations

### Recommendation 1: Rewrite Historical Sections

**Priority**: High  
**Effort**: 30 minutes  

**Action**:
1. Replace lines 16-29 with "Core Capabilities" and "Delegation Safety Features" sections
2. Remove version number (line 3) and creation date (line 6)
3. Remove FIX comment (line 14)
4. Review entire document for other historical references

**Rationale**: Improves clarity, professionalism, and maintainability

### Recommendation 2: Apply XML Styling

**Priority**: Medium  
**Effort**: 1.5 hours  

**Action**:
1. Add YAML frontmatter
2. Wrap sections in XML tags following subagent pattern
3. Rename "Workflow Stages" to "Process Flow"
4. Add `<orchestrator_principles>` section
5. Test that commands still work correctly

**Rationale**: Consistency with other agents, better structure, improved LLM context

### Recommendation 3: Keep Current Agent Location

**Priority**: High  
**Effort**: 0 minutes (no change)  

**Action**:
1. **Do NOT rename orchestrator.md to AGENTS.md**
2. Keep orchestrator at `.opencode/agent/orchestrator.md`
3. Optionally add to `opencode.json` for configuration
4. Document usage: "Press Tab to switch to orchestrator or use `@orchestrator`"

**Rationale**: AGENTS.md is for custom instructions, not agent definitions. Renaming would break the orchestrator.

### Recommendation 4: Document Agent Usage

**Priority**: Medium  
**Effort**: 15 minutes  

**Action**:
1. Add "Usage" section to orchestrator.md
2. Explain how to invoke orchestrator (Tab key or `@orchestrator`)
3. Explain relationship to built-in agents (build, plan)
4. Add to project README if needed

**Rationale**: Helps users understand how to use the orchestrator

---

## Implementation Estimate

### Total Effort Breakdown

| Task | Effort | Priority |
|------|--------|----------|
| Rewrite historical sections | 30 min | High |
| Apply XML styling | 1.5 hours | Medium |
| Keep current location (no change) | 0 min | High |
| Document agent usage | 15 min | Medium |
| **Total** | **2 hours 15 min** | - |

### Implementation Order

1. **Rewrite historical sections** (30 min) - High priority, quick win
2. **Apply XML styling** (1.5 hours) - Medium priority, larger effort
3. **Document agent usage** (15 min) - Medium priority, quick win

### Testing Plan

After each change:
1. Verify orchestrator.md is still readable
2. Test command invocation (e.g., `/task`, `/research`)
3. Verify delegation still works
4. Check that XML tags don't break parsing

---

## Sources and Citations

1. **OpenCode Rules Documentation**  
   URL: https://opencode.ai/docs/rules/  
   Retrieved: 2025-12-28  
   Content: AGENTS.md purpose, locations, precedence

2. **OpenCode Agents Documentation**  
   URL: https://opencode.ai/docs/agents/  
   Retrieved: 2025-12-28  
   Content: Agent types, configuration, default agent behavior

3. **Project Files Analyzed**:
   - `.opencode/agent/orchestrator.md` (914 lines)
   - `.opencode/agent/subagents/error-diagnostics-agent.md` (495 lines)
   - `.opencode/agent/subagents/planner.md` (337 lines)
   - `.opencode/agent/subagents/researcher.md` (345 lines)

---

## Conclusion

This research provides clear guidance for three orchestrator.md improvements:

1. **FIX Comment**: Rewrite historical sections to present current capabilities directly
2. **XML Styling**: Apply consistent XML structure used in other subagents
3. **Default Agent**: Keep orchestrator.md in current location; AGENTS.md is for custom instructions, not agent definitions

All three improvements are feasible with estimated total effort of 2 hours 15 minutes. The changes are backward compatible and will improve consistency, clarity, and maintainability.
