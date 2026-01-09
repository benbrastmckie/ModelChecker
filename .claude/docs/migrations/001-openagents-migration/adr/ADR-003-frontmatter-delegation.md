# ADR-003: Frontmatter Delegation Pattern

**Status**: Accepted  
**Date**: 2025-12-28  
**Decision Makers**: ProofChecker Development Team  
**Related Tasks**: Task 245 (Phase 2)

---

## Context and Problem Statement

The original OpenCode system embedded routing logic directly in command files. Each command contained 800-1200 lines of code including routing logic, workflow execution, and agent delegation. This created several problems:

1. **File Size Bloat**: Command files were 800-1200 lines (too large)
2. **Embedded Routing Logic**: Routing logic mixed with documentation
3. **Maintenance Burden**: Changes to routing required updating all commands
4. **Poor Separation of Concerns**: Commands did too much
5. **Difficult to Understand**: Large files were hard to navigate

**Key Question**: How can we separate routing metadata from routing logic while keeping commands simple and maintainable?

---

## Decision Drivers

1. **File Size**: Command files must be <300 lines
2. **Separation of Concerns**: Routing metadata separate from routing logic
3. **Maintainability**: Routing changes should require minimal command updates
4. **Discoverability**: Easy to see which agent handles each command
5. **Simplicity**: Commands should be easy to understand

---

## Considered Options

### Option 1: Embedded Workflow (Status Quo)

**Description**: Continue embedding routing logic and workflow in command files.

**Pros**:
- No changes required
- All logic in one place
- Familiar pattern

**Cons**:
- 800-1200 line command files
- Routing logic mixed with documentation
- High maintenance burden
- Poor separation of concerns

**Verdict**: ❌ Rejected - Doesn't solve file size problem

### Option 2: External Configuration File

**Description**: Move routing configuration to separate YAML/JSON file.

**Pros**:
- Routing metadata separate from commands
- Structured configuration
- Easy to parse programmatically

**Cons**:
- Requires separate configuration file
- Routing metadata not visible in command file
- Additional file to maintain
- Less discoverable

**Verdict**: ❌ Rejected - Poor discoverability

### Option 3: Frontmatter Delegation (Selected)

**Description**: Use YAML frontmatter in command files to specify agent. Orchestrator reads frontmatter and delegates to specified agent.

**Pros**:
- Routing metadata in command file (visible)
- Minimal syntax (just `agent:` field)
- No separate configuration file needed
- Easy to discover (frontmatter at top of file)
- Orchestrator handles all routing logic
- Commands become thin delegation layers

**Cons**:
- Requires frontmatter parsing in orchestrator
- Initial implementation effort

**Verdict**: ✅ **Selected** - Best balance of simplicity and discoverability

---

## Decision Outcome

**Chosen Option**: Frontmatter Delegation (Option 3)

### Implementation

1. **Frontmatter Format**: YAML frontmatter at top of command files
   ```yaml
   ---
   agent: research-agent
   ---
   ```

2. **Command Structure**: Commands contain only:
   - Frontmatter (agent specification)
   - Purpose documentation
   - Usage instructions
   - Examples
   - No routing logic or workflow execution

3. **Orchestrator Routing**: Orchestrator reads frontmatter and delegates
   - Parse frontmatter to extract `agent:` field
   - Load agent file from `.claude/skills/{agent}.md`
   - Delegate request to agent
   - Return agent response to user

4. **Agent Specification**: Agents specified by name
   - `research-agent` → `.claude/skills/research-agent.md`
   - `planner` → `.claude/skills/planner.md`
   - `implementer` → `.claude/skills/implementer.md`
   - `reviser` → `.claude/skills/reviser.md`

### Positive Consequences

1. **File Size Reduction**: Commands reduced from 800-1200 lines to 180-270 lines (70-85% reduction)
2. **Discoverability**: Agent visible in frontmatter at top of file
3. **Maintainability**: Routing logic centralized in orchestrator
4. **Simplicity**: Commands are easy to understand (just documentation)
5. **Separation of Concerns**: Routing metadata separate from routing logic

### Negative Consequences

1. **Frontmatter Parsing**: Orchestrator must parse YAML frontmatter (minor complexity)
2. **Convention**: Developers must remember to include frontmatter (mitigated by templates)
3. **Migration Effort**: Required migrating all commands (one-time cost)

### Mitigation Strategies

1. **Command Template**: Provide template with frontmatter included
2. **Validation**: Check for frontmatter in code review
3. **Documentation**: Document frontmatter pattern in development guide
4. **Error Handling**: Orchestrator validates frontmatter and provides clear errors

---

## Validation

### Success Criteria

- [x] All command files <300 lines
- [x] All commands use frontmatter delegation
- [x] Orchestrator successfully routes based on frontmatter
- [x] No functionality lost during migration

### Actual Results

- **Command File Sizes**: 180-270 lines (all under 300 line target)
- **Frontmatter Compliance**: All 4 commands use frontmatter delegation
- **Routing Success**: 100% successful routing (no failures)
- **Functionality**: Zero regressions, all features working

**Validation Status**: ✅ [PASS] - All success criteria met

---

## Pattern Details

### Frontmatter Schema

```yaml
---
agent: <agent-name>
---
```

**Fields**:
- `agent` (required): Name of agent to handle this command
  - Must match agent file name (without `.md` extension)
  - Example: `research-agent` → `.claude/skills/research-agent.md`

**Future Extensions** (not implemented):
- `version`: Agent version to use
- `timeout`: Custom timeout for this command
- `context`: Additional context files to load

### Command File Structure

```markdown
---
agent: research-agent
---

# /research Command

## Purpose
[Command purpose documentation]

## Usage
[Usage instructions]

## Examples
[Usage examples]

## Workflow
[High-level workflow description]
```

### Orchestrator Routing Logic

```
1. Parse command file frontmatter
2. Extract `agent:` field
3. Validate agent file exists
4. Load agent file
5. Delegate request to agent
6. Return agent response
```

---

## Lessons Learned

1. **Frontmatter is Effective**: Simple, visible, and easy to maintain
2. **Thin Delegation Layers**: Commands should delegate, not execute
3. **Centralized Routing**: Orchestrator should own all routing logic
4. **Templates Help**: Command template ensures frontmatter included
5. **File Size Matters**: Smaller files are easier to understand and maintain

---

## References

- **Implementation**: Task 245 (Phase 2: Core Architecture Migration)
- **Validation**: `.claude/specs/245_phase_2_core_architecture_migration/reports/validation-001.md`
- **Command Files**: `.claude/command/*.md`
- **Agent Files**: `.claude/skills/*.md`
- **Command Template**: `.claude/docs/templates/command-template.md`
- **Migration Guide**: `.claude/docs/migrations/001-openagents-migration/phase-2-guide.md`

---

**ADR Status**: Accepted and Implemented  
**Last Updated**: 2025-12-29
