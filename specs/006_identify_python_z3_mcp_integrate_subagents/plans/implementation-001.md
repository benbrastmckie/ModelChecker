# Implementation Plan: Task #6

- **Task**: 6 - Identify Python and Z3 MCP Integration for Subagents
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: specs/006_identify_python_z3_mcp_integrate_subagents/reports/research-001.md, specs/006_identify_python_z3_mcp_integrate_subagents/reports/research-002.md
- **Artifacts**: plans/implementation-001.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: meta
- **Lean Intent**: false

## Overview

Create Python and Z3 research/implementation subagents with domain-specific context files and skill wrappers. The research identified Context7 MCP for documentation lookup, z3_mcp for Z3 constraint solving, and mcp_python_toolbox for Python development. Due to the documented MCP scope limitation (subagents cannot access project-scoped MCP servers), these tools are designed as optional enhancements with graceful fallback to standard tools.

### Research Integration

**From research-001.md**:
- Context7 MCP provides live documentation lookup (user-scope configuration required)
- z3_mcp (javergar) provides Z3 constraint solving via MCP protocol
- mcp_python_toolbox provides Python analysis and formatting tools
- MCP servers must be configured in user scope (`~/.claude.json`) for subagent access

**From research-002.md**:
- Agents follow 8-stage execution flow with YAML frontmatter
- Context organized under `.claude/context/project/{domain}/` with README, domain/, patterns/, standards/, templates/
- Research agents use read-only tools + WebSearch/WebFetch; implementation agents add Write/Edit/Bash
- Lazy context loading via @-references with loading conditions

## Goals & Non-Goals

**Goals**:
- Create `.claude/context/project/python/` directory with ModelChecker-specific patterns
- Create `.claude/context/project/z3/` directory with Z3 API and constraint patterns
- Define 4 new agents: python-research, python-implementation, z3-research, z3-implementation
- Create 4 corresponding skills as thin wrappers
- Update CLAUDE.md with new language routing and skill-to-agent mappings
- Document MCP configuration for optional enhanced capabilities

**Non-Goals**:
- Installing MCP servers (user responsibility; documented only)
- Implementing first-order or spatial logos subtheories (future task)
- Creating combined python-z3-agent (keeping separate for focused expertise)
- Modifying existing agents (additive changes only)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| MCP scope limitation persists | Medium | High | Design agents to work without MCP; MCP is enhancement only |
| Context files become stale | Low | Medium | Link to source files; note update triggers |
| Agent proliferation | Low | Low | Follow established patterns; consider consolidation if overlap emerges |
| Incomplete ModelChecker coverage | Medium | Low | Focus on logos/semantic.py patterns; extend incrementally |

## Implementation Phases

### Phase 1: Create Python Context Directory [COMPLETED]

**Goal**: Establish domain context for Python/ModelChecker development

**Tasks**:
- [ ] Create `.claude/context/project/python/` directory structure
- [ ] Write `README.md` with loading strategy and overview
- [ ] Write `domain/model-checker-api.md` documenting package structure and key classes
- [ ] Write `domain/theory-lib-patterns.md` documenting standard theory library conventions
- [ ] Write `patterns/semantic-evaluation.md` documenting truthmaker semantic patterns
- [ ] Write `standards/code-style.md` referencing project Python conventions

**Timing**: 1.5 hours

**Files to create**:
- `.claude/context/project/python/README.md` - Overview and loading strategy
- `.claude/context/project/python/domain/model-checker-api.md` - Package structure
- `.claude/context/project/python/domain/theory-lib-patterns.md` - Theory conventions
- `.claude/context/project/python/patterns/semantic-evaluation.md` - Semantic patterns
- `.claude/context/project/python/standards/code-style.md` - Python style guide

**Verification**:
- All files exist and are non-empty
- README contains valid @-reference examples

---

### Phase 2: Create Z3 Context Directory [NOT STARTED]

**Goal**: Establish domain context for Z3/SMT development within ModelChecker

**Tasks**:
- [ ] Create `.claude/context/project/z3/` directory structure
- [ ] Write `README.md` with Z3 overview and ModelChecker usage patterns
- [ ] Write `domain/z3-api.md` documenting core Z3 Python API
- [ ] Write `domain/smt-patterns.md` documenting SMT-LIB and solver patterns
- [ ] Write `patterns/constraint-generation.md` documenting ModelChecker Z3 patterns
- [ ] Write `patterns/bitvector-operations.md` documenting BitVec patterns for state representation

**Timing**: 1.5 hours

**Files to create**:
- `.claude/context/project/z3/README.md` - Overview and loading strategy
- `.claude/context/project/z3/domain/z3-api.md` - Z3 Python API reference
- `.claude/context/project/z3/domain/smt-patterns.md` - SMT-LIB patterns
- `.claude/context/project/z3/patterns/constraint-generation.md` - Constraint building
- `.claude/context/project/z3/patterns/bitvector-operations.md` - BitVec patterns

**Verification**:
- All files exist and are non-empty
- README contains valid @-reference examples

---

### Phase 3: Create Python Agents [NOT STARTED]

**Goal**: Define python-research-agent and python-implementation-agent

**Tasks**:
- [ ] Create `.claude/agents/python-research-agent.md` following general-research-agent pattern
- [ ] Create `.claude/agents/python-implementation-agent.md` following general-implementation-agent pattern
- [ ] Both agents reference Python context files via @-references
- [ ] Include MCP tools as optional enhancements
- [ ] Include ModelChecker-specific verification commands

**Timing**: 1 hour

**Files to create**:
- `.claude/agents/python-research-agent.md` - Research agent for Python/ModelChecker
- `.claude/agents/python-implementation-agent.md` - Implementation agent for Python code

**Verification**:
- Agent files have YAML frontmatter with name and description
- All 8 stages documented in execution flow
- Context references include Python-specific files
- Verification commands use PYTHONPATH=Code/src pattern

---

### Phase 4: Create Z3 Agents [NOT STARTED]

**Goal**: Define z3-research-agent and z3-implementation-agent

**Tasks**:
- [ ] Create `.claude/agents/z3-research-agent.md` following general-research-agent pattern
- [ ] Create `.claude/agents/z3-implementation-agent.md` following general-implementation-agent pattern
- [ ] Both agents reference Z3 context files via @-references
- [ ] Include MCP tools (z3_mcp, context7) as optional enhancements
- [ ] Include Z3-specific verification patterns

**Timing**: 1 hour

**Files to create**:
- `.claude/agents/z3-research-agent.md` - Research agent for Z3/SMT topics
- `.claude/agents/z3-implementation-agent.md` - Implementation agent for Z3 constraints

**Verification**:
- Agent files have YAML frontmatter with name and description
- All 8 stages documented in execution flow
- Context references include Z3-specific files
- Verification includes Z3 version check and pytest -k z3

---

### Phase 5: Create Skills and Update Configuration [NOT STARTED]

**Goal**: Create skill wrappers and update CLAUDE.md

**Tasks**:
- [ ] Create `.claude/skills/skill-python-research/SKILL.md` routing to python-research-agent
- [ ] Create `.claude/skills/skill-python-implementation/SKILL.md` routing to python-implementation-agent
- [ ] Create `.claude/skills/skill-z3-research/SKILL.md` routing to z3-research-agent
- [ ] Create `.claude/skills/skill-z3-implementation/SKILL.md` routing to z3-implementation-agent
- [ ] Update `.claude/CLAUDE.md` Language-Based Routing table with `python` and `z3` languages
- [ ] Update `.claude/CLAUDE.md` Skill-to-Agent Mapping table with new entries
- [ ] Update `.claude/context/index.md` with new Python and Z3 context files

**Timing**: 1 hour

**Files to create**:
- `.claude/skills/skill-python-research/SKILL.md`
- `.claude/skills/skill-python-implementation/SKILL.md`
- `.claude/skills/skill-z3-research/SKILL.md`
- `.claude/skills/skill-z3-implementation/SKILL.md`

**Files to modify**:
- `.claude/CLAUDE.md` - Add routing and mapping entries
- `.claude/context/index.md` - Add new context file references

**Verification**:
- Skills exist in correct directories
- CLAUDE.md contains `python` and `z3` in Language-Based Routing
- CLAUDE.md contains 4 new entries in Skill-to-Agent Mapping
- index.md references new Python and Z3 context directories

## Testing & Validation

- [ ] All 17 new files created exist and are non-empty
- [ ] Agent files contain required YAML frontmatter
- [ ] CLAUDE.md edits render correctly (no broken markdown)
- [ ] Context @-references in agents resolve to valid paths
- [ ] Bash verification: `ls .claude/agents/python-*.md .claude/agents/z3-*.md`
- [ ] Bash verification: `ls .claude/skills/skill-python-*/ .claude/skills/skill-z3-*/`
- [ ] Bash verification: `grep -q "python" .claude/CLAUDE.md && grep -q "z3" .claude/CLAUDE.md`

## Artifacts & Outputs

**New directories**:
- `.claude/context/project/python/` (5 files)
- `.claude/context/project/z3/` (5 files)
- `.claude/skills/skill-python-research/`
- `.claude/skills/skill-python-implementation/`
- `.claude/skills/skill-z3-research/`
- `.claude/skills/skill-z3-implementation/`

**New files** (17 total):
- 5 Python context files
- 5 Z3 context files
- 4 agent definitions
- 4 skill definitions (SKILL.md in each directory)

**Modified files** (2):
- `.claude/CLAUDE.md` - Routing and mapping tables
- `.claude/context/index.md` - Context references

**Summaries**:
- `specs/006_identify_python_z3_mcp_integrate_subagents/summaries/implementation-summary-{DATE}.md`

## Rollback/Contingency

All changes are additive. Rollback by:
1. Remove created directories: `rm -rf .claude/context/project/python .claude/context/project/z3`
2. Remove agent files: `rm .claude/agents/python-*.md .claude/agents/z3-*.md`
3. Remove skill directories: `rm -rf .claude/skills/skill-python-* .claude/skills/skill-z3-*`
4. Revert CLAUDE.md and index.md edits via git: `git checkout .claude/CLAUDE.md .claude/context/index.md`
