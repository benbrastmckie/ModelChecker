# Research Report: Task #6 (Round 2)

**Task**: 6 - Identify Python and Z3 MCP Integration for Subagents
**Started**: 2026-03-01T19:44:41Z
**Completed**: 2026-03-01T20:15:00Z
**Effort**: 2-3 hours (implementation)
**Dependencies**: None
**Sources/Inputs**: Codebase analysis (.claude/agents/, .claude/context/, .claude/skills/)
**Artifacts**: This research report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Existing agent patterns identified**: 9 agent definitions following consistent 8-stage structure with YAML frontmatter, tool declarations, context references, and execution flow
- **Context index system**: Hierarchical organization under `.claude/context/` with core/, project/, and per-domain subdirectories; agents load context via @-references
- **Tool access patterns**: Research agents (read-only: WebSearch, WebFetch, Read, Glob, Grep), Implementation agents (full: Read, Write, Edit, Bash with domain-specific verification commands)
- **Recommended context files**: Z3 API patterns, SMT-LIB syntax, Python model-checker patterns, existing logos semantic evaluation code
- **Integration approach**: Create python/z3 context directory with domain knowledge; new agents reference these via @.claude/context/project/python/ and @.claude/context/project/z3/

## Context & Scope

### Research Focus

This research round focuses on:
1. How existing agents declare tools and context
2. Context index system organization
3. Patterns for domain-specific context files
4. Concrete recommendations for Python/Z3 agent implementation

### Prior Research (Round 1)

Research-001.md covered:
- MCP server identification (z3_mcp, mcp_python_toolbox, Context7)
- Installation and configuration procedures
- Language routing table extensions
- Phase-based implementation plan

This round complements by analyzing existing agent architecture to ensure new agents follow established patterns.

## Findings

### 1. Existing Agent Architecture Patterns

#### Agent File Structure

All agents in `.claude/agents/` follow this structure:

```markdown
---
name: {agent-name}
description: {brief description}
---

# {Agent Name}

## Overview
{Purpose, invocation pattern, return format}

## Agent Metadata
- **Name**: {agent-name}
- **Purpose**: {purpose}
- **Invoked By**: {skill-name} (via Task tool)
- **Return Format**: Brief text summary + metadata file

## Allowed Tools
{Categorized list of tools with descriptions}

## Context References
{@-references to context files with loading conditions}

## Execution Flow
{8-stage workflow with code examples}

## Error Handling
{Domain-specific error patterns}

## Critical Requirements
{MUST DO and MUST NOT lists}
```

#### Tool Access Patterns

**Research Agents** (general-research-agent, neovim-research-agent):
| Tool | Purpose |
|------|---------|
| Read | Source files, documentation, context documents |
| Write | Research reports, metadata file |
| Edit | Modify existing files if needed |
| Glob | Find files by pattern |
| Grep | Search file contents |
| Bash | Verification commands |
| WebSearch | Documentation, tutorials, best practices |
| WebFetch | Specific documentation pages |

**Implementation Agents** (general-implementation-agent, neovim-implementation-agent, latex-implementation-agent):
| Tool | Purpose |
|------|---------|
| Read | Plans, source files, context documents |
| Write | New files, summaries |
| Edit | Modify existing files |
| Glob | Find files by pattern |
| Grep | Search file contents |
| Bash | Build commands, tests, verification |

**Domain-specific Bash usage**:
- Neovim: `nvim --headless -c "lua require('module')" -c "q"`
- LaTeX: `latexmk -pdf -interaction=nonstopmode document.tex`

#### 8-Stage Execution Flow

All agents follow this standardized workflow:

| Stage | Name | Purpose |
|-------|------|---------|
| 0 | Initialize Early Metadata | Create `.return-meta.json` BEFORE substantive work |
| 1 | Parse Delegation Context | Extract task_context, session_id, metadata_file_path |
| 2 | Load/Parse Input | Read research focus or implementation plan |
| 3 | Find Resume Point | (Implementation only) Scan phases for incomplete |
| 4 | Execute Core Work | Perform research searches or file operations |
| 5 | Run Verification | Domain-specific validation |
| 6 | Create Artifact | Research report or implementation summary |
| 6a | Generate Completion Data | (Implementation only) completion_summary, claudemd_suggestions |
| 7 | Write Metadata File | Final status to .return-meta.json |
| 8 | Return Brief Summary | 3-6 bullet points, NOT JSON |

### 2. Context Index System

#### Directory Structure

```
.claude/context/
├── README.md              # Context overview
├── index.md               # Master index for lazy loading
├── core/                  # Framework patterns
│   ├── architecture/      # System design (component-checklist.md, etc.)
│   ├── checkpoints/       # Checkpoint model (gate-in, gate-out, commit)
│   ├── formats/           # Artifact formats (report, plan, summary)
│   ├── orchestration/     # Delegation and routing
│   ├── patterns/          # Behavior patterns (anti-stop, lifecycle)
│   ├── standards/         # Status markers, documentation, testing
│   ├── templates/         # Agent/skill templates
│   └── workflows/         # Review, task breakdown, sessions
└── project/               # Domain-specific knowledge
    ├── meta/              # Meta-builder patterns
    ├── neovim/            # Neovim configuration
    │   ├── README.md      # Overview and loading strategy
    │   ├── domain/        # Core concepts (lua-patterns, neovim-api)
    │   ├── patterns/      # Implementation patterns (plugin-spec, keymap)
    │   ├── standards/     # Coding conventions (lua-style-guide)
    │   ├── tools/         # Tool guides (lazy-nvim, telescope)
    │   └── templates/     # Boilerplate (plugin-template, ftplugin)
    ├── typst/             # Typst document context
    └── repo/              # General project context
```

#### Agent Context Loading Pattern

Agents declare context references with loading conditions:

```markdown
## Context References

Load these on-demand using @-references:

**Always Load**:
- `@.claude/context/core/formats/return-metadata-file.md` - Metadata file schema

**Load When Creating Report**:
- `@.claude/context/core/formats/report-format.md` - Research report structure

**Load for {Domain} Research**:
- `@.claude/context/project/{domain}/README.md` - Domain overview
- `@.claude/context/project/{domain}/domain/{concept}.md` - Core concepts
```

#### Index File Role (index.md)

The index file serves as a quick-reference map for context loading:
- Categorizes files by purpose (checkpoints, orchestration, patterns, etc.)
- Indicates approximate token counts per file
- Specifies when to load each file
- Documents consolidation status

### 3. Skill-to-Agent Delegation Pattern

From `.claude/CLAUDE.md`:

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-researcher | general-research-agent | General web/codebase research |
| skill-implementer | general-implementation-agent | General file implementation |
| skill-neovim-research | neovim-research-agent | Neovim/plugin research |
| skill-neovim-implementation | neovim-implementation-agent | Neovim configuration implementation |
| skill-latex-implementation | latex-implementation-agent | LaTeX document implementation |

Skills are thin wrappers that:
1. Validate input (task exists, status allows operation)
2. Update status (preflight)
3. Prepare delegation context
4. Invoke agent via Task tool (NOT Skill tool)
5. Read metadata file
6. Update status (postflight)
7. Link artifacts
8. Git commit
9. Cleanup
10. Return brief summary

### 4. Recommended Context Structure for Python/Z3

#### Directory Layout

```
.claude/context/project/python/
├── README.md                    # Overview and loading strategy
├── domain/
│   ├── model-checker-api.md     # ModelChecker package structure, core classes
│   ├── theory-lib-patterns.md   # Theory library conventions (semantic.py, operators.py)
│   └── z3-integration.md        # How model-checker uses Z3 (ForAll, Exists, etc.)
├── patterns/
│   ├── semantic-evaluation.md   # Truth-maker semantic patterns
│   ├── operator-definition.md   # How to define new operators
│   └── constraint-generation.md # Z3 constraint building patterns
├── standards/
│   └── code-style.md            # Python conventions from CLAUDE.md
└── templates/
    ├── operator-template.md     # Template for new operator
    └── test-template.md         # Template for pytest tests

.claude/context/project/z3/
├── README.md                    # Z3 overview and ModelChecker usage
├── domain/
│   ├── z3-api.md                # Core Z3 API (Bool, Int, Real, BitVec, etc.)
│   ├── smt-lib-syntax.md        # SMT-LIB2 format reference
│   └── tactics.md               # Common Z3 tactics (simplify, solve, etc.)
├── patterns/
│   ├── quantifier-patterns.md   # ForAll, Exists patterns
│   ├── bitvector-patterns.md    # BitVec operations (model-checker uses extensively)
│   └── constraint-debugging.md  # Debugging unsat cores, model extraction
└── templates/
    └── constraint-template.md   # Z3 constraint snippet template
```

#### Content Recommendations

**python/domain/model-checker-api.md**:
- Package structure (`model_checker/theory_lib/logos/`)
- Key classes: `LogosSemantics`, `LogosProposition`, `LogosModel`
- Import patterns (relative imports within packages)
- Type hints and protocols used

**python/domain/theory-lib-patterns.md**:
- Standard files per subtheory: `semantic.py`, `operators.py`, `examples.py`
- Operator registration pattern
- Example structure (`get_examples()` function)

**python/patterns/semantic-evaluation.md**:
- Truthmaker semantic evaluation patterns
- Verifier/falsifier computation
- Bilateral evaluation methods

**z3/domain/z3-api.md**:
- Core types: `Bool`, `Int`, `Real`, `BitVec`, `Array`
- Solver usage: `Solver()`, `add()`, `check()`, `model()`
- Quantifiers: `ForAll`, `Exists`
- Simplification: `simplify()`

**z3/patterns/bitvector-patterns.md**:
- `BitVec` creation and operations
- Conversion utilities (`bitvec_to_substates`, `int_to_binary`)
- Part-whole state representation

### 5. Agent Definition Recommendations

#### python-research-agent.md

```markdown
## Allowed Tools

### File Operations
- Read - Read Python source files, documentation, context documents
- Write - Create research report artifacts and metadata file
- Edit - Modify existing files if needed
- Glob - Find Python files by pattern (*.py)
- Grep - Search file contents

### Build Tools
- Bash - Run verification commands:
  - `PYTHONPATH=Code/src pytest Code/tests/ -v` - Run tests
  - `python -m py_compile file.py` - Check syntax
  - `mypy file.py` - Type checking (if available)

### Web Tools
- WebSearch - Search for Python/Z3 documentation
- WebFetch - Retrieve specific documentation pages

### MCP Tools (User Scope Required)
- context7 - Documentation lookup
- mcp_python_toolbox - Python analysis (if configured)

## Context References

**Always Load**:
- `@.claude/context/core/formats/return-metadata-file.md`

**Load for Python Research**:
- `@.claude/context/project/python/README.md` - Python context overview
- `@.claude/context/project/python/domain/model-checker-api.md` - ModelChecker structure
- `@.claude/context/project/python/domain/theory-lib-patterns.md` - Theory patterns
```

#### z3-research-agent.md

```markdown
## Allowed Tools

### File Operations
- Read, Write, Edit, Glob, Grep (same as Python agent)

### Build Tools
- Bash - Run Z3 verification:
  - `python -c "import z3; print(z3.get_version())"` - Check Z3 version
  - `PYTHONPATH=Code/src pytest Code/tests/ -k "z3" -v` - Run Z3-related tests

### Web Tools
- WebSearch, WebFetch

### MCP Tools
- context7 - Z3 documentation lookup
- z3_mcp - Z3 constraint solving (if configured)

## Context References

**Always Load**:
- `@.claude/context/core/formats/return-metadata-file.md`

**Load for Z3 Research**:
- `@.claude/context/project/z3/README.md` - Z3 context overview
- `@.claude/context/project/z3/domain/z3-api.md` - Z3 API reference
- `@.claude/context/project/python/domain/z3-integration.md` - ModelChecker Z3 patterns
```

#### python-implementation-agent.md

```markdown
## Allowed Tools

### File Operations
- Read, Write, Edit, Glob, Grep

### Build/Verification Tools
- Bash - Python development commands:
  - `PYTHONPATH=Code/src pytest Code/tests/ -v` - Full test suite
  - `PYTHONPATH=Code/src pytest {test_file} -v` - Specific tests
  - `python -m py_compile {file}` - Syntax check
  - `./dev_cli.py examples.py` - Run examples

## Context References

**Always Load**:
- `@.claude/context/core/formats/return-metadata-file.md`

**Load for Implementation**:
- `@.claude/context/project/python/patterns/operator-definition.md`
- `@.claude/context/project/python/patterns/semantic-evaluation.md`
- `@.claude/context/project/python/standards/code-style.md`
```

### 6. Language Routing Extension

Update `.claude/CLAUDE.md` Language-Based Routing table:

| Language | Research Tools | Implementation Tools |
|----------|----------------|---------------------|
| `python` | WebSearch, WebFetch, Read, context7 | Read, Write, Edit, Bash (pytest, mypy), mcp_python_toolbox |
| `z3` | WebSearch, WebFetch, Read, context7 | Read, Write, Edit, Bash (pytest), z3_mcp |

Add to Skill-to-Agent Mapping:

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-python-research | python-research-agent | Python/ModelChecker research |
| skill-python-implementation | python-implementation-agent | Python code implementation |
| skill-z3-research | z3-research-agent | Z3/SMT research |
| skill-z3-implementation | z3-implementation-agent | Z3 constraint implementation |

## Decisions

1. **Follow existing 8-stage agent pattern**: All new agents use the standardized execution flow with early metadata, context loading, and brief text returns
2. **Create project/python/ and project/z3/ context directories**: Match neovim/ and typst/ patterns with README, domain/, patterns/, standards/, templates/ subdirectories
3. **Extract patterns from existing logos code**: Use semantic.py, operators.py as source material for context files
4. **MCP tools as optional enhancement**: Agents function with standard tools; MCP provides additional capabilities when configured in user scope
5. **Separate research and implementation agents**: Maintains focused tool access and context loading

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Context files become stale | Medium | Low | Link to source files; update when logos code changes |
| MCP unavailable to subagents | High | Medium | Design agents to work without MCP; MCP is enhancement |
| Excessive context loading | Low | Medium | Use lazy loading with specific @-references per task type |
| Agent proliferation | Low | Low | Consider combined python-z3-agent if patterns converge |

## Implementation Recommendations

### Phase 1: Context File Creation

1. Create `.claude/context/project/python/` directory structure
2. Create `.claude/context/project/z3/` directory structure
3. Extract patterns from `Code/src/model_checker/theory_lib/logos/semantic.py`
4. Document Z3 API patterns used in model-checker

### Phase 2: Agent Definition

1. Create `python-research-agent.md` following general-research-agent pattern
2. Create `z3-research-agent.md` following general-research-agent pattern
3. Create `python-implementation-agent.md` following general-implementation-agent pattern
4. Create `z3-implementation-agent.md` following general-implementation-agent pattern

### Phase 3: Skill Integration

1. Create thin wrapper skills for each agent
2. Update CLAUDE.md language routing table
3. Update index.md with new context files

### Phase 4: Verification

1. Test research workflow with sample task
2. Test implementation workflow with simple change
3. Verify context loading works correctly
4. Validate MCP integration (if configured)

## Appendix

### Files Examined

#### Agents
- `.claude/agents/general-research-agent.md` - Reference pattern for research agents
- `.claude/agents/general-implementation-agent.md` - Reference pattern for implementation agents
- `.claude/agents/neovim-research-agent.md` - Domain-specific research example
- `.claude/agents/neovim-implementation-agent.md` - Domain-specific implementation example
- `.claude/agents/latex-implementation-agent.md` - Another domain-specific example

#### Context
- `.claude/context/index.md` - Master context index
- `.claude/context/project/neovim/README.md` - Domain context organization example
- `.claude/context/project/repo/project-overview.md` - Project structure documentation
- `.claude/context/core/templates/subagent-template.md` - Agent template reference

#### Skills
- `.claude/skills/skill-researcher/SKILL.md` - Skill-to-agent delegation pattern
- `.claude/skills/skill-implementer/SKILL.md` - Implementation skill pattern

#### ModelChecker Source
- `Code/src/model_checker/theory_lib/logos/semantic.py` - Logos semantic framework
- `Code/src/model_checker/theory_lib/logos/README.md` - Logos theory overview

### Key Pattern Examples

#### Context Reference Declaration (from neovim-research-agent)

```markdown
## Context References

Load these on-demand using @-references:

**Always Load**:
- `@.claude/context/core/formats/return-metadata-file.md` - Metadata file schema

**Load When Creating Report**:
- `@.claude/context/core/formats/report-format.md` - Research report structure

**Load for Neovim Research**:
- `@.claude/context/project/neovim/README.md` - Neovim context overview
- `@.claude/context/project/neovim/domain/neovim-api.md` - vim.* API patterns
- `@.claude/context/project/neovim/domain/plugin-ecosystem.md` - Plugin overview
```

#### Early Metadata Pattern (Stage 0)

```json
{
  "status": "in_progress",
  "started_at": "{ISO8601 timestamp}",
  "artifacts": [],
  "partial_progress": {
    "stage": "initializing",
    "details": "Agent started, parsing delegation context"
  },
  "metadata": {
    "session_id": "{from delegation context}",
    "agent_type": "{agent-name}",
    "delegation_depth": 1,
    "delegation_path": ["orchestrator", "{operation}", "{agent-name}"]
  }
}
```

#### Domain Verification Commands (from implementation agents)

```bash
# Neovim
nvim --headless -c "lua require('plugins.newplugin')" -c "q"
nvim --headless -c "checkhealth" -c "q"

# LaTeX
latexmk -pdf -interaction=nonstopmode document.tex
grep -A 2 "^!" document.log  # Check for errors

# Python (ModelChecker)
PYTHONPATH=Code/src pytest Code/tests/ -v
./dev_cli.py examples/my_example.py
```
