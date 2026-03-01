# Research Report: Task #6

**Task**: 6 - Identify Python and Z3 MCP servers for Logos theory implementation
**Started**: 2026-03-01T00:00:00Z
**Completed**: 2026-03-01T00:30:00Z
**Effort**: 2-4 hours (implementation)
**Dependencies**: None
**Sources/Inputs**: WebSearch, Codebase analysis, MCP documentation
**Artifacts**: This research report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Z3 MCP servers exist**: Two mature implementations (z3_mcp by javergar, mcp-solver by szeider) provide Z3/SMT capabilities via MCP
- **Python tooling available**: mcp_python_toolbox provides comprehensive Python development tools; Python REPL servers enable code execution
- **Context7 MCP**: Provides live documentation lookup for libraries and frameworks
- **Subagent scope limitation**: Project-scoped MCP servers (`.mcp.json`) are not accessible to subagents; user-scope (`~/.claude.json`) required
- **Recommended approach**: Create Python and Z3 research/implementation agents that leverage user-scope MCP servers

## Context & Scope

### Research Questions

1. What MCP servers exist for Python development (linting, type checking, code execution)?
2. What MCP servers exist for Z3 theorem proving and SMT solving?
3. How does Context7 MCP work for documentation lookup?
4. How can these tools be integrated into the .claude/ agent system?

### Project Context

The ModelChecker's Logos theory includes:
- **First-Order Subtheory**: Planned extension for quantification, lambda abstraction, and first-order identity (currently documentation-only)
- **Spatial Subtheory**: Planned extension for hyperintensional spatial reasoning with state-valued metrics (documentation-only)

Both subtheories will require:
- Z3 constraint generation and solving
- Python code for semantic evaluation
- Parser extensions for new syntax

## Findings

### Z3 MCP Servers

#### 1. z3_mcp (javergar)

**Repository**: [https://github.com/javergar/z3_mcp](https://github.com/javergar/z3_mcp)

**Capabilities**:
- Constraint satisfaction problem solving
- Relationship analysis with Z3
- Functional programming abstractions over Z3
- MCP protocol exposure for AI assistants

**Installation**:
```bash
git clone https://github.com/javergar/z3_mcp.git
cd z3_mcp
uv pip install -e .
```

**Claude Code Configuration** (user scope):
```json
{
  "mcpServers": {
    "z3-solver": {
      "command": "uv",
      "args": [
        "--directory", "/path/to/z3_mcp",
        "run", "z3_poc/server/main.py"
      ]
    }
  }
}
```

**Tools Exposed**:
- `simple_constraint_solver` - Basic constraint solving
- `simple_relationship_analyzer` - Analyze relationships
- `solve_constraint_problem` - Full constraint problem solving
- `analyze_relationships` - Full relationship analysis

#### 2. mcp-solver (szeider)

**Repository**: [https://github.com/szeider/mcp-solver](https://github.com/szeider/mcp-solver)

**Capabilities**:
- Z3 SMT solving with rich type system (booleans, integers, reals, bitvectors, arrays)
- MiniZinc constraint optimization (alternative mode)
- PySAT SAT solving (alternative mode)
- ReAct agent framework for translating natural language to constraints

**Installation**:
```bash
git clone https://github.com/szeider/mcp-solver.git
cd mcp-solver
uv venv
source .venv/bin/activate
uv pip install -e ".[all]"  # Install all solvers including Z3
```

**Claude Code Configuration**:
```bash
claude mcp add-json "mcp-solver-z3" '{"command":"mcp-solver-z3","args":[]}'
```

**Key Features**:
- Prototype status (use with caution)
- Academic research backing (SAT 2025 paper)
- Supports constraint optimization beyond satisfiability

#### 3. Official Z3 MCP (Z3Prover)

**Location**: `z3/src/api/z3mcp.py` in Z3 repository

**Status**: Minimal MCP server included with Z3 source
**Recommendation**: Use community implementations (z3_mcp or mcp-solver) for better feature support

### Python Development MCP Servers

#### 1. mcp_python_toolbox (gianlucamazza)

**Repository**: [https://github.com/gianlucamazza/mcp_python_toolbox](https://github.com/gianlucamazza/mcp_python_toolbox)

**Capabilities**:
- Code analysis and formatting (Black/PEP8)
- Linting with Pylint
- Project management with virtual environments
- Dependency handling
- Safe code execution
- File operations

**Installation**:
```bash
git clone https://github.com/gianlucamazza/mcp_python_toolbox.git
cd mcp_python_toolbox
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

**Running**:
```bash
# Current directory as workspace
python -m mcp_python_toolbox

# Specific workspace
python -m mcp_python_toolbox --workspace /path/to/project
```

**Claude Desktop Configuration**:
```json
{
  "mcpServers": {
    "python-toolbox": {
      "command": "python",
      "args": ["-m", "mcp_python_toolbox", "--workspace", "/home/benjamin/Projects/ModelChecker"]
    }
  }
}
```

#### 2. python-lft-mcp (Agent-Hellboy)

**Repository**: [https://github.com/Agent-Hellboy/python-lft-mcp](https://github.com/Agent-Hellboy/python-lft-mcp)

**Capabilities**:
- ruff linting
- black formatting
- pytest execution
- mypy type checking
- pylint analysis
- LLM-optimized tool integration

**Use Case**: Comprehensive Python development workflow automation

#### 3. Python REPL MCP Servers

Multiple implementations exist for Python code execution:

| Server | Features |
|--------|----------|
| lyuhau/python-repl | REPL execution, shell commands |
| yzfly/mcp-python-interpreter | File I/O, code execution, workflow management |
| shibing624/python-code-interpreter | Isolated environments, package installation |

**Common Capabilities**:
- Persistent sessions with variable retention
- Package installation (pip)
- File operations
- Output capture

### Context7 MCP (Documentation Lookup)

**Publisher**: Upstash
**Purpose**: Live, version-specific documentation lookup for libraries and frameworks

**Installation for Claude Code**:
```bash
# User scope (all projects)
claude mcp add --scope user context7 -- npx -y @upstash/context7-mcp --api-key YOUR_API_KEY

# HTTP transport alternative
claude mcp add --scope user --header "CONTEXT7_API_KEY: YOUR_API_KEY" --transport http context7 https://mcp.context7.com/mcp
```

**Manual Configuration** (`~/.claude.json`):
```json
{
  "mcpServers": {
    "context7": {
      "command": "npx",
      "args": ["-y", "@upstash/context7-mcp", "--api-key", "YOUR_API_KEY"]
    }
  }
}
```

**Usage**:
- Include `use context7` in prompts to activate documentation lookup
- Fetches up-to-date code examples and docs
- Intelligent project ranking
- Customizable token limits

**API Key**:
- Optional for basic usage
- Recommended for higher rate limits
- Obtain from [context7.com/dashboard](https://context7.com/dashboard)

### Formal Verification MCP Servers (Related)

For reference, other formal verification MCP servers exist:

| Server | Proof System | Capabilities |
|--------|-------------|--------------|
| mcp-rocq | Coq | Dependent type checking, inductive types, property proving |
| mcp-logic | Prover9/Mace4 | Automated theorem proving, model checking |
| dafny-verifier | Dafny | Program verification |

These could be relevant for future Lean formalization integration.

## Integration Patterns

### MCP Server Scope Issue

**Critical Limitation**: Custom subagents (spawned via Task tool) cannot access project-scoped MCP servers defined in `.mcp.json`. Instead, they hallucinate results.

**Documented in**: `.claude/README.md` (MCP Server Configuration section)

**Workaround**: Configure MCP servers in user scope (`~/.claude.json`) instead of project scope.

**Tracked Issues**:
- [anthropics/claude-code#13898](https://github.com/anthropics/claude-code/issues/13898)
- [anthropics/claude-code#14496](https://github.com/anthropics/claude-code/issues/14496)
- [anthropics/claude-code#13605](https://github.com/anthropics/claude-code/issues/13605)

### Agent Integration Architecture

#### Proposed Structure

```
.claude/agents/
├── python-research-agent.md      # NEW: Python development research
├── python-implementation-agent.md # NEW: Python implementation with MCP tools
├── z3-research-agent.md          # NEW: Z3/SMT research
└── z3-implementation-agent.md    # NEW: Z3 constraint implementation

.claude/skills/
├── skill-python-research/SKILL.md     # NEW: Routes to python-research-agent
├── skill-python-implementation/SKILL.md # NEW: Routes to python-implementation-agent
├── skill-z3-research/SKILL.md         # NEW: Routes to z3-research-agent
└── skill-z3-implementation/SKILL.md   # NEW: Routes to z3-implementation-agent
```

#### Language Routing Extension

Update `.claude/CLAUDE.md` language routing table:

| Language | Research Tools | Implementation Tools |
|----------|----------------|---------------------|
| `python` | WebSearch, Context7 MCP, Read | Read, Write, Edit, mcp_python_toolbox, Python REPL |
| `z3` | WebSearch, Context7 MCP, Read | Read, Write, Edit, z3_mcp or mcp-solver |

### Recommended MCP Configuration

For user scope (`~/.claude.json`):

```json
{
  "mcpServers": {
    "context7": {
      "command": "npx",
      "args": ["-y", "@upstash/context7-mcp"]
    },
    "python-toolbox": {
      "command": "python",
      "args": ["-m", "mcp_python_toolbox", "--workspace", "/home/benjamin/Projects/ModelChecker"]
    },
    "z3-solver": {
      "command": "uv",
      "args": ["--directory", "/path/to/z3_mcp", "run", "z3_poc/server/main.py"]
    }
  }
}
```

## Decisions

1. **Use user-scope MCP configuration**: Required for subagent access
2. **Prefer z3_mcp over mcp-solver**: Simpler setup, more focused on core Z3 capabilities
3. **Use mcp_python_toolbox for Python**: Most comprehensive toolset
4. **Include Context7**: Valuable for documentation lookup across all languages
5. **Create language-specific agents**: Separate Python and Z3 agents for focused expertise

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| MCP scope limitation persists | High | Medium | Use user-scope configuration; monitor issues for platform fix |
| z3_mcp instability | Medium | Medium | Fallback to direct Z3 Python API in agent code |
| Context7 rate limits | Low | Low | API key provides higher limits; graceful degradation |
| MCP server startup latency | Medium | Low | Lazy initialization; connection pooling |

## Implementation Recommendations

### Phase 1: MCP Server Setup (Prerequisites)

1. Install z3_mcp locally:
   ```bash
   cd ~/Tools  # Or preferred location
   git clone https://github.com/javergar/z3_mcp.git
   cd z3_mcp && uv pip install -e .
   ```

2. Install mcp_python_toolbox:
   ```bash
   cd ~/Tools
   git clone https://github.com/gianlucamazza/mcp_python_toolbox.git
   cd mcp_python_toolbox && pip install -r requirements.txt
   ```

3. Configure user-scope MCP (`~/.claude.json`)

4. Restart Claude Code

### Phase 2: Agent Creation

1. Create `python-research-agent.md` with Context7 integration for library docs
2. Create `python-implementation-agent.md` with mcp_python_toolbox for development
3. Create `z3-research-agent.md` with Context7 for Z3 documentation
4. Create `z3-implementation-agent.md` with z3_mcp for constraint solving

### Phase 3: Skill Integration

1. Create thin wrapper skills for each agent
2. Update language routing in CLAUDE.md
3. Add `python` and `z3` to supported languages

### Phase 4: First-Order/Spatial Implementation

Apply the new agents to:
1. First-order subtheory parser extensions
2. First-order semantic evaluation with Z3
3. Spatial subtheory metric function implementation
4. Triangle inequality constraint verification

## Appendix

### Search Queries Used

1. "MCP Model Context Protocol Python development server 2026"
2. "MCP Model Context Protocol Z3 theorem prover SMT solver server 2026"
3. "context7 MCP server documentation lookup Model Context Protocol 2026"
4. "Python MCP server pyright mypy linting type checking development tools 2026"
5. "Python REPL MCP server execute code interpreter Model Context Protocol"
6. "Claude Code MCP subagent access project scope user scope configuration"

### References

#### Z3 MCP Servers
- [javergar/z3_mcp](https://github.com/javergar/z3_mcp) - Z3 with functional programming abstractions
- [szeider/mcp-solver](https://github.com/szeider/mcp-solver) - Multi-solver MCP (Z3, MiniZinc, PySAT)
- [Z3 Theorem Prover with Functional Programming MCP Server](https://mcp.so/server/z3_mcp/javergar)

#### Python MCP Servers
- [gianlucamazza/mcp_python_toolbox](https://github.com/gianlucamazza/mcp_python_toolbox)
- [Agent-Hellboy/python-lft-mcp](https://github.com/Agent-Hellboy/python-lft-mcp)
- [yzfly/mcp-python-interpreter](https://github.com/yzfly/mcp-python-interpreter)

#### Context7
- [Context7 MCP - Upstash](https://upstash.com/blog/context7-mcp)
- [upstash/context7-mcp NPM](https://www.npmjs.com/package/@upstash/context7-mcp)

#### Claude Code MCP Documentation
- [Connect Claude Code to tools via MCP](https://code.claude.com/docs/en/mcp)
- [Custom Subagents Cannot Access Project-Scoped MCP Servers](https://github.com/anthropics/claude-code/issues/13898)
