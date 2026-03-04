# Neovim Configuration Management System (OpenCode)

Task management and agent orchestration for Neovim configuration maintenance. For comprehensive documentation, see @.opencode/README.md.

## Quick Reference

- **Task List**: @specs/TODO.md
- **Machine State**: @specs/state.json
- **Error Tracking**: @specs/errors.json
- **Architecture**: @.opencode/context/core/architecture/system-overview.md

## Project Structure

```
nvim/                     # Neovim configuration
  lua/                   # Lua modules
    neotex/              # Main configuration namespace
      core/              # Core configuration
      plugins/           # Plugin specifications
      utils/             # Utility functions
  after/                 # Filetype-specific overrides
    ftplugin/            # Filetype plugins
  plugin/                # Auto-loaded plugins
  init.lua               # Entry point
docs/                    # Project documentation
specs/                   # Task management artifacts
.opencode/               # OpenCode configuration
```

## Task Management

### Status Markers
- `[NOT STARTED]` - Initial state
- `[RESEARCHING]` -> `[RESEARCHED]` - Research phase
- `[PLANNING]` -> `[PLANNED]` - Planning phase
- `[IMPLEMENTING]` -> `[COMPLETED]` - Implementation phase
- `[BLOCKED]`, `[ABANDONED]`, `[PARTIAL]`, `[EXPANDED]` - Terminal/exception states

### Artifact Paths
```
specs/{NNN}_{SLUG}/
  reports/research-{NNN}.md
  plans/implementation-{NNN}.md
  summaries/implementation-summary-{DATE}.md
```
`{NNN}` = 3-digit padded number (e.g., `001`), `{DATE}` = YYYYMMDD. Task numbers in text use unpadded format.

### Language-Based Routing

| Language | Research Tools | Implementation Tools |
|----------|----------------|---------------------|
| `neovim` | WebSearch, WebFetch, Read | Read, Write, Edit, Bash (nvim --headless) |
| `lean` | lean_leansearch, lean_loogle, lean_leanfinder | lean_goal, lean_hover_info, lean_multi_attempt |
| `latex` | skill-latex-research (LaTeX context) | Read, Write, Edit, Bash (pdflatex) |
| `typst` | skill-typst-research (Typst context) | Read, Write, Edit, Bash (typst compile) |
| `general` | WebSearch, WebFetch, Read | Read, Write, Edit, Bash |
| `meta` | Read, Grep, Glob | Write, Edit |

## Command Reference

All commands use checkpoint-based execution: GATE IN (preflight) -> DELEGATE (skill/agent) -> GATE OUT (postflight) -> COMMIT.

| Command | Usage | Description |
|---------|-------|-------------|
| `/task` | `/task "Description"` | Create task |
| `/task` | `/task --recover N`, `--expand N`, `--sync`, `--abandon N` | Manage tasks |
| `/research` | `/research N [focus]` | Research task, route by language |
| `/plan` | `/plan N` | Create implementation plan |
| `/implement` | `/implement N` | Execute plan, resume from incomplete phase |
| `/revise` | `/revise N` | Create new plan version |
| `/review` | `/review` | Analyze codebase |
| `/todo` | `/todo` | Archive completed/abandoned tasks, sync repository metrics |
| `/errors` | `/errors` | Analyze error patterns, create fix plans |
| `/meta` | `/meta` | System builder for .opencode/ changes |
| `/learn` | `/learn [PATH...]` | Scan for FIX:/NOTE:/TODO: tags |
| `/refresh` | `/refresh [--dry-run] [--force]` | Clean orphaned processes and old files |
| `/convert` | `/convert FILE --to FORMAT` | Convert documents between formats |

## State Synchronization

TODO.md and state.json must stay synchronized. Update state.json first (machine state), then TODO.md (user-facing).

### state.json Structure
```json
{
  "next_project_number": 1,
  "active_projects": [{
    "project_number": 1,
    "project_name": "task_slug",
    "status": "planned",
    "language": "neovim",
    "completion_summary": "Required when status=completed"
  }],
  "repository_health": {
    "last_assessed": "ISO8601 timestamp",
    "status": "healthy"
  }
}
```

### Completion Workflow
- Non-meta tasks: `completion_summary` + optional `roadmap_items` -> /todo annotates ROAD_MAP.md
- Meta tasks: `completion_summary` + `claudemd_suggestions` -> /todo displays for user review

## Git Commit Conventions

Format: `task {N}: {action}` with session ID in body.
```
task 1: complete research

Session: sess_1736700000_abc123

Co-Authored-By: OpenCode <noreply@opencode.ai>
```

Standard actions: `create`, `complete research`, `create implementation plan`, `phase {P}: {name}`, `complete implementation`.

## Skill-to-Agent Mapping

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-neovim-research | neovim-research-agent | Neovim/plugin research |
| skill-neovim-implementation | neovim-implementation-agent | Neovim configuration implementation |
| skill-lean-research | lean-research-agent | Lean 4/Mathlib research |
| skill-lean-implementation | lean-implementation-agent | Lean proof implementation |
| skill-logic-research | logic-research-agent | Mathematical logic research |
| skill-math-research | math-research-agent | Mathematical foundations research |
| skill-latex-research | latex-research-agent | LaTeX documentation research |
| skill-researcher | general-research-agent | General web/codebase research |
| skill-planner | planner-agent | Implementation plan creation |
| skill-implementer | general-implementation-agent | General file implementation |
| skill-latex-implementation | latex-implementation-agent | LaTeX document implementation |
| skill-typst-implementation | typst-implementation-agent | Typst document implementation |
| skill-typst-research | typst-research-agent | Typst documentation research |
| skill-meta | meta-builder-agent | System building and task creation |
| skill-filetypes | filetypes-router-agent | File format conversion and manipulation |
| skill-status-sync | (direct execution) | Atomic status updates |
| skill-refresh | (direct execution) | Process and file cleanup |
| skill-git-workflow | (direct execution) | Scoped git commits for task operations |
| skill-learn | (direct execution) | Scan for FIX:/NOTE:/TODO: tags |
| skill-orchestrator | (direct execution) | Route commands to workflows |

## Rules References

Core rules (auto-applied by file path):
- @.opencode/rules/state-management.md - Task state patterns (specs/**)
- @.opencode/rules/git-workflow.md - Commit conventions
- @.opencode/rules/neovim-lua.md - Neovim Lua development (lua/**/*.lua, after/**/*.lua)
- @.opencode/rules/error-handling.md - Error recovery (.opencode/**)
- @.opencode/rules/artifact-formats.md - Report/plan formats (specs/**)
- @.opencode/rules/workflows.md - Command lifecycle (.opencode/**)

## Context Imports

Domain knowledge (load as needed):
- @.opencode/context/project/neovim/domain/neovim-api.md
- @.opencode/context/project/neovim/patterns/plugin-spec.md
- @.opencode/context/project/neovim/tools/lazy-nvim-guide.md
- @.opencode/context/project/repo/project-overview.md

## Error Handling

- **On failure**: Keep task in current status, log to errors.json, preserve partial progress
- **On timeout**: Mark phase [PARTIAL], next /implement resumes
- **Git failures**: Non-blocking (logged, not fatal)

## jq Command Safety

Claude Code Issue #1132 causes jq parse errors when using `!=` operator (escaped as `\!=`).

**Safe pattern**: Use `select(.type == "X" | not)` instead of `select(.type != "X")`

```bash
# SAFE - use "| not" pattern
select(.type == "plan" | not)

# UNSAFE - gets escaped as \!=
select(.type != "plan")
```

Full documentation: @.opencode/context/core/patterns/jq-escaping-workarounds.md

## Important Notes

- Update status BEFORE starting work (preflight) and AFTER completing (postflight)
- state.json = machine truth, TODO.md = user visibility
- All skills use lazy context loading via @-references
- Session ID format: `sess_{timestamp}_{random}` - generated at GATE IN, included in commits

<!-- SECTION: extension_oc_z3 -->
## Z3 Extension

This project includes Z3 SMT solver development support via the z3 extension.

### Language Routing

| Language | Research Tools | Implementation Tools |
|----------|----------------|---------------------|
| `z3` | WebSearch, WebFetch, Read | Read, Write, Edit, Bash (python, z3) |

### Skill-Agent Mapping

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-z3-research | z3-research-agent | Z3/SMT research |
| skill-z3-implementation | z3-implementation-agent | Z3 constraint implementation |

### Z3 Patterns

- Use `z3.Solver()` for constraint solving
- BitVec for finite-domain state representation
- Incremental solving with `push()`/`pop()` for efficiency
- Use `simplify()` on expressions before adding to solver

### Common Operations

- Model checking: Define constraints, check `sat`, extract model
- Theory exploration: Use quantifiers sparingly, prefer ground terms
- Optimization: Use `z3.Optimize()` for objective functions

<!-- END_SECTION: extension_oc_z3 -->

<!-- SECTION: extension_oc_web -->
## Web Extension

This project includes web development support via the web extension.

### Language Routing

| Language | Research Tools | Implementation Tools |
|----------|----------------|---------------------|
| `web` | WebSearch, WebFetch, Read | Read, Write, Edit, Bash (pnpm build/check) |

### Skill-Agent Mapping

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-web-research | web-research-agent | Astro/Tailwind/Cloudflare research |
| skill-web-implementation | web-implementation-agent | Web (Astro/Tailwind/TypeScript) implementation |

### Key Technologies

- **Astro**: Static site generator with islands architecture (v5 stable, v6 notes where relevant)
- **Tailwind CSS v4**: CSS-first configuration with @theme directive
- **TypeScript**: Strict mode with Astro type utilities
- **Cloudflare Pages**: Edge deployment with automatic preview deployments

### Build Verification

```bash
# Development server
pnpm dev

# TypeScript + Astro diagnostics
pnpm check

# Production build
pnpm build

# Preview production build
pnpm preview
```

### Context Categories

- **Domain**: Core framework concepts (Astro, Tailwind v4, Cloudflare, TypeScript)
- **Patterns**: Implementation patterns (components, layouts, content collections, accessibility)
- **Standards**: Coding conventions and targets (style guide, performance, accessibility)
- **Tools**: Tool-specific guides (CLI, deployment, debugging)
- **Templates**: Boilerplate templates (pages, components)

<!-- END_SECTION: extension_oc_web -->

<!-- SECTION: extension_oc_typst -->
## Typst Extension

This project includes Typst document development support via the typst extension.

### Language Routing

| Language | Research Tools | Implementation Tools |
|----------|----------------|---------------------|
| `typst` | WebSearch, WebFetch, Read | Read, Write, Edit, Bash (typst compile) |

### Skill-Agent Mapping

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-typst-research | typst-research-agent | Typst documentation research |
| skill-typst-implementation | typst-implementation-agent | Typst document implementation |

### Typst vs LaTeX

- Typst uses single-pass compilation (faster)
- Modern scripting syntax with `#` prefix
- Built-in bibliography management
- Simpler package import with `#import`

### Common Operations

- Compile: `typst compile main.typ`
- Watch: `typst watch main.typ`
- Format: Use consistent indentation for readability
- Diagrams: Use `fletcher` package for commutative diagrams

<!-- END_SECTION: extension_oc_typst -->

<!-- SECTION: extension_oc_python -->
## Python Extension

This project includes Python development support via the python extension.

### Language Routing

| Language | Research Tools | Implementation Tools |
|----------|----------------|---------------------|
| `python` | WebSearch, WebFetch, Read | Read, Write, Edit, Bash (python, pytest) |

### Skill-Agent Mapping

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-python-research | python-research-agent | Python/library research |
| skill-python-implementation | python-implementation-agent | Python implementation |

### Testing

- Run tests: `pytest`
- Run specific test: `pytest path/to/test.py::test_function`
- Coverage: `pytest --cov=src`
- Watch mode: `pytest-watch`

### Code Quality

- Type checking: `mypy src/`
- Linting: `ruff check src/`
- Formatting: `ruff format src/`
- All checks: `make lint` or `nox -s lint`

<!-- END_SECTION: extension_oc_python -->

<!-- SECTION: extension_oc_nix -->
## Nix Extension

This project includes NixOS and Home Manager configuration support via the nix extension.

### Language Routing

| Language | Research Tools | Implementation Tools |
|----------|----------------|---------------------|
| `nix` | MCP-NixOS, WebSearch, WebFetch, Read | Read, Write, Edit, Bash (nix flake check, nixos-rebuild, home-manager) |

### Skill-Agent Mapping

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-nix-research | nix-research-agent | NixOS/Home Manager/flakes research with MCP-NixOS |
| skill-nix-implementation | nix-implementation-agent | Nix configuration implementation with verification |

### Key Technologies

- **NixOS**: Declarative Linux distribution with reproducible system configurations
- **Home Manager**: User-level declarative configuration management
- **Nix Flakes**: Reproducible, hermetic package management with lockfiles
- **MCP-NixOS**: Model Context Protocol server for package/option search and validation

### Build Verification

```bash
# Check flake syntax and evaluate outputs
nix flake check

# Show flake outputs
nix flake show

# Build NixOS configuration
nixos-rebuild build --flake .#hostname

# Build Home Manager configuration
home-manager build --flake .#user

# Evaluate specific expression
nix eval .#path
```

### Context Categories

- **Domain**: Core Nix concepts (Nix language, flakes, NixOS modules, Home Manager)
- **Patterns**: Implementation patterns (modules, overlays, derivations)
- **Standards**: Coding conventions (style guide)
- **Tools**: Tool-specific guides (nixos-rebuild, home-manager)

### MCP-NixOS Integration

The MCP-NixOS server provides enhanced package and option validation:

```bash
# Available via MCP tools when configured:
mcp__nixos__nix(action="search", query="pkgname", source="nixpkgs")
mcp__nixos__nix(action="options", query="services.X", source="nixos-options")
mcp__nixos__nix_versions(package="nodejs")
```

Agents gracefully degrade to WebSearch and CLI commands when MCP is unavailable.

<!-- END_SECTION: extension_oc_nix -->

<!-- SECTION: extension_oc_lean -->
## Lean 4 Extension

This project includes Lean 4 theorem prover support via the lean extension.

### Language Routing

| Language | Research Tools | Implementation Tools |
|----------|----------------|---------------------|
| `lean4` | WebSearch, WebFetch, Read, Lean MCP | Read, Write, Edit, Bash (lake), Lean MCP |

### Skill-Agent Mapping

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-lean-research | lean-research-agent | Lean/Mathlib research |
| skill-lean-implementation | lean-implementation-agent | Lean proof implementation |
| skill-lake-repair | lean-implementation-agent | Lake build repair |
| skill-lean-version | (direct execution) | Lean version management |

### MCP Integration

The `lean-lsp` MCP server provides:
- Goal state inspection (`lean_goal`)
- Proof search (`lean_state_search`, `lean_hammer_premise`)
- Mathlib lookup (`lean_loogle`, `lean_leansearch`, `lean_leanfinder`)
- Code actions and diagnostics

### Commands

- `/lake` - Build management and error handling
- `/lean` - Lean-specific proof assistance

<!-- END_SECTION: extension_oc_lean -->

<!-- SECTION: extension_oc_latex -->
## LaTeX Extension

This project includes LaTeX document development support via the latex extension.

### Language Routing

| Language | Research Tools | Implementation Tools |
|----------|----------------|---------------------|
| `latex` | WebSearch, WebFetch, Read | Read, Write, Edit, Bash (pdflatex, latexmk) |

### Skill-Agent Mapping

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-latex-implementation | latex-implementation-agent | LaTeX document implementation |

### VimTeX Integration

- Compile: `:VimtexCompile` (`<leader>lc`)
- View PDF: `:VimtexView` (`<leader>lv`)
- Clean: `:VimtexClean` (`<leader>lk`)
- TOC: `:VimtexTocOpen` (`<leader>li`)

### Document Structure

- Use `\documentclass` appropriate for document type
- Organize with `\input{}` for modular documents
- Use `build/` directory for output files
- Keep `.bib` files organized by project

<!-- END_SECTION: extension_oc_latex -->

<!-- SECTION: extension_oc_formal -->
## Formal Reasoning Extension

Language routing and context for formal mathematical reasoning including logic, mathematics, and physics.

### Language Routing

| Language | Description | Use Cases |
|----------|-------------|-----------|
| `formal` | General formal reasoning | Multi-domain formal tasks |
| `logic` | Mathematical logic | Modal logic, Kripke semantics, proof theory |
| `math` | Mathematics | Algebra, lattice theory, category theory, topology |
| `physics` | Physics | Dynamical systems, formalization |

### Skill-to-Agent Mapping

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-formal-research | formal-research-agent | Multi-domain formal research coordination |
| skill-logic-research | logic-research-agent | Modal logic and Kripke semantics research |
| skill-math-research | math-research-agent | Mathematics research (algebra, lattices, categories) |
| skill-physics-research | physics-research-agent | Physics formalization research |

### Domain Routing

Automatic routing based on task keywords:

**Logic Domain** (triggers logic-research-agent):
- Modal logic, Kripke, accessibility, possible worlds
- Proof theory, sequent calculus, natural deduction
- Completeness, soundness, decidability
- Temporal logic, epistemic logic

**Math Domain** (triggers math-research-agent):
- Lattice, partial order, complete lattice
- Group, ring, field, monoid
- Category, functor, natural transformation
- Topology, metric space, topological space

**Physics Domain** (triggers physics-research-agent):
- Dynamical systems, fixed points, orbits
- Flow, trajectory, ergodic
- Chaos, Lyapunov, bifurcation

### Context Import References

Load context files on-demand:

```
Logic domain:
@.opencode/extensions/formal/context/project/logic/README.md
@.opencode/extensions/formal/context/project/logic/domain/kripke-semantics-overview.md

Math domain:
@.opencode/extensions/formal/context/project/math/README.md
@.opencode/extensions/formal/context/project/math/lattice-theory/lattices.md

Physics domain:
@.opencode/extensions/formal/context/project/physics/README.md
@.opencode/extensions/formal/context/project/physics/dynamical-systems/dynamical-systems.md
```

<!-- END_SECTION: extension_oc_formal -->

<!-- SECTION: extension_oc_filetypes -->
## Filetypes Extension

This project includes comprehensive file format conversion and manipulation via the filetypes extension.

### Skill-Agent Mapping

| Skill | Agent | Purpose |
|-------|-------|---------|
| skill-filetypes | filetypes-router-agent | Format detection and routing to specialized agents |
| skill-filetypes | document-agent | Document format conversion (PDF/DOCX/Markdown) |
| skill-spreadsheet | spreadsheet-agent | Spreadsheet to LaTeX/Typst table conversion |
| skill-presentation | presentation-agent | Presentation extraction and slide generation |

### Supported Conversions

#### Document Conversions (via /convert)

| Source | Target | Primary Tool | Fallback |
|--------|--------|--------------|----------|
| PDF | Markdown | markitdown | pandoc |
| DOCX | Markdown | markitdown | pandoc |
| HTML | Markdown | markitdown | pandoc |
| Images | Markdown | markitdown | - |
| Markdown | PDF | pandoc | typst |

#### Spreadsheet Conversions (via /table)

| Source | Target | Primary Tool | Fallback |
|--------|--------|--------------|----------|
| XLSX | LaTeX table | pandas + openpyxl | xlsx2csv |
| XLSX | Typst table | pandas -> CSV -> Typst csv() | xlsx2csv |
| CSV | LaTeX table | pandas | manual |
| CSV | Typst table | Typst csv() | manual |
| ODS | LaTeX/Typst table | pandas | - |

#### Presentation Conversions (via /slides)

| Source | Target | Primary Tool | Fallback |
|--------|--------|--------------|----------|
| PPTX | Beamer | python-pptx + pandoc | markitdown |
| PPTX | Polylux (Typst) | python-pptx | markitdown |
| PPTX | Touying (Typst) | python-pptx | markitdown |
| Markdown | PPTX | pandoc | - |

### Command Usage

```bash
# Document conversion (format inferred)
/convert document.pdf                    # -> document.md
/convert report.docx notes.md            # -> notes.md
/convert README.md README.pdf            # -> README.pdf

# Spreadsheet to table
/table data.xlsx                         # -> data.tex (LaTeX)
/table data.xlsx output.typ --format typst
/table budget.csv budget.tex --format latex

# Presentation conversion
/slides presentation.pptx                # -> presentation.tex (Beamer)
/slides deck.pptx slides.typ --format polylux
/slides talk.pptx talk.typ --format touying
```

### Prerequisites

Install conversion tools based on your needs:

**Document Conversion**:
- `markitdown`: `pip install markitdown`
- `pandoc`: Install from package manager
- `typst`: Install for Typst output

**Spreadsheet Conversion**:
- `pandas`: `pip install pandas`
- `openpyxl`: `pip install openpyxl` (for XLSX support)
- `xlsx2csv`: `pip install xlsx2csv` (fallback)

**Presentation Conversion**:
- `python-pptx`: `pip install python-pptx`
- `pandoc`: For Beamer output

See `context/project/filetypes/tools/dependency-guide.md` for platform-specific installation instructions.

### NixOS Quick Install

```nix
home.packages = with pkgs; [
  pandoc typst
  (python3.withPackages (ps: with ps; [
    markitdown openpyxl pandas python-pptx xlsx2csv
  ]))
];
```

### Dependency Summary

| Tool | Purpose | Required For |
|------|---------|--------------|
| markitdown | Office to Markdown | /convert |
| pandoc | Universal converter | /convert, /slides |
| typst | Typst compiler | /convert (typst output) |
| pandas | DataFrame handling | /table |
| openpyxl | XLSX support | /table (xlsx) |
| python-pptx | PPTX extraction | /slides |

<!-- END_SECTION: extension_oc_filetypes -->
