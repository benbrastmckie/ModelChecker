
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
