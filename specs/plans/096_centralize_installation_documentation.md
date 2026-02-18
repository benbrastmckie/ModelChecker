# Plan 096: Centralize Installation Documentation

**Status**: COMPLETED
**Created**: 2025-01-12
**Updated**: 2025-01-13
**Completed**: 2025-01-13
**Dependencies**: Plan 094 (Documentation Cross-Linking)

## Executive Summary

This plan enhances and completes the existing Docs/installation/ directory structure, ensuring comprehensive installation documentation with clear guidance for inexperienced users and appropriate links from gateway README files. The focus is on improving existing documentation rather than creating new files. ModelChecker has minimal dependencies (just Python, z3-solver, and networkx), so installation is straightforward and environment management tools like virtual environments or Nix are entirely optional.

## Current State Analysis

### Existing Structure

The Docs/installation/ directory already exists with:
```
installation/
├── README.md                    # Installation hub
├── BASIC_INSTALLATION.md       # Standard pip installation (includes NixOS section)
├── GETTING_STARTED.md          # First steps after installation
├── TROUBLESHOOTING.md          # Platform-specific issues (includes NixOS)
├── VIRTUAL_ENVIRONMENTS.md     # Virtual environment setup (includes NixOS isolation)
├── JUPYTER_SETUP.md            # Jupyter notebook configuration
└── DEVELOPER_SETUP.md          # Development environment (includes NixOS development)
```

### Key Resources Found

1. **Minimal Dependencies**
   - Core: Python 3.8+, z3-solver, networkx
   - Optional: jupyter, matplotlib, ipywidgets (for notebooks)
   - No complex system dependencies or compilation needed

2. **Optional Nix Support**
   - `/Code/shell.nix` - Available for those who prefer reproducible environments
   - Particularly useful for NixOS users who cannot use pip directly
   - Not required for standard usage or development

2. **Development Scripts**
   - `/Code/dev_cli.py` - Local development CLI
   - `/Code/run_tests.py` - Unified test runner
   - `/Code/run_jupyter.sh` - Jupyter launcher with nix-shell
   - `/Code/run_update.py` - Version management

3. **Gateway Files (TO KEEP)**
   - `/README.md` - Main entry point (keep brief installation with links)
   - `/Code/README.md` - Code entry point (keep brief installation with links)
   - `/Code/CLAUDE.md` - AI assistant guide (excluded from changes)

### What's Working Well

1. **NixOS documentation exists** in multiple places
2. **Basic installation guide** covers pip and NixOS
3. **Developer setup** has NixOS-specific section
4. **Troubleshooting** includes NixOS issues

### What Needs Improvement

1. **BASIC_INSTALLATION.md** needs extended sections for inexperienced users
2. **Emphasize simplicity** - Make clear that basic pip install usually suffices
3. **Links from gateway files** to installation docs need verification
4. **Virtual environments** should be presented as optional
5. **Nix documentation** should be clearly marked as optional
6. **Developer setup** should start with simple approach, then mention options

## Proposed Enhancements

### Keep Existing Structure, Enhance Content

The existing file structure is good. Focus on enhancing content in existing files rather than creating new ones:

1. **BASIC_INSTALLATION.md** - Add extended explanations for beginners, emphasize simplicity
2. **DEVELOPER_SETUP.md** - Start with simple pip install, then optional environments
3. **VIRTUAL_ENVIRONMENTS.md** - Present as optional for those wanting isolation
4. **TROUBLESHOOTING.md** - Focus on common pip issues, include NixOS-specific section
5. **New: PLATFORM_SPECIFIC.md** - Consolidate OS-specific details (optional)

## Implementation Phases

### Phase 1: Enhance BASIC_INSTALLATION.md
**Timeline**: Day 1

#### Additions for Inexperienced Users

Add new sections explaining:

1. **Simple Dependencies**
   ```markdown
   ## Why Installation is Simple
   
   ModelChecker has minimal dependencies:
   - Python 3.8 or higher
   - z3-solver (for constraint solving)
   - networkx (for graph operations)
   
   That's it! No complex setup required.
   ```

2. **What is pip?**
   - Package manager explanation
   - Why we use it
   - Relationship to Python

3. **Understanding Python Versions**
   - How to check your version
   - Why version matters
   - Common version issues

4. **What Gets Installed?**
   - ModelChecker package structure
   - Just two dependencies explained
   - Where files are installed

5. **Optional: Nix for NixOS Users**
   ```markdown
   ## NixOS Users
   
   If you're on NixOS, you cannot use pip directly. Use the provided shell.nix:
   
   ```bash
   git clone https://github.com/benbrastmckie/ModelChecker.git
   cd ModelChecker/Code
   nix-shell
   ./dev_cli.py examples/test.py
   ```
   
   The shell.nix provides everything you need.
   
   ### Optional: Nix on Other Platforms
   
   Nix is also available on other platforms if you prefer reproducible environments,
   but it's not necessary given ModelChecker's simple dependencies.
   ```

5. **Common Beginner Mistakes**
   - Using wrong Python version
   - Not activating virtual environment
   - Permission issues
   - Path problems

### Phase 2: Enhance DEVELOPER_SETUP.md
**Timeline**: Day 2

#### Simple Development Setup First

```markdown
## Development Setup

### Simple Approach (Recommended for Most Users)

ModelChecker has minimal dependencies, so setup is straightforward:

```bash
# Clone the repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Install in development mode
pip install -e .

# That's it! Run tests to verify
./run_tests.py --unit
```

### Available Development Scripts

- `./dev_cli.py` - Run examples with local code
- `./run_tests.py` - Run test suites  
- `./run_update.py` - Version management

### Optional: Virtual Environment

If you prefer to isolate dependencies (though with only z3-solver and networkx, 
conflicts are unlikely):

```bash
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate
pip install -e .
```

### Optional: Nix Environment

For those who prefer reproducible environments, a shell.nix is provided:

```bash
nix-shell  # If you have Nix installed
```

This is particularly useful for:
- NixOS users (who must use this approach)
- Teams wanting identical environments
- CI/CD pipelines

But it's not necessary for general development given the simple dependencies.
```

### Phase 3: Enhance VIRTUAL_ENVIRONMENTS.md
**Timeline**: Day 3

#### Present Virtual Environments as Optional

```markdown
# Virtual Environment Management

## Do You Need a Virtual Environment?

ModelChecker has minimal dependencies (just z3-solver and networkx), so virtual
environments are optional. You can likely install it directly:

```bash
pip install model-checker
```

## When to Use Virtual Environments

Consider a virtual environment if you:
- Want to isolate ModelChecker from other projects
- Are testing multiple Python versions
- Have conflicting package versions with other projects
- Prefer keeping your system Python clean

## Python venv (Simple and Built-in)

```bash
python -m venv venv
source venv/bin/activate  # Linux/macOS
venv\Scripts\activate     # Windows
pip install model-checker
```

## Conda Environments

If you're already using Anaconda/Miniconda:

```bash
conda create -n modelchecker python=3.9
conda activate modelchecker
pip install model-checker
```

## Optional: Nix Environments

For those wanting reproducible environments, the repository includes a shell.nix:

```bash
# If you have Nix installed
cd ModelChecker/Code
nix-shell
```

This is required for NixOS users, optional for everyone else.

## Recommendations

- **For quick testing**: Just use pip in your main shell
- **For development**: Consider a venv if you want isolation
- **For teams**: Nix provides reproducibility if needed
- **For NixOS**: Must use nix-shell
```

### Phase 4: Update Gateway Files
**Timeline**: Day 4

#### Root /README.md

Keep brief installation section but ensure proper links:

```markdown
## Installation

For most users:
```bash
pip install model-checker
```

For comprehensive installation instructions including platform-specific guides, virtual environments, and development setup, see the [Installation Documentation](Docs/installation/README.md).

**Quick Links:**
- [Basic Installation](Docs/installation/BASIC_INSTALLATION.md) - Standard pip installation
- [NixOS Installation](Docs/installation/BASIC_INSTALLATION.md#nixos-installation) - NixOS-specific setup
- [Developer Setup](Docs/installation/DEVELOPER_SETUP.md) - Development environment
- [Troubleshooting](Docs/installation/TROUBLESHOOTING.md) - Common issues
```

#### Code/README.md

Similar approach - keep brief with links:

```markdown
## Quick Start

Install the package:
```bash
pip install model-checker
```

For development:
```bash
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code
pip install -e .
```

**NixOS users**: Use `nix-shell` instead. See [NixOS Development](../Docs/installation/DEVELOPER_SETUP.md#nixos-development).

For complete installation guides, see [Installation Documentation](../Docs/installation/README.md).
```

### Phase 4: Update Other Documentation
**Timeline**: Day 4

#### Files to Update with Links (NOT full installation)

1. `/Code/docs/DEVELOPMENT.md`
   - Add: "For installation, see [Installation Guide](../../Docs/installation/README.md)"
   - Keep existing NixOS section but link to main docs

2. `/Code/src/model_checker/README.md`
   - Add brief install + link to full guide

3. `/Code/src/model_checker/jupyter/README.md`
   - Link to JUPYTER_SETUP.md for installation

4. `/CONTRIBUTING.md`
   - Link to DEVELOPER_SETUP.md

### Phase 5: Create PLATFORM_SPECIFIC.md (Optional)
**Timeline**: Day 5

Consolidate platform details in one place:

```markdown
# Platform-Specific Installation Guide

## Standard Installation (All Platforms)

ModelChecker works on any platform with Python 3.8+:

```bash
pip install model-checker
```

That's usually all you need!

## Platform-Specific Notes

### Windows

- Install Python from python.org (not Microsoft Store)
- Use `py` instead of `python` if needed
- May need Visual C++ Build Tools for z3

### macOS

- Works with system Python or Homebrew Python
- Apple Silicon (M1/M2) fully supported

### Linux

Works on all distributions:
```bash
# Ubuntu/Debian
sudo apt install python3-pip
pip install model-checker

# Arch
sudo pacman -S python-pip
pip install model-checker
```

### NixOS

NixOS users cannot use pip directly. Use the provided shell.nix:

```bash
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code
nix-shell
./dev_cli.py examples/test.py
```

## Optional: Nix on Other Platforms

If you prefer Nix for reproducible environments, it's available on:
- Other Linux distributions
- macOS
- Windows (via WSL2)

But given ModelChecker's minimal dependencies, standard pip installation
works fine for most users.
```

### Phase 6: Testing and Validation
**Timeline**: Day 6

#### Test Installation Paths

1. **Fresh NixOS Install**
   ```bash
   git clone https://github.com/benbrastmckie/ModelChecker.git
   cd ModelChecker/Code
   nix-shell
   ./dev_cli.py examples/test.py
   ```

2. **pip Install (non-NixOS)**
   ```bash
   python -m venv test_env
   source test_env/bin/activate
   pip install model-checker
   model-checker --version
   ```

3. **Development Install**
   ```bash
   pip install -e .
   ./run_tests.py --unit
   ```

#### Verify Links

- Check all cross-references work
- Ensure no broken links
- Test navigation flow

#### Documentation Review

- Have inexperienced user review BASIC_INSTALLATION.md
- Technical review of NixOS sections
- Consistency check across all files

## Success Criteria

### Content Quality
- [x] Existing installation docs identified
- [x] BASIC_INSTALLATION.md expanded for beginners
- [x] Simple pip installation emphasized as primary method
- [x] NixOS-specific section for those who need it
- [x] Gateway files have proper links
- [ ] No installation info in non-installation docs (except links)

### Organization
- [x] Installation docs centralized in Docs/installation/
- [x] Clear navigation between guides
- [x] Consistent information across files
- [x] Minimal dependencies emphasized throughout

### Platform Support
- [x] Standard pip installation as primary method
- [x] Virtual environments presented as optional
- [x] Nix presented as optional tool (required only for NixOS)
- [x] Windows, macOS, Linux covered simply
- [x] No Fedora/RHEL (as requested)
- [x] No Docker mentions

### User Experience
- [x] Beginners understand installation is simple
- [x] Developers can work in main shell if preferred
- [x] Virtual environments available for those who want isolation
- [x] NixOS users have clear instructions
- [ ] Clear troubleshooting available

## Notes

- **DO NOT** change root /README.md or /Code/README.md beyond adding links
- **DO NOT** modify /Code/CLAUDE.md
- **EMPHASIZE** simple dependencies (just z3-solver and networkx)
- **PRESENT** pip installation in main shell as normal approach
- **POSITION** virtual environments and Nix as optional tools
- **ENSURE** BASIC_INSTALLATION.md is beginner-friendly
- **USE** existing file structure where possible
- **EXCLUDE** Fedora/RHEL documentation
- **EXCLUDE** Docker comparisons or mentions