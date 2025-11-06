# API: Public API Documentation

[← Back to Docs](../README.md) | [Builder API →](builder/LOADER.md)

## Directory Structure

```
api/
└── builder/
    └── LOADER.md                  # ModuleLoader API reference
```

## Overview

The API directory contains public API documentation for ModelChecker components that are intended for programmatic use. These documents specify the interfaces, parameters, return values, and usage patterns for public APIs.

Currently focused on the builder subsystem (BuildProject and ModuleLoader), this directory will expand as additional public APIs are formalized and documented.

Use these documents when integrating ModelChecker functionality into other tools or when programmatically creating and loading theory projects.

## Documents

### builder/LOADER.md
- **Purpose**: Document the ModuleLoader API for theory package loading
- **Use When**: Programmatically loading theory packages or understanding package loading
- **Key Sections**:
  - ModuleLoader class interface
  - Package loading mechanisms
  - .modelchecker marker file format
  - Error handling for invalid packages
  - Load ordering and dependencies

## Learning Path

**API integration workflow**:

1. **Package loading**: [builder/LOADER.md](builder/LOADER.md) - How to load theory packages programmatically

## Quick Reference

### Common Tasks

- **Loading theory package?** → See builder/LOADER.md ModuleLoader class
- **Understanding .modelchecker format?** → builder/LOADER.md specifies marker file structure
- **Handling load errors?** → builder/LOADER.md documents error conditions
- **Creating projects?** → See [PROJECT_CREATION.md](../guides/PROJECT_CREATION.md) for BuildProject usage

### ModuleLoader Quick Start

From [builder/LOADER.md](builder/LOADER.md):

```python
from model_checker.builder import ModuleLoader

# Load theory package
loader = ModuleLoader()
theory_module = loader.load("/path/to/project_my_theory")

# Access loaded theory
semantic = theory_module.semantic
operators = theory_module.operators
examples = theory_module.examples
```

### Package Requirements

- Package must contain `.modelchecker` marker file
- Marker must include `package=true`
- Required modules: `semantic.py`, `operators.py`
- Optional modules: `examples.py`, `iterate.py`, `utils.py`

## References

### Related Documentation Categories
- [Package Structure](../specific/PACKAGES.md) - Theory package organization standards
- [Project Creation](../guides/PROJECT_CREATION.md) - How to create new theory projects
- [Core Architecture](../core/ARCHITECTURE.md) - System design context

### Implementation Resources
- [Builder Package](../../src/model_checker/builder/README.md) - Builder implementation details
- [Development Workflow](../implementation/DEVELOPMENT_WORKFLOW.md) - How to develop with API

### User Guides
- [Project Creation Guide](../guides/PROJECT_CREATION.md) - Creating theory projects
- [Migration Guide](../migration/package_loading_v2.md) - Package loading changes (Issue #73)

[← Back to Docs](../README.md) | [Builder API →](builder/LOADER.md)
