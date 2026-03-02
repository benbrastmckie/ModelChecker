# Guides: User Guides and How-To Documentation

[← Back to Docs](../README.md) | [PROJECT_CREATION →](PROJECT_CREATION.md)

## Directory Structure

```
guides/
└── PROJECT_CREATION.md            # Creating new theory projects
```

## Overview

The guides directory contains user-facing how-to documentation for common ModelChecker tasks. Unlike standards documents that specify requirements, guides provide step-by-step instructions for accomplishing specific goals.

Currently focused on project creation workflows, this directory will expand with additional user guides as common usage patterns emerge. Guides complement API documentation by showing practical examples and workflows.

Use these guides when learning how to use ModelChecker features or when you need step-by-step instructions for specific tasks.

## Documents

### PROJECT_CREATION.md
- **Purpose**: Guide users through creating new theory projects
- **Use When**: Starting a new semantic theory project
- **Key Sections**:
  - Interactive project creation workflow
  - Programmatic project creation (BuildProject API)
  - Project structure requirements
  - Required vs optional files
  - Package marker file format (.modelchecker)
  - Loading and using created projects

## Learning Path

**Getting started with ModelChecker**:

1. **Create project**: [PROJECT_CREATION.md](PROJECT_CREATION.md) - Build your first theory project

## Quick Reference

### Common Tasks

- **Creating new theory?** → PROJECT_CREATION.md interactive workflow
- **Understanding project structure?** → PROJECT_CREATION.md structure section
- **Programmatic creation?** → PROJECT_CREATION.md BuildProject API examples
- **Package marker format?** → PROJECT_CREATION.md .modelchecker requirements

### Quick Start: Interactive Creation

From [PROJECT_CREATION.md](PROJECT_CREATION.md):

```bash
# Start interactive project creation
./dev_cli.py

# Follow prompts to configure your project
```

### Quick Start: Programmatic Creation

From [PROJECT_CREATION.md](PROJECT_CREATION.md):

```python
from model_checker.builder import BuildProject

# Create project builder
builder = BuildProject()

# Generate project
project_path = builder.generate("my_theory", "/path/to/projects")
print(f"Project created at: {project_path}")
```

### Project Structure

Required files:
- `.modelchecker` - Package marker (must contain `package=true`)
- `__init__.py` - Package initialization
- `semantic.py` - Theory semantics
- `operators.py` - Operator definitions

Optional files:
- `examples.py` - Example formulas and tests
- `iterate.py` - Custom iteration logic
- `utils.py` - Helper functions

## References

### Related Documentation Categories
- [API Documentation](../api/README.md) - ModuleLoader API for loading projects
- [Package Standards](../specific/PACKAGES.md) - Package structure requirements
- [Development Workflow](../implementation/DEVELOPMENT_WORKFLOW.md) - How to develop theories

### Templates
- [Theory Template](../templates/THEORY_TEMPLATE.py) - Template for semantic.py
- [Examples Template](../templates/EXAMPLES_TEMPLATE.py) - Template for examples.py
- [Test Template](../templates/TEST_TEMPLATE.py) - Template for unit tests

### Migration Information
- [Package Loading Migration](../migration/package_loading_v2.md) - Issue #73 changes

[← Back to Docs](../README.md) | [PROJECT_CREATION →](PROJECT_CREATION.md)
