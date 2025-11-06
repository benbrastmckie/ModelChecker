# Project Creation Guide

## Overview

This guide explains how to create new ModelChecker theory projects using the `BuildProject` class. Projects are self-contained Python packages that implement semantic theories.

**Important**: Following issue #73 fix, generated projects have strict structure requirements with no backwards compatibility.

## Quick Start

### Interactive Creation

```bash
# Start interactive project creation
./dev_cli.py

# When prompted, choose to create a new project
# Follow the prompts to configure your project
```

### Programmatic Creation

```python
from model_checker.builder import BuildProject

# Create project builder
builder = BuildProject()

# Generate project in specific directory
project_path = builder.generate("my_theory", "/path/to/projects")
print(f"Project created at: {project_path}")
```

## Project Structure

Generated projects follow this strict structure:

```
project_my_theory/
├── .modelchecker          # REQUIRED: Package marker (must contain "package=true")
├── __init__.py           # REQUIRED: Package initialization
├── semantic.py           # Semantic theory implementation
├── operators.py          # Operator definitions
├── examples.py           # Example formulas and test cases
├── iterate.py            # Model iteration logic (optional)
├── utils.py              # Helper functions (optional)
└── subtheories/          # Subtheory implementations (optional)
    └── modal/
        ├── __init__.py
        └── examples.py
```

## Required Files

### .modelchecker (REQUIRED)

**Purpose**: Identifies directory as a generated ModelChecker package

**Format**: Must contain exactly:
```
package=true
```

**Breaking Change**: This file is now mandatory. No fallback detection methods exist.

### __init__.py (REQUIRED)

**Purpose**: Makes directory a valid Python package

**Typical Content**:
```python
"""My theory package."""

from .semantic import MySemantics, MyProposition, MyModelStructure
from .operators import my_operators, get_operators
from .examples import semantic_theories, example_range

__version__ = "1.0.0"

__all__ = [
    'MySemantics',
    'MyProposition', 
    'MyModelStructure',
    'my_operators',
    'get_operators',
    'semantic_theories',
    'example_range',
]
```

### semantic.py

**Purpose**: Core semantic theory implementation

**Structure**:
```python
from model_checker.semantics import Semantics
from model_checker.models import Model, Proposition

class MySemantics(Semantics):
    """Semantic theory implementation."""
    
    def check_validity(self, premises, conclusions, settings):
        """Check if argument is valid."""
        # Implementation
        
class MyProposition(Proposition):
    """Proposition implementation."""
    
class MyModelStructure(Model):
    """Model structure implementation."""
```

### examples.py

**Purpose**: Define example formulas and test cases

**Structure**:
```python
from .semantic import MySemantics, MyProposition, MyModelStructure
from .operators import my_operators

semantic_theories = {
    "MyTheory": {
        "semantics": MySemantics,
        "proposition": MyProposition,
        "model": MyModelStructure,
        "operators": my_operators
    }
}

example_range = {
    "modus_ponens": [
        ["A", "(A \\rightarrow B)"],  # Premises
        ["B"],                         # Conclusions
        {"N": 3}                       # Settings
    ]
}
```

## Creating a Project Step-by-Step

### Step 1: Initialize Builder

```python
from model_checker.builder import BuildProject

builder = BuildProject()
```

### Step 2: Generate Project

```python
# Basic generation
project_path = builder.generate("my_theory")

# Specify output directory
project_path = builder.generate("my_theory", "/custom/path")

# Interactive generation
builder.ask_generate()
```

### Step 3: Verify Structure

After generation, verify the project structure:

```bash
# Check required files exist
ls -la project_my_theory/
# Should see: .modelchecker, __init__.py, semantic.py, examples.py

# Verify marker content
cat project_my_theory/.modelchecker
# Should output: package=true
```

### Step 4: Test the Project

```python
# The project is immediately importable
import sys
sys.path.insert(0, "/path/to/parent")

from project_my_theory import semantic_theories, example_range

# Or run with model-checker
./dev_cli.py project_my_theory/examples.py
```

## Package Requirements

### Import Structure

Generated packages use relative imports internally:

```python
# In examples.py
from .semantic import MySemantics  # Relative import
from .operators import my_operators  # Relative import
```

### External Usage

When using the package externally:

```python
# Must use full package imports
from project_my_theory import semantic_theories
from project_my_theory.semantic import MySemantics

# NOT: from semantic import MySemantics  # Won't work
```

### sys.path Behavior

**Important Breaking Change**: When a generated package is loaded, its parent directory is added to sys.path **permanently**. This change is not reversed.

```python
# Before loading
print(sys.path)  # [original paths]

# Load module from package
from model_checker.builder import ModuleLoader
loader = ModuleLoader("examples", "project/examples.py")
module = loader.load_module()

# After loading
print(sys.path)  # [parent_dir, original paths]
# parent_dir remains in sys.path permanently
```

## Common Issues

### Issue: ModuleNotFoundError

**Cause**: Package structure invalid or marker missing

**Solution**:
1. Ensure `.modelchecker` exists with `package=true`
2. Ensure `__init__.py` exists
3. Verify parent directory is accessible

### Issue: PackageFormatError

**Cause**: `.modelchecker` has wrong content

**Solution**:
```bash
echo "package=true" > project_name/.modelchecker
```

### Issue: Import errors with relative imports

**Cause**: Package not being loaded as package

**Solution**: Use the generated project as a proper Python package:
```python
# Good
from project_name.module import function

# Bad (won't work from outside package)
from module import function
```

## Best Practices

1. **Always verify structure** after generation
2. **Use relative imports** within the package
3. **Use absolute imports** when importing the package
4. **Keep .modelchecker** file exactly as generated
5. **Don't modify __init__.py** exports unless necessary
6. **Test immediately** after generation

## Migration from Old Projects

If you have projects created before the issue #73 fix:

1. Add `.modelchecker` file:
```bash
echo "package=true" > old_project/.modelchecker
```

2. Ensure `__init__.py` exists:
```bash
touch old_project/__init__.py
```

3. Update any custom loading code to handle permanent sys.path changes

## See Also

- [Migration Guide](../migration/package_loading_v2.md) - Detailed migration instructions
- [ModuleLoader API](../api/builder/LOADER.md) - Loader documentation
- [Builder README](../../src/model_checker/builder/README.md) - Builder package overview
- [Issue #73](https://github.com/benbrastmckie/ModelChecker/issues/73) - Original issue that prompted these changes