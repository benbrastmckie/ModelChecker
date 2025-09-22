# ModuleLoader API Documentation

## Overview

`ModuleLoader` provides simplified, robust module loading for the ModelChecker framework. Following the fail-fast philosophy with no backwards compatibility, it offers a clean, single path for loading modules with clear error messages.

**Location**: `model_checker.builder.loader`  
**Lines of Code**: 223 (reduced from 619, 64% reduction)

## Class: ModuleLoader

### Constructor

```python
ModuleLoader(module_name: str, module_path: str)
```

Initialize the module loader with strict validation.

**Parameters:**
- `module_name` (str): Name of the module to load
- `module_path` (str): Full path to the module file

**Raises:**
- `ModuleLoadError`: If the module file does not exist

**Example:**
```python
from model_checker.builder.loader import ModuleLoader

loader = ModuleLoader("examples", "/path/to/examples.py")
```

### Methods

#### load_module()

```python
load_module() -> ModuleType
```

Load a Python module with permanent sys.path modifications.

**Key Behaviors:**
- No backwards compatibility
- No sys.path restoration (changes are permanent)
- Simple, direct loading with clear error messages
- Automatically detects and handles generated packages

**Returns:**
- `ModuleType`: The loaded Python module

**Raises:**
- `PackageImportError`: If package cannot be imported
- `ModuleLoadError`: If module cannot be loaded

**Example:**
```python
module = loader.load_module()
# sys.path has been permanently modified if needed
```

#### load_attribute()

```python
load_attribute(module: ModuleType, attribute_name: str, default: Any = None) -> Any
```

Load an attribute from a module with optional default.

**Parameters:**
- `module` (ModuleType): The module to load from
- `attribute_name` (str): Name of the attribute to load
- `default` (Any): Default value if attribute doesn't exist

**Returns:**
- The attribute value or default

**Example:**
```python
semantic_theories = loader.load_attribute(module, "semantic_theories", {})
```

### Private Methods

#### _is_generated_project_package()

```python
_is_generated_project_package() -> bool
```

Check if module is part of a generated package.

**Strict Requirements:**
- Only checks for `.modelchecker` marker
- No fallbacks or alternative detection methods
- Marker must contain `package=true`

**Returns:**
- `bool`: True if part of generated package

**Raises:**
- `PackageFormatError`: If marker exists but is invalid

#### _find_package_root()

```python
_find_package_root() -> Optional[str]
```

Find the package root directory by looking for `.modelchecker` marker.

**Returns:**
- `Optional[str]`: Path to package root, or None if not found

**Search Behavior:**
- Searches up to 10 directories up from module location
- Stops at filesystem root
- Returns first directory containing `.modelchecker`

#### _load_as_package_module()

```python
_load_as_package_module() -> ModuleType
```

Load module as part of a package with no fallbacks.

**Key Behaviors:**
- Adds parent directory to sys.path permanently
- No restoration of sys.path
- Clear error messages with context

**Returns:**
- `ModuleType`: The loaded module

**Raises:**
- `PackageStructureError`: If package structure is invalid
- `PackageImportError`: If package cannot be imported

#### _load_standard_module()

```python
_load_standard_module() -> ModuleType
```

Load a standard Python module file.

**Returns:**
- `ModuleType`: The loaded module

**Raises:**
- `ModuleLoadError`: If module cannot be loaded

## Error Hierarchy

### PackageError

Base class for all package-related errors.

```python
class PackageError(BuilderError):
    def __init__(self, message: str, *details: str)
```

**Features:**
- Main error message
- Additional details for context
- Formatted output with bullet points

### PackageStructureError

Raised when package structure doesn't meet requirements.

**Common Causes:**
- Missing `.modelchecker` marker
- Missing `__init__.py`
- Invalid directory structure

### PackageFormatError

Raised when package format is invalid.

**Common Causes:**
- `.modelchecker` doesn't contain `package=true`
- Malformed marker file
- Invalid package metadata

### PackageImportError

Raised when package cannot be imported.

**Common Causes:**
- Import statement fails
- Module not found in package
- Circular imports
- Missing dependencies

### PackageNotImportableError

Raised when generated package is not in importable state.

**Common Causes:**
- Package not in sys.path
- Parent directory not accessible
- Package dependencies missing

## Usage Examples

### Basic Module Loading

```python
from model_checker.builder.loader import ModuleLoader

# Load a standalone module
loader = ModuleLoader("my_module", "/path/to/my_module.py")
module = loader.load_module()

# Access module attributes
my_function = getattr(module, "my_function")
my_variable = loader.load_attribute(module, "my_variable", default=42)
```

### Generated Package Loading

```python
# Load a module from a generated package
loader = ModuleLoader("examples", "/path/to/project/examples.py")

# Automatically detects package via .modelchecker
if loader._is_generated_project_package():
    print("Loading as package")
    
module = loader.load_module()
# Parent directory has been added to sys.path permanently
```

### Error Handling

```python
from model_checker.builder.loader import ModuleLoader
from model_checker.builder.errors import (
    PackageStructureError,
    PackageFormatError,
    PackageImportError
)

try:
    loader = ModuleLoader("examples", path)
    module = loader.load_module()
    
except PackageStructureError as e:
    print(f"Package structure issue: {e}")
    # Details include what's missing
    
except PackageFormatError as e:
    print(f"Invalid marker format: {e}")
    # Details include what was found vs expected
    
except PackageImportError as e:
    print(f"Cannot import package: {e}")
    # Details include paths and original error
```

## Breaking Changes from v1

### Removed Methods

The following methods no longer exist:

- `is_generated_project()` - Use `_is_generated_project_package()`
- `find_project_directory()` - Removed entirely
- `_extract_theory_from_config()` - No config.py support
- `_load_generated_project_module()` - Removed
- `_load_generated_project_with_absolute_imports()` - Removed

### Changed Behaviors

1. **sys.path is never restored** - Changes are permanent
2. **No PYTHONPATH manipulation** - Direct sys.path only
3. **No config.py support** - Only .modelchecker markers
4. **No fallback methods** - Single detection method
5. **Strict validation** - Marker must be exactly correct

## Performance Characteristics

- **Module Detection**: O(1) file check for .modelchecker
- **Package Root Finding**: O(d) where d is directory depth (max 10)
- **Import Time**: Same as standard Python import
- **Memory**: No caching, minimal overhead

## Thread Safety

ModuleLoader is not thread-safe due to sys.path modifications. Use appropriate locking if loading modules from multiple threads.

## See Also

- [Migration Guide](../../migration/package_loading_v2.md) - Migrating from v1
- [Error Hierarchy](../errors.md) - Complete error documentation
- [Builder README](../../../src/model_checker/builder/README.md) - Package overview