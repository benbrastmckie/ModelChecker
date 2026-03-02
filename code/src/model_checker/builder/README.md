# Builder: Modular Model Checking Framework

[← Back to ModelChecker](../../README.md) | [API Reference →](../README.md)

## Directory Structure

```
builder/
├── README.md                           # This file - builder package overview
├── __init__.py                         # Public API exports
├── types.py                            # Type definitions and protocols for type safety
├── errors.py                           # Custom exception hierarchy
├── protocols.py                        # Protocol definitions for interfaces
├── module.py                           # Core orchestration and initialization
├── runner.py                           # Model checking execution engine
├── runner_utils.py                     # Runner utility functions
├── comparison.py                       # Theory comparison and benchmarking
├── translation.py                      # Operator translation utilities
├── loader.py                           # Module loading and discovery
├── example.py                          # Individual example processing
├── validation.py                       # Parameter validation with detailed errors
├── z3_utils.py                         # Z3 solver utilities and helpers
├── serialize.py                        # Theory serialization for multiprocessing
├── project.py                          # Theory project generation
└── tests/                              # Comprehensive test suite
```

## Overview

The **Builder Package** provides the core infrastructure for constructing and executing modal logic model checking examples. Following a modular architecture, it separates concerns across focused components while maintaining clean interfaces and avoiding backwards compatibility cruft.

### Key Design Principles

1. **No Backwards Compatibility**: Interfaces evolve freely without optional parameters or compatibility layers
2. **Clear Separation of Concerns**: Each module has a single, well-defined responsibility
3. **No Decorators**: All methods are instance methods or module-level functions
4. **Fail-Fast Philosophy**: Errors surface immediately with helpful context
5. **Explicit Data Flow**: No hidden state or implicit conversions
6. **Type Safety**: Comprehensive type hints throughout for better IDE support and error detection

## Core Components

### BuildModule (module.py)

The main orchestrator that coordinates all model checking operations:

```python
from model_checker.builder import BuildModule

# Initialize with command-line flags
module = BuildModule(module_flags)

# Run all examples defined in the module
module.runner.run_examples()
```

**Responsibilities:**
- Module loading and initialization
- Settings management and validation
- Component coordination (runner, comparison, translation)
- Output management and interactive workflows

**Key Features:**
- Dynamic module loading from file paths
- Theory-aware settings validation
- Interactive and batch output modes
- Z3 context isolation between examples

### ModelRunner (runner.py)

Executes model checking operations and manages iteration:

```python
# Internally used by BuildModule
runner = ModelRunner(build_module)
result = runner.process_example(example_name, example_case, theory_name, semantic_theory)
```

**Responsibilities:**
- Individual example execution
- Model iteration coordination
- Progress tracking and timeout handling
- Theory-specific iterate function integration

**Key Features:**
- Unified progress tracking for iterations
- Generator-based incremental model display
- Detailed difference reporting between models
- Clean Z3 context management

### ModelComparison (comparison.py)

Benchmarks different semantic theories by finding maximum model sizes:

```python
# Created when using comparison mode
comparison = ModelComparison(build_module)
results = comparison.run_comparison()
```

**Responsibilities:**
- Theory performance comparison
- Maximum N-value discovery
- Parallel execution management
- Result aggregation and reporting

### OperatorTranslation (translation.py)

Handles operator notation differences between theories:

```python
# Translates operators according to theory dictionaries
translation = OperatorTranslation()
translated_case = translation.translate(example_case, operator_dictionary)
```

**Responsibilities:**
- Operator symbol replacement
- Formula tree traversal
- Theory-specific translations

### ModuleLoader (loader.py)

Enhanced module loader with improved package detection:

```python
# Used internally for module discovery
loader = ModuleLoader(module_name, module_path)
module = loader.load_module()
```

**Responsibilities:**
- Dynamic module importing
- Package detection via .modelchecker marker or config.py
- Intelligent sys.path management
- Clear error messages with actionable solutions

**Key Features:**
- Supports both .modelchecker marker and legacy config.py
- Automatic package detection for generated projects
- Improved error messages for import failures
- Backwards compatible with existing projects

## Usage Patterns

### Running Examples from Command Line

```bash
# Run a single example file
./dev_cli.py examples/my_example.py

# Run with specific settings
./dev_cli.py examples/my_example.py -n -e --contingent

# Compare theories (maximize mode)
./dev_cli.py -m examples/my_example.py

# Save output interactively
./dev_cli.py -s examples/my_example.py
```

### Creating Theory Projects

```python
from model_checker.builder import BuildProject

# Create a new theory project
project = BuildProject('logos')  # Use logos as template
project_path = project.generate('my_new_theory')

# Or use interactive mode
project.ask_generate()
```

### Example Module Structure

```python
# my_examples.py
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['modal', 'counterfactual'])

semantic_theories = {
    "Logos": {
        "semantics": theory["semantics"],
        "proposition": theory["proposition"],
        "model": theory["model"],
        "operators": theory["operators"]
    }
}

example_range = {
    "example1": [
        ["\\Box p", "\\Box q"],           # Premises
        ["\\Box (p \\wedge q)"],          # Conclusions
        {"N": 3, "max_time": 10}          # Settings
    ]
}

general_settings = {
    "N": 3,
    "max_time": 10,
    "iterate": 1
}
```

## Model Iteration

The builder integrates with theory-specific iteration capabilities:

```python
# Settings control iteration behavior
example_settings = {
    "N": 3,
    "iterate": 5,  # Find up to 5 distinct models
    "max_time": 10
}
```

**Iteration Features:**
- Automatic integration with theory iterate functions
- Progress tracking for multi-model searches
- Difference reporting between successive models
- Isomorphism detection and avoidance
- Generator-based incremental display

## Extension Points

### Adding New Theory Support

1. Create theory implementation following the standard structure
2. Define `iterate_example` or `iterate_example_generator` function
3. Implement theory-specific difference detection
4. Add operator dictionary for translations

### Custom Validation

Extend `validation.py` for theory-specific requirements:

```python
def validate_my_theory_settings(settings):
    """Custom validation for my theory."""
    if settings.get('special_param') not in VALID_VALUES:
        raise ValueError("Invalid special_param value")
```

### Progress Tracking

Use the unified progress system for long operations:

```python
from model_checker.output.progress import UnifiedProgress

progress = UnifiedProgress(total_models=10, max_time=60.0)
progress.start_model_search(1)
# ... perform work ...
progress.model_checked()
progress.complete_model_search(found=True)
```

## Performance Considerations

- **Z3 Context Isolation**: Each example runs in a fresh Z3 context
- **Multiprocessing**: Comparison mode uses ProcessPoolExecutor
- **Memory Management**: Explicit garbage collection between examples
- **Timeout Handling**: Configurable timeouts at multiple levels

## Testing

```bash
# Run all builder tests
./run_tests.py builder

# Run specific test modules
python -m pytest src/model_checker/builder/tests/test_module.py -xvs

# Test with example files
./dev_cli.py test_example.py
```

## Improvements (Issue #73 Fix)

### Package Loading Enhancements

The module loader has been enhanced to fix issue #73 while maintaining backwards compatibility:

**New Features:**
- Support for `.modelchecker` marker files in generated packages
- Improved package detection with `_is_generated_project_package()` method
- Better sys.path handling with `_load_as_package_module()` method
- Clearer error messages when packages cannot be imported

**Supported Formats:**
- Legacy `config.py` format (still works)
- New `.modelchecker` marker format (recommended for new projects)
- Both formats can coexist

**Error Improvements:**
- New `PackageError` hierarchy provides detailed context
- `PackageStructureError` - missing or invalid package structure
- `PackageFormatError` - invalid .modelchecker marker
- `PackageImportError` - package cannot be imported
- All errors include actionable solutions

### Using the New Package Format

For new generated projects, you can optionally use the cleaner package format:

1. **Add .modelchecker marker:**
```bash
echo "package=true" > project_name/.modelchecker
```

2. **Ensure proper package structure:**
```bash
# Must have __init__.py
touch project_name/__init__.py
```

3. **Import normally:**
```python
# Package will be automatically detected and loaded
from project_name import examples
```

**Note:** Existing projects with `config.py` continue to work without any changes.

## See Also

### Conceptual Documentation
- **[Builder Architecture](../../../../Docs/architecture/BUILDER.md)** - High-level pipeline concepts
- **[Architecture Overview](../../../../Docs/architecture/ARCHITECTURE.md)** - System design principles

### Technical Documentation
- **[Technical Architecture](../../../docs/ARCHITECTURE.md)** - Detailed component relationships
- **[Implementation Guide](../../../docs/IMPLEMENTATION.md)** - Feature development process
- **[Testing Guide](../../../docs/TESTS.md)** - Testing the builder components

### Related Components
- **[Iterate Package](../iterate/README.md)** - Model iteration functionality
- **[Settings Package](../settings/README.md)** - Configuration management
- **[Theory Library](../theory_lib/README.md)** - Semantic theory implementations

---

[← Back to ModelChecker](../../README.md) | [API Reference →](../README.md)