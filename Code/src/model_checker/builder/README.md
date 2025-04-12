# Model Checker Builder Package

This package provides components for building and executing modal logic model checking examples. It replaces the monolithic builder.py with a more modular approach, following the project's design philosophy.

## Components

### Core Classes

- **BuildModule**: Manages loading and executing model checking examples from Python modules.
- **BuildProject**: Creates new theory implementation projects from templates.
- **BuildExample**: Handles individual model checking examples.

### Utilities

- **progress.py**: Progress tracking for long-running operations.
- **validation.py**: Parameter validation utilities.
- **z3_utils.py**: Utilities for working with Z3 models.

## Design Philosophy

The builder package follows the project's design philosophy:

- **Fail Fast**: Let errors occur naturally with detailed error messages.
- **Required Parameters**: Parameters are explicitly required with no implicit conversions.
- **Clear Data Flow**: Maintain a consistent approach to passing data between components.
- **No Silent Failures**: Don't catch exceptions or provide defaults to avoid errors.

## Usage Examples

### Creating a New Theory Project

```python
from model_checker.builder import BuildProject

# Create a project builder using 'default' theory as template
project = BuildProject('default')

# Generate a new project
project_path = project.generate('my_theory')
print(f"New theory project created at: {project_path}")
```

### Running Model Checking Examples

```python
from model_checker.builder import BuildModule

# Initialize with module flags (e.g., from command line)
module = BuildModule(module_flags)

# Run all examples
module.run_examples()

# Or run a single example
example = module.run_model_check(
    example_case,
    example_name="Example 1",
    theory_name="Default",
    semantic_theory=module.semantic_theories["default"]
)

# Get and display results
result = example.get_result()
print(f"Model found: {result['model_found']}")
print(f"Runtime: {result['runtime']} seconds")
```

## Extension Points

The builder package is designed for modularity and extension:

1. **New Theory Types**: Create new theory implementations by extending the base classes.
2. **Custom Validation**: Add specialized validation for your theory's parameters.
3. **Progress Reporting**: Use or extend the progress tracking for long-running operations.

## Testing

Run the tests with pytest:

```bash
pytest src/model_checker/builder/test_*.py
```

## Future Development

The module is being developed as a replacement for the monolithic builder.py. Once complete, the original builder.py will be deprecated and removed.

Note: This is a breaking change from the original builder.py. The new module prioritizes clarity and correctness over backwards compatibility.