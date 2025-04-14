# Model Checker Builder Package

This package provides components for building and executing modal logic model checking examples. It replaces the monolithic builder.py with a modular approach, following the project's design philosophy.

## Components

### Core Classes

- **BuildModule**: Manages loading and executing model checking examples from Python modules, including running examples, comparing theories, and handling theory translations.
- **BuildProject**: Creates new theory implementation projects from templates, including file copying, project setup, and test execution.
- **BuildExample**: Handles individual model checking examples, including model building, result evaluation, and iterative model finding.

### Utilities

- **progress.py**: Thread-based progress tracking for long-running operations.
- **validation.py**: Parameter validation utilities with detailed error messages.
- **z3_utils.py**: Utilities for working with Z3 models, including finding alternative models.

## Design Philosophy

The builder package follows the project's design philosophy:

- **Fail Fast**: Let errors occur naturally with detailed error messages.
- **Required Parameters**: Parameters are explicitly required with no implicit conversions.
- **Clear Data Flow**: Maintain a consistent approach to passing data between components.
- **No Silent Failures**: Don't catch exceptions or provide defaults to avoid errors.
- **Modularity**: Separate concerns into focused, reusable components.

## Usage Examples

### Creating a New Theory Project

```python
from model_checker.builder import BuildProject

# Create a project builder using 'default' theory as template
project = BuildProject('default')

# Generate a new project
project_path = project.generate('my_theory')
print(f"New theory project created at: {project_path}")

# Or use the interactive mode
project.ask_generate()
```

### Running Model Checking Examples

```python
from model_checker.builder import BuildModule

# Initialize with module flags (e.g., from command line)
module = BuildModule(module_flags)

# Run all examples
module.run_examples()

# Or run a comparison across different semantic theories
module.run_comparison()

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

# Find alternative models
if result['model_found']:
    found_alternative = example.find_next_model()
    if found_alternative:
        print("Found an alternative model")
        example.print_model("Alternative", "Default")
```

### Theory Translation

```python
from model_checker.builder import BuildModule

# Initialize module
module = BuildModule(module_flags)

# Example case with standard notation
example_case = [["\\Box p"], ["\\Diamond p"], {"N": 3}]

# Translate to alternate notation used by different theories
translated_examples = module.translate_example(
    example_case, 
    module.semantic_theories
)

# Each theory now has properly translated operators
for theory_name, semantic_theory, translated_case in translated_examples:
    print(f"Theory: {theory_name}")
    print(f"Translated premises: {translated_case[0]}")
    print(f"Translated conclusions: {translated_case[1]}")
```

## Extension Points

The builder package is designed for modularity and extension:

1. **New Theory Types**: Create new theory implementations by extending the base classes.
2. **Custom Validation**: Add specialized validation for your theory's parameters.
3. **Progress Reporting**: Use or extend the progress tracking for long-running operations.
4. **Z3 Utilities**: Extend the Z3 utilities to support additional constraint types.

## Testing

Run the tests using the project's test infrastructure:

```bash
# Run all builder tests
python test_package.py --components builder

# Run specific component tests
python test_package.py --components builder.validation

# Run with all theory tests to ensure compatibility
python run_tests.py
```
