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
- **iterate.py**: Systematic discovery of multiple distinct models for logical examples.
- **z3_utils.py**: Utilities for working with Z3 models, including finding alternative models.
- **graph_utils.py**: Graph representation of models for structural comparison.

## Model Iteration System

The model iteration system (in `iterate.py`) provides capabilities for finding multiple semantically distinct models for a logical example. This is particularly useful for:

1. Finding countermodels that demonstrate formula invalidity
2. Exploring the space of possible models for a given set of constraints
3. Comparing different semantic interpretations of the same logical structure

### How Iteration Works

The iteration process systematically finds multiple distinct models by:

1. Starting with an initial valid model found by `BuildExample`
2. Creating constraints that require each new model to differ from all previous models
3. Using Z3 to find solutions that satisfy both the original logical constraints and the difference constraints
4. Checking for model isomorphism to ensure truly distinct models are found
5. Tracking and reporting differences between successive models

### Difference Mechanism

The iteration system uses a comprehensive approach to find different models by combining several techniques:

1. **Semantic differences**: Ensures changes in sentence letter valuations and semantic function interpretations from one model to the next.

2. **Theory-specific differences**: When available, uses a theory's `calculate_model_differences` method to identify meaningful differences according to the theory's semantics.

3. **Structural checks**: When NetworkX is available, analyzes model graph structures to avoid isomorphic models that have the same structure but different representations.

4. **Escalating constraints**: Uses increasingly stronger constraints when similar models are encountered repeatedly, helping to escape from isomorphic regions of the search space.

The system automatically applies the most appropriate difference methods based on the model's characteristics and theory implementation:

### Iteration Settings

The following settings control the iteration behavior in any theory:

- **iterate**: Maximum number of models to find (default: 1)
- **max_time**: Maximum solver time for each model (inherited from general settings)
- **iteration_attempts**: Maximum consecutive isomorphic models before applying stronger constraints (default: 5)
- **escape_attempts**: Maximum attempts to escape from isomorphic models before giving up (default: 3)
- **iteration_timeout**: Maximum time for isomorphism checking (default: 1.0 seconds)
- **difference_type**: Legacy setting, currently only 'semantic' is fully implemented

In the default theory, the `iterate` setting can be used as follows:

```python
# Example in default theory that finds up to 3 different models
example = {
    "name": "iteration_example",
    "premises": ["(p \\rightarrow q)"],
    "conclusions": ["(p \\wedge q)"],
    "settings": {
        "N": 3,
        "iterate": 3,  # Find up to 3 distinct models
        "max_time": 5
    }
}
```

### Differences Between Models

The iteration system tracks differences between models in several ways:

1. **Propositional differences**: Different truth values for sentence letters
2. **Structural differences**: Different accessibility relations or world structures
3. **Graph differences**: Models with different graph structures
4. **Function differences**: Theory-specific semantic function interpretations

Each found model includes a `model_differences` property that details how it differs from the previous model, making it easy to understand the semantic variations.

## Usage Examples

### Creating a New Theory Project

```python
from model_checker.builder import BuildProject

# Create a project builder using 'logos' theory as template
project = BuildProject('logos')

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
```

### Finding Multiple Models

```python
from model_checker import BuildExample, get_theory
from model_checker.builder.iterate import ModelIterator

# Create a model with the default theory
theory = get_theory("logos")
example = BuildExample("simple_modal", theory, settings={"iterate": 3, "max_time": 5})

# Check if the model is satisfiable
if example.model_structure.z3_model_status:
    # Create an iterator to find multiple models
    iterator = ModelIterator(example)
    
    # Find up to 3 distinct models
    models = iterator.iterate()
    
    # Print summary information
    print(f"Found {len(models)} distinct models")
    
    # Print differences between models
    for i, model in enumerate(models[1:], 2):
        print(f"Model {i} differences:")
        for key, diff in model.model_differences.items():
            print(f"  {key}: {diff}")
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
5. **Model Iteration**: Extend the iteration system for theory-specific differentiating constraints.

## Testing

Run the tests using the project's test infrastructure:

```bash
# Run all builder tests
python test_package.py --components builder

# Run specific component tests
python test_package.py --components builder.validation

# Run with all theory tests to ensure compatibility
python test_theories.py
```
