# Builder Pattern: BuildModule/BuildExample Architecture

[← Back to Methodology](README.md) | [Syntax Pipeline →](SYNTAX.md)

## Table of Contents

1. [Introduction](#introduction)
2. [BuildModule Architecture](#buildmodule-architecture)
   - [Module Loading](#module-loading)
   - [Settings Management](#settings-management)
   - [Theory Selection](#theory-selection)
   - [Example Execution](#example-execution)
3. [BuildExample Flow](#buildexample-flow)
   - [Complete Pipeline](#complete-pipeline)
   - [Settings Merger](#settings-merger)
   - [Operator Collection](#operator-collection)
   - [Model Solving](#model-solving)
4. [BuildProject Functionality](#buildproject-functionality)
   - [Theory Generation](#theory-generation)
   - [Directory Structure](#directory-structure)
   - [Module Initialization](#module-initialization)
5. [Integration Points](#integration-points)
   - [Component Connection](#component-connection)
   - [Settings Flow](#settings-flow)
   - [Theory Loading](#theory-loading)
   - [Result Interpretation](#result-interpretation)
6. [Code Examples](#code-examples)
7. [References](#references)

## Introduction

The Builder Pattern in ModelChecker orchestrates the model checking pipeline through three core classes: `BuildModule`, `BuildExample`, and `BuildProject`. This pattern provides a clean separation between module management, example execution, and project generation while maintaining a consistent flow of settings and data throughout the system.

The builder architecture serves as the entry point for all model checking operations, handling everything from loading Python modules containing logical examples to generating new theory implementation projects. It ensures proper initialization of components, manages concurrent execution for performance comparisons, and provides isolation between different examples to prevent state leakage.

## BuildModule Architecture

### Module Loading

BuildModule dynamically loads Python modules containing modal logic examples and extracts the necessary components for model checking. The loading process handles both installed packages and generated projects through intelligent path detection:

```python
# Module loading process
build_module = BuildModule(module_flags)
# 1. Detects if module is from generated project (project_* prefix)
# 2. Sets up proper Python path for imports
# 3. Loads module using importlib
# 4. Extracts semantic_theories, example_range, and settings
```

The module loader supports:
- Standard theory library modules (`theory_lib/logos/examples.py`)
- Generated project modules (`project_my_theory/examples.py`)
- Relative imports within theory packages
- Dynamic theory loading without prior registration

### Settings Management

BuildModule implements a sophisticated settings management system that handles theory-specific defaults, module-level settings, and command-line overrides:

```python
# Settings hierarchy (highest to lowest priority)
1. Command-line flags (--verbose, --N=5, etc.)
2. Example-specific settings (in example_range)
3. Module general_settings
4. Theory-specific defaults
5. System DEFAULT_GENERAL_SETTINGS
```

The settings manager validates settings based on each theory's requirements, warning about unknown settings in single-theory mode while allowing flexibility in comparison mode.

### Theory Selection

BuildModule manages multiple semantic theories for comparative analysis:

```python
semantic_theories = {
    "Brast-McKie": {
        "semantics": LogosSemantics,
        "proposition": LogosProposition,
        "model": LogosModelStructure,
        "operators": LogosOperatorRegistry().operators,
        "dictionary": {"\\implies": "\\rightarrow"}  # Optional translations
    },
    "Exclusion": {
        "semantics": ExclusionSemantics,
        "proposition": ExclusionProposition,
        "model": ExclusionModelStructure,
        "operators": exclusion_operators
    }
}
```

### Example Execution

BuildModule coordinates example execution with proper isolation and progress tracking:

```python
# Example execution flow
for example_name, example_case in example_range.items():
    # Reset Z3 context for isolation
    Z3ContextManager.reset_context()
    
    for theory_name, semantic_theory in semantic_theories.items():
        # Create isolated example copy
        example = BuildExample(build_module, semantic_theory, example_case, theory_name)
        # Process with iteration support
        build_module.process_example(example_name, example_case, theory_name, semantic_theory)
```

## BuildExample Flow

### Complete Pipeline

BuildExample orchestrates the complete model checking pipeline from premises/conclusions to final model structure:

```python
# BuildExample initialization pipeline
example = BuildExample(build_module, semantic_theory, example_case, theory_name)

# Pipeline stages:
1. Validate semantic theory components
2. Extract premises, conclusions, settings
3. Create SettingsManager with theory context
4. Initialize Syntax (parses formulas)
5. Create ModelConstraints (links syntax to semantics)
6. Build ModelStructure (Z3 solving)
7. Interpret sentences (evaluate in model)
```

### Settings Merger

BuildExample implements theory-aware settings validation and merging:

```python
# Settings validation with theory context
settings_manager = SettingsManager(
    {"semantics": self.semantics},
    build_module.general_settings,
    theory_name=theory_name,
    is_comparison=is_comparison
)

# Get complete settings with validation
self.settings = settings_manager.get_complete_settings(
    raw_general_settings,
    example_settings,
    module_flags
)
```

### Operator Collection

Operator instantiation connects syntactic operators to their semantic implementations:

```python
# Create syntax with operator collection
self.example_syntax = Syntax(premises, conclusions, operators)

# Create model constraints linking syntax to semantics
self.model_constraints = ModelConstraints(
    settings,
    example_syntax,
    semantics(settings),  # Instantiated semantics
    proposition_class
)
```

### Model Solving

Model solving integrates Z3 constraint generation and solution extraction:

```python
# Model structure creation and solving
self.model_structure = model_structure_class(model_constraints, settings)

# Interpret sentences in found model
sentence_objects = model_structure.premises + model_structure.conclusions
model_structure.interpret(sentence_objects)

# Extract results
result = {
    "model_found": model_structure.z3_model_status,
    "runtime": model_structure.z3_model_runtime,
    "model_structure": model_structure_data
}
```

## BuildProject Functionality

### Theory Generation

BuildProject creates new theory implementations from existing templates:

```python
# Create new theory project
project = BuildProject(theory='logos')
project_dir = project.generate('my_counterfactual_theory')

# Generated structure:
project_my_counterfactual_theory/
├── __init__.py          # Version info and exports
├── semantic.py          # Core semantic implementation
├── operators.py         # Operator definitions
├── examples.py          # Example formulas
├── LICENSE.md           # GPL-3.0 license
├── CITATION.md          # Citation template
├── docs/                # Documentation
├── tests/               # Test suite
└── notebooks/           # Interactive tutorials
```

### Directory Structure

BuildProject ensures consistent project organization:

```python
# Essential components created
- __init__.py with version tracking
- semantic.py implementing SemanticDefaults
- operators.py with operator registry
- examples.py with semantic_theories and example_range
- Proper Python package structure with imports
```

### Module Initialization

Project initialization includes version management and licensing:

```python
# Version tracking in __init__.py
__version__ = "0.1.0"  # Theory version
__model_checker_version__ = "1.2.3"  # Compatible ModelChecker version

# Automatic license and citation files
LICENSE.md - GPL-3.0 license text
CITATION.md - Academic citation template
```

## Integration Points

### Component Connection

BuildExample serves as the central integration point connecting all framework components:

```text
BuildModule (orchestrator)
    ├── Settings Management
    ├── Theory Loading
    └── BuildExample (pipeline)
        ├── Syntax (parsing)
        ├── ModelConstraints (bridging)
        ├── ModelStructure (solving)
        └── Result Extraction
```

### Settings Flow

Settings flow through the system with proper validation at each stage:

```python
# Settings flow path
1. Module flags → BuildModule
2. BuildModule + general_settings → SettingsManager
3. SettingsManager + example_settings → validated settings
4. Validated settings → all components (Syntax, Semantics, Model)
```

### Theory Loading

Theory loading supports both static and dynamic registration:

```python
# Static registration (in semantic_theories dict)
"Theory_Name": {
    "semantics": SemanticClass,
    "proposition": PropositionClass,
    "model": ModelClass,
    "operators": operator_collection
}

# Dynamic loading (operator registry)
registry = LogosOperatorRegistry()
registry.load_subtheories(['modal', 'constitutive'])
operators = registry.operators
```

### Result Interpretation

Results flow from Z3 models through interpretation layers:

```python
# Result interpretation pipeline
Z3 Model → ModelStructure.interpret()
         → Sentence.update_proposition()
         → Proposition evaluation
         → Truth value extraction
         → Formatted output display
```

## Code Examples

### Complete BuildExample Initialization

```python
from model_checker.builder import BuildModule
from model_checker.builder.example import BuildExample

# Load module with examples
module_flags = type('Flags', (), {
    'file_path': 'theory_lib/logos/examples.py',
    'verbose': True,
    'N': 4
})()
build_module = BuildModule(module_flags)

# Get example case
example_case = build_module.example_range['MODAL_TH_1']
semantic_theory = build_module.semantic_theories['Brast-McKie']

# Create and process example
example = BuildExample(build_module, semantic_theory, example_case, 'Brast-McKie')
```

### Settings Management Example

```python
# Module general_settings
general_settings = {
    'N': 3,
    'max_time': 1,
    'contingent': False
}

# Example-specific override
MODAL_TH_1_settings = {
    'N': 4,  # Override N for this example
    'contingent': True  # Make contingent
}

# Command-line override
# model-checker examples.py --N=5 --verbose
# Final N will be 5 (command-line wins)
```

### Theory Loading and Operator Setup

```python
from model_checker.theory_lib.logos import LogosOperatorRegistry
from model_checker.theory_lib.logos import (
    LogosSemantics, LogosProposition, LogosModelStructure
)

# Create operator registry
registry = LogosOperatorRegistry()

# Load specific subtheories
registry.load_subtheories(['modal', 'constitutive', 'counterfactual'])

# Build semantic theory dictionary
semantic_theory = {
    "semantics": LogosSemantics,
    "proposition": LogosProposition,
    "model": LogosModelStructure,
    "operators": registry.operators
}
```

### Complete Pipeline Example

```python
# Example: Running "A ∧ B → C" through the pipeline

# 1. Input definition
premises = ["A \\wedge B"]
conclusions = ["C"]
settings = {"N": 3, "contingent": True}

# 2. BuildModule loads and validates
build_module = BuildModule(module_flags)
example_case = [premises, conclusions, settings]

# 3. BuildExample creates pipeline
example = BuildExample(
    build_module,
    semantic_theory,
    example_case,
    theory_name="Brast-McKie"
)

# 4. Syntax parsing (in BuildExample.__init__)
# Sentences created: "A \\wedge B", "C", "A", "B"
# Operators identified: AndOperator

# 5. ModelConstraints generation
# Frame constraints + proposition constraints + evaluation constraints

# 6. Z3 solving in ModelStructure
# Find satisfying assignment for all constraints

# 7. Result interpretation
if example.model_structure.z3_model_status:
    print("Countermodel found - argument is invalid")
else:
    print("No countermodel - argument is valid")
```

## References

### Implementation Files
- `model_checker/builder/module.py` - BuildModule implementation
- `model_checker/builder/example.py` - BuildExample implementation  
- `model_checker/builder/project.py` - BuildProject implementation
- `model_checker/settings.py` - Settings management system

### Related Documentation
- [Syntax Pipeline](SYNTAX.md) - How formulas are parsed
- [Semantics Pipeline](SEMANTICS.md) - Constraint generation
- [Model Finding](MODELS.md) - SMT solving process
- [Development Guide](../../Code/docs/DEVELOPMENT.md) - Creating new theories

---

[← Back to Methodology](README.md) | [Syntax Pipeline →](SYNTAX.md)
