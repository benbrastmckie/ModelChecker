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

The Builder Pattern in ModelChecker orchestrates the model checking pipeline through three core classes that work together to transform logical formulas into concrete semantic evaluations:

```
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│ BuildModule  │     │ BuildExample │     │ BuildProject │
│              │     │              │     │              │
│ Coordinates  │────▶│  Executes    │     │  Generates   │
│  examples    │     │  pipeline    │     │   theories   │
└──────────────┘     └──────────────┘     └──────────────┘
```

The architecture mirrors the logical inference process: take premises and conclusions, apply semantic rules, and either find a countermodel (showing invalidity) or prove none exists (confirming validity). This separation allows researchers to focus on their semantic theories while the framework handles the computational complexity.

Key insights this pattern provides:
- **Theory Independence**: Each semantic theory runs in isolation, preventing cross-contamination
- **Settings Flexibility**: Configure everything from state space size to semantic constraints
- **Comparative Analysis**: Run multiple theories on the same examples side-by-side
- **Extensibility**: Add new theories without modifying core infrastructure

For detailed architectural patterns, see [Technical Architecture](../../Code/docs/ARCHITECTURE.md). For the theoretical foundations of model checking, see [Hyperintensional Semantics](../../HYPERINTENSIONAL.md).

## BuildModule Architecture

### Module Loading

BuildModule dynamically loads Python modules containing modal logic examples and extracts the necessary components for model checking. The loading process handles both installed packages and generated projects through intelligent path detection:

```python
# Module loading process
build_module = BuildModule(module_flags)
# Process steps:
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

**Why Dynamic Loading?** This approach allows researchers to develop and test new semantic theories without modifying the core framework. You can create a standalone Python file with your logical examples and semantic definitions, and the framework will automatically discover and load the necessary components. This is particularly useful when experimenting with variations of existing theories or developing entirely new semantic frameworks.

### Settings Management

BuildModule implements a settings management system that handles theory-specific defaults, module-level settings, and command-line overrides:

Settings hierarchy (highest to lowest priority):
1. Command-line flags (--verbose, --N=5, etc.)
2. Example-specific settings (in example_range)
3. Module general_settings
4. Theory-specific defaults
5. System DEFAULT_GENERAL_SETTINGS

The settings manager validates settings based on each theory's requirements, warning about unknown settings in single-theory mode while allowing flexibility in comparison mode.

Each setting controls specific aspects of the model checking process:
- `N`: Number of atomic states (typically 3-5, max 64 due to bit vector representation)
- `contingent`: Requires atomic propositions to have both verifiers and falsifiers
- `non_empty`: Prevents empty verifier/falsifier sets
- `disjoint`: Ensures no state both verifies and falsifies the same proposition
- `max_time`: Z3 solver timeout in seconds
- `iterate`: Number of distinct models to find (see [Iterator System](ITERATOR.md))

Command-line flags like `-v` (verbose) and `-i` (print impossible states) provide debugging output without modifying the logical analysis.

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

The dictionary structure enables theory comparison - each theory provides its own truth conditions (`semantics`), atomic proposition behavior (`proposition`), and model interpretation (`model`). The optional `dictionary` maps between different operator notations, allowing theories to share example formulas even when they use different symbols.

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

The Z3 context reset between examples prevents constraint contamination - without this isolation, constraints from one example would affect subsequent analyses. This is crucial when comparing theories: each gets a fresh solver state, ensuring fair comparison of their logical properties rather than accumulated solver heuristics.

## BuildExample Flow

The BuildExample class orchestrates the transformation from logical formulas to semantic evaluation. Think of it as a production line where each station performs a specific transformation, ultimately determining whether your inference holds:

```
Premises/Conclusions ─▶ Parse Trees ─▶ Z3 Variables ─▶ Constraints ─▶ Model/Countermodel
                        (Syntax)       (Semantics)      (Solver)       (Result)
```

### Complete Pipeline

BuildExample orchestrates the complete model checking pipeline from premises/conclusions to final model structure:

```python
# BuildExample initialization pipeline
example = BuildExample(build_module, semantic_theory, example_case, theory_name)
```

Pipeline stages:
1. Validate semantic theory components
2. Extract premises, conclusions, settings
3. Create SettingsManager with theory context
4. Initialize Syntax (parses formulas)
5. Create ModelConstraints (links syntax to semantics)
6. Build ModelStructure (Z3 solving)
7. Interpret sentences (evaluate in model)

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

The `is_comparison` flag changes validation behavior: in single-theory mode, unknown settings trigger warnings to catch typos, while comparison mode silently ignores theory-specific settings that don't apply to all theories. This allows unified example files that work across different semantic frameworks.

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

The `operators` collection maps LaTeX notation (like `\\wedge`, `\\Box`) to their semantic implementations. Each operator class defines its own truth conditions through `extended_verify` and `extended_falsify` methods. The Syntax class discovers which operators are actually used in the formulas, enabling automatic dependency resolution - you don't need to manually specify that conjunction requires the extensional subtheory.

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
```

Generated structure:
```
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

Essential components created:
- `__init__.py` with version tracking
- `semantic.py` implementing SemanticDefaults
- `operators.py` with operator registry
- `examples.py` with semantic_theories and example_range
- Proper Python package structure with imports

### Module Initialization

Project initialization includes version management and licensing:

```python
# Version tracking in __init__.py
__version__ = "0.1.0"  # Theory version
__model_checker_version__ = "1.2.3"  # Compatible ModelChecker version
```

Automatic license and citation files:
- `LICENSE.md` - GPL-3.0 license text
- `CITATION.md` - Academic citation template

## Integration Points

The builder pattern's strength lies in how components integrate while maintaining independence. Each integration point serves a specific purpose in the overall architecture, enabling both flexibility and robustness. Understanding these connections helps when extending the framework or debugging unexpected behavior.

### Component Connections

BuildExample serves as the central integration point connecting all framework components:

```
┌─────────────────────────────────────────────────────────────────┐
│                          BuildModule                            │
│  ┌─────────────┐  ┌──────────────┐  ┌────────────────────────┐  │
│  │   Settings  │  │    Theory    │  │   Example Execution    │  │
│  │  Management │  │   Loading    │  │    (orchestration)     │  │
│  └─────────────┘  └──────────────┘  └────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ creates & configures
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                          BuildExample                           │
│                                                                 │
│  ┌─────────────┐         ┌──────────────────┐                   │
│  │   Syntax    │────────▶│ ModelConstraints │                   │
│  │  (parsing)  │  AST    │   (bridging)     │                   │
│  └─────────────┘         └────────┬─────────┘                   │
│                                   │ constraints                 │
│                                   ▼                             │
│                          ┌──────────────────┐                   │
│                          │  ModelStructure  │                   │
│                          │    (solving)     │                   │
│                          └────────┬─────────┘                   │
│                                   │ Z3 model                    │
│                                   ▼                             │
│                          ┌──────────────────┐                   │
│                          │     Results      │                   │
│                          │   (extraction)   │                   │
│                          └──────────────────┘                   │
└─────────────────────────────────────────────────────────────────┘
```

This architecture ensures clean separation of concerns: BuildModule handles orchestration and configuration, BuildExample manages the pipeline flow, and each component focuses on its specific transformation of the logical problem.

### Settings Flow

Settings flow through the system with proper validation at each stage:

```
┌─────────────────┐
│ Command Line    │ ──────────────────────────┐
│ (-z, -i, ...)   │                           │ Highest
└─────────────────┘                           │ Priority
                                              ▼
┌─────────────────┐                    ┌──────────────┐
│ Example Settings│ ─────────────────▶ │              │
│ {'N': 4, ...}   │                    │   Settings   │
└─────────────────┘                    │   Manager    │
                                       │              │
┌─────────────────┐                    │ (validates & │
│ Module General  │ ─────────────────▶ │   merges)    │
│ {'N': 3, ...}   │                    │              │
└─────────────────┘                    └──────┬───────┘
                                              │
┌─────────────────┐                           │
│ Theory Defaults │ ──────────────────────────┘
│ {'N': 16, ...}  │                    Lowest
└─────────────────┘                    Priority
                                              
                                              ▼
                        ┌─────────────────────────────────────┐
                        │      Validated Settings             │
                        │  {'N': 5, 'contingent': True, ...} │
                        └──────────────┬──────────────────────┘
                                       │
                    ┌──────────────────┼──────────────────┐
                    ▼                  ▼                  ▼
              ┌──────────┐      ┌──────────┐      ┌────────────┐
              │  Syntax  │      │Semantics │      │   Model    │
              └──────────┘      └──────────┘      └────────────┘
```

Each component receives the same validated settings, ensuring consistent behavior. The priority cascade allows fine-grained control: set theory defaults for typical usage, override per-module for specific investigations, override per-example for edge cases, and use command-line for quick experiments.

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

**Static vs Dynamic Loading**: Static registration suits fixed theories where all components are known upfront. Dynamic loading excels when theories have modular subtheories - load only what you need. For instance, if your examples only use modal operators, loading the counterfactual subtheory wastes memory and slows constraint generation. The registry pattern also handles operator dependencies automatically.

### Result Interpretation

Results flow from Z3 models through interpretation layers:

Result interpretation pipeline:
```
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

Each stage transforms the logical problem: strings become parse trees, trees become Z3 variables, variables get constrained by semantic rules, and the solver either finds a satisfying assignment (countermodel) or proves none exists (validity). The countermodel, if found, shows exactly which states verify/falsify each proposition, revealing why the inference fails.

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
