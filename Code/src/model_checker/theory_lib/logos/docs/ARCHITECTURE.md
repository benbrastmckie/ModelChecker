# Logos Theory Architecture

This document provides a comprehensive technical overview of the Logos theory's architecture, design patterns, and implementation details.

## Table of Contents

- [Overview](#overview)
- [Core Design Principles](#core-design-principles)
- [System Architecture](#system-architecture)
- [Component Deep Dive](#component-deep-dive)
- [Operator Registry System](#operator-registry-system)
- [Semantic Framework](#semantic-framework)
- [Model Construction](#model-construction)
- [Integration Points](#integration-points)
- [Performance Considerations](#performance-considerations)
- [Extension Patterns](#extension-patterns)

## Overview

The Logos theory implements a **three-layer modular architecture** that provides a unified hyperintensional semantic framework with dynamic operator loading capabilities. Unlike monolithic semantic theories, Logos separates concerns across multiple levels while maintaining semantic consistency.

### Key Architectural Features

1. **Modular Subtheory System** - Independent operator modules that can be loaded on demand
2. **Dynamic Operator Registry** - Runtime operator loading with dependency resolution
3. **Unified Semantic Core** - Shared truthmaker semantics across all operators
4. **Lazy Loading Pattern** - Operators loaded only when needed
5. **Clean Separation of Concerns** - Clear boundaries between components

## Core Design Principles

### 1. Modularity First
Each subtheory (extensional, modal, constitutive, counterfactual, relevance) is completely self-contained:
- Independent operator definitions
- Isolated test suites
- Separate documentation
- Clear dependency declarations

### 2. Semantic Consistency
All operators share the same underlying semantic framework:
- Bilateral propositions (verifiers and falsifiers)
- State-based truthmaker semantics
- Consistent evaluation patterns
- Unified constraint generation

### 3. Dynamic Composition
The system supports runtime composition of logical systems:
- Load any combination of subtheories
- Automatic dependency resolution
- No compile-time coupling
- Flexible theory construction

### 4. Performance Optimization
Architecture designed for efficiency:
- Lazy module loading
- Operator caching
- Minimal memory footprint
- Optimized constraint patterns

## System Architecture

### Layer 1: Core Framework

```
logos/
├── semantic.py          # LogosSemantics base class
├── operators.py         # LogosOperatorRegistry
├── proposition.py       # (inherited from semantic.py)
└── model_structure.py   # (inherited from semantic.py)
```

**LogosSemantics** provides:
- Shared semantic primitives (verify, falsify, possible)
- Frame constraints (possibility downward closure)
- Truth evaluation methods
- Model construction interface

**LogosOperatorRegistry** manages:
- Dynamic operator loading
- Dependency resolution
- Operator caching
- Subtheory coordination

### Layer 2: Subtheory Modules

```
subtheories/
├── extensional/
│   ├── __init__.py
│   ├── operators.py     # Truth-functional operators
│   ├── examples.py      # Test examples
│   └── README.md        # Documentation
├── modal/
├── constitutive/
├── counterfactual/
└── relevance/
```

Each subtheory is structured identically:
- **operators.py** - Operator class definitions
- **examples.py** - Logical principle tests
- **tests/** - Unit and integration tests
- **README.md** - Subtheory documentation

### Layer 3: Integration Layer

```
logos/
├── __init__.py          # Public API
├── examples.py          # Cross-subtheory examples
├── iterate.py           # Model iteration
└── notebooks/           # Interactive demos
```

Integration components:
- Unified API through `get_theory()`
- Combined example testing
- Cross-subtheory validation
- User-facing documentation

## Component Deep Dive

### LogosSemantics Class

The semantic foundation implementing hyperintensional truthmaker semantics:

```python
class LogosSemantics(SemanticDefaults):
    """Shared semantic framework for all logos subtheories."""
    
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 16,              # Larger default for complex formulas
        'contingent': True,   # Hyperintensional distinctions
        'non_empty': True,    # Content requirement
        'non_null': True,     # Null state exclusion
        'disjoint': True,     # Clear proposition boundaries
        'max_time': 10000,    # Extended solver time
        'iterate': False,     # Model iteration control
    }
```

Key methods:
- `compatible(state_x, state_y)` - Test state compatibility via fusion
- `load_subtheories(subtheories)` - Coordinate with registry
- Frame constraint definitions
- Evaluation point management

### LogosOperatorRegistry

The dynamic loading system at the heart of Logos' modularity:

```python
class LogosOperatorRegistry:
    """Manages dynamic loading and caching of operator subtheories."""
    
    SUBTHEORY_INFO = {
        'extensional': {
            'module': 'extensional',
            'dependencies': []
        },
        'modal': {
            'module': 'modal', 
            'dependencies': ['extensional']
        },
        # ... other subtheories
    }
```

Key features:
- **Dependency Resolution** - Automatically loads required subtheories
- **Import Caching** - Modules loaded once and reused
- **Error Handling** - Graceful failures with informative messages
- **Operator Merging** - Combines operators from multiple sources

### Operator Implementation Pattern

All Logos operators follow a consistent pattern:

```python
class LogosOperator(Operator):
    """Base pattern for Logos operators."""
    
    def __init__(self):
        super().__init__(symbol, arity)
    
    def semantic_clause(self, sentence):
        """Generate Z3 constraints for this operator."""
        # Access sentence components
        x = sentence['x']
        args = sentence['args']
        
        # Define verification conditions
        verify_conditions = self._verify_conditions(x, args)
        
        # Define falsification conditions  
        falsify_conditions = self._falsify_conditions(x, args)
        
        return z3.And(verify_conditions, falsify_conditions)
```

This pattern ensures:
- Consistent constraint generation
- Bilateral semantic treatment
- Integration with Z3 solver
- Clear separation of concerns

## Operator Registry System

### Registry Architecture

The registry uses a multi-stage loading process:

1. **Initialization** - Empty operator dictionary
2. **Request Processing** - Parse subtheory list
3. **Dependency Resolution** - Build load order
4. **Module Loading** - Dynamic imports
5. **Operator Collection** - Merge into dictionary
6. **Caching** - Store for reuse

### Dependency Management

```python
def _resolve_dependencies(self, subtheories):
    """Resolve all dependencies for requested subtheories."""
    all_subtheories = set()
    
    for subtheory in subtheories:
        all_subtheories.add(subtheory)
        deps = self.SUBTHEORY_INFO[subtheory]['dependencies']
        all_subtheories.update(deps)
    
    return self._topological_sort(all_subtheories)
```

Features:
- Transitive dependency resolution
- Circular dependency detection
- Topological sorting for load order
- Clear error messages

### Operator Discovery

Each subtheory exports operators via `get_operators()`:

```python
def get_operators():
    """Return dictionary of operator name to class."""
    return {
        '\\wedge': Conjunction,
        '\\vee': Disjunction,
        '\\neg': Negation,
        # ... more operators
    }
```

This enables:
- Clear operator inventory
- Name-to-class mapping
- Easy operator addition
- Subtheory independence

## Semantic Framework

### Truthmaker Semantics

The Logos theory implements bilateral truthmaker semantics:

1. **States as Bit Vectors** - Efficient representation of atomic states
2. **Verifier Sets** - States that make propositions true
3. **Falsifier Sets** - States that make propositions false
4. **Fusion Operations** - Combining states algebraically

### Evaluation Process

```
Formula → Parse Tree → Operator Application → Z3 Constraints → Model → Evaluation
```

Each stage:
1. **Parsing** - Convert formula strings to AST
2. **Operator Dispatch** - Route to appropriate operator class
3. **Constraint Generation** - Create Z3 boolean expressions
4. **Model Finding** - Z3 solver finds satisfying assignment
5. **Result Extraction** - Convert Z3 model to semantic model

### Constraint Patterns

Common constraint patterns across operators:

```python
# Verification constraint pattern
verify = z3.Or([
    z3.And(self.semantics.is_part_of(y, x), 
           condition(y))
    for y in possible_verifiers
])

# Falsification constraint pattern  
falsify = z3.Or([
    z3.And(self.semantics.is_part_of(z, x),
           condition(z))
    for z in possible_falsifiers
])
```

## Model Construction

### BuildExample Integration

The Logos theory integrates with ModelChecker's BuildExample:

```python
# Theory loading and example checking
from model_checker import check_formula

# Check a modal identity formula
result = check_formula("(A ≡ A)", theory_name="logos")

# Or check with specific subtheories
theory = logos.get_theory(['modal', 'constitutive'])
# Use theory in custom model construction (advanced usage)
```

### Model Structure

LogosModelStructure provides:
- State space enumeration
- Possible world identification
- Proposition evaluation
- Countermodel display

### Constraint Optimization

Logos uses several optimization strategies:
- Bit vector operations for state manipulation
- Constraint sharing across similar formulas
- Early termination for unsatisfiable constraints
- Incremental solving for iteration

## Integration Points

### ModelChecker Framework

Logos integrates seamlessly with ModelChecker:
- Inherits from `SemanticDefaults`
- Uses standard `Operator` base class
- Compatible with `BuildExample`
- Supports all ModelChecker features

### Theory Comparison

Can be compared with other theories:
```python
semantic_theories = {
    "Logos": logos.get_theory(),
    "Exclusion": exclusion_theory,
    "Imposition": imposition_theory,
}
```

### Jupyter Integration

Full support for interactive exploration:
- Theory loading in notebooks
- ModelExplorer compatibility
- High-level check functions
- Visualization support

## Performance Considerations

### Memory Management

- **Lazy Loading** - Subtheories loaded on demand
- **Module Caching** - Imported modules reused
- **Operator Instances** - Created once per session
- **Selective Loading** - Load only needed operators

### Computational Complexity

- **State Space** - O(2^N) for N atomic states
- **Constraint Generation** - Linear in formula size
- **Model Finding** - NP-complete (Z3 solver)
- **Evaluation** - Polynomial in model size

### Optimization Strategies

1. **Use Smaller N** - Start with N=3, increase as needed
2. **Load Minimal Subtheories** - Only what you need
3. **Cache Theory Instances** - Reuse for multiple examples
4. **Adjust Timeouts** - Balance completeness vs speed

## Extension Patterns

### Adding New Operators

1. Create operator class in appropriate subtheory:
```python
class NewOperator(Operator):
    def __init__(self):
        super().__init__("\\new", arity)
    
    def semantic_clause(self, sentence):
        # Implementation
        pass
```

2. Add to subtheory's `get_operators()`:
```python
def get_operators():
    return {
        # ... existing operators
        '\\new': NewOperator,
    }
```

### Creating New Subtheories

1. Create directory structure:
```
subtheories/new_theory/
├── __init__.py
├── operators.py
├── examples.py
├── tests/
└── README.md
```

2. Register in `SUBTHEORY_INFO`:
```python
'new_theory': {
    'module': 'new_theory',
    'dependencies': ['extensional']
}
```

3. Implement required components
4. Add tests and documentation

### Custom Semantic Variants

Extend LogosSemantics for variants:
```python
class VariantSemantics(LogosSemantics):
    """Custom semantic variant."""
    
    def compatible(self, state_x, state_y):
        # Custom compatibility relation
        pass
```

## Best Practices

### Design Guidelines
1. Keep subtheories independent
2. Declare dependencies explicitly
3. Follow naming conventions
4. Document semantic choices

### Code Organization
1. One operator per class
2. Clear method signatures
3. Comprehensive docstrings
4. Type hints where helpful

### Testing Strategy
1. Unit tests per operator
2. Integration tests per subtheory
3. Cross-subtheory validation
4. Performance benchmarks

### Documentation Standards
1. Operator-level documentation
2. Subtheory READMEs
3. Example explanations
4. API documentation

## Conclusion

The Logos architecture represents a sophisticated approach to implementing logical systems:
- **Modular** - Load what you need
- **Extensible** - Easy to add operators
- **Performant** - Optimized for common cases
- **Maintainable** - Clear separation of concerns

This architecture enables researchers and developers to work with one of the most advanced semantic frameworks while maintaining clarity and efficiency.

---

**Navigation**: [README](README.md) | [User Guide](USER_GUIDE.md) | [Settings](SETTINGS.md) | [Iteration](ITERATE.md) | [Main README](../README.md)