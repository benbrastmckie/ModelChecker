# Theory Architecture in ModelChecker

This document provides detailed implementation guidance for the two architectural patterns supported by ModelChecker theories. For overview and pattern selection guidance, see [README.md](README.md#theory-architecture-patterns).

## Architectural Pattern Implementation

ModelChecker supports two distinct architectural patterns, each optimized for different theory complexities:

- **Simple Pattern**: Single-file operator organization (e.g., Exclusion Theory)
- **Modular Pattern**: Subtheory-based operator organization (e.g., Logos Theory)

Both patterns share [common interface elements](README.md#common-interface-elements) while adapting their internal structure to semantic complexity.

## Simple Pattern Architecture

### Directory Structure

```
theory_lib/
└── simple_theory/
    ├── README.md           # Theory documentation
    ├── __init__.py         # Public API exports
    ├── semantic.py         # Core semantic framework
    ├── operators.py        # All operators in single file
    ├── examples.py         # Test cases and examples
    ├── tests/              # Unit tests
    │   ├── __init__.py
    │   ├── test_operators.py
    │   ├── test_examples.py
    │   └── test_semantic.py
    └── notebooks/          # Jupyter demonstrations (optional)
        └── simple_theory_demo.ipynb
```

### Core Implementation Files

#### 1. `semantic.py` - Semantic Framework

```python
from model_checker.model import SemanticDefaults, PropositionDefaults, ModelDefaults

class SimpleSemantics(SemanticDefaults):
    """Core semantics for simple theory."""
    
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'max_time': 1,
        'theory_specific_setting': False,  # Only include relevant settings
    }
    
    DEFAULT_GENERAL_SETTINGS = {
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
    }

    def __init__(self, settings=None):
        super().__init__(settings)
        self._initialize_theory_primitives()
        
    def _initialize_theory_primitives(self):
        """Initialize theory-specific semantic primitives."""
        # Theory-specific Z3 functions and relations
        self.theory_relation = self.z3.Function('theory_rel', 
                                               self.StateSort, self.StateSort, self.z3.BoolSort())
        
    # Implement core semantic methods specific to your theory
    def theory_specific_relation(self, s1, s2):
        """Implement theory-specific semantic relation."""
        return self.theory_relation(s1, s2)

class SimpleProposition(PropositionDefaults):
    """Proposition implementation for simple theory."""
    # Standard proposition implementation
    
class SimpleStructure(ModelDefaults):
    """Model structure for simple theory."""
    # Standard model structure implementation

__all__ = ["SimpleSemantics", "SimpleProposition", "SimpleStructure"]
```

#### 2. `operators.py` - Unified Operator Collection

```python
from model_checker.syntactic import Operator, DefinedOperator, OperatorCollection

class TheorySpecificOperator(Operator):
    """Primary operator unique to this theory."""
    def __init__(self):
        super().__init__("theory_op", "\\theoryop", 2)
    
    def semantic_clause(self, sentence):
        """Implement operator semantics using theory primitives."""
        # Use semantics from semantic.py
        
class AnotherOperator(Operator):
    """Another operator in the theory."""
    # Implementation...

# Single collection containing all operators
simple_operators = OperatorCollection(
    # Standard extensional operators
    NegationOperator,
    AndOperator, 
    OrOperator,
    
    # Theory-specific operators
    TheorySpecificOperator,
    AnotherOperator,
)

__all__ = ["simple_operators"]
```

#### 3. `examples.py` - Theory Examples

```python
from .semantic import SimpleSemantics, SimpleProposition, SimpleStructure
from .operators import simple_operators

# Example definitions using standard format
SIMPLE_CM_1_example = [
    ['premise'],           # premises
    ['conclusion'],        # conclusions  
    {'N': 2, 'expectation': True}  # settings
]

SIMPLE_TH_1_example = [
    [],                    # premises
    ['valid_formula'],     # conclusions
    {'N': 2, 'expectation': False}  # settings
]

# Required dictionaries
semantic_theories = {
    "SimpleTheory": {
        "semantics": SimpleSemantics,
        "proposition": SimpleProposition,
        "model": SimpleStructure,
        "operators": simple_operators
    }
}

example_range = {
    "SIMPLE_CM_1": SIMPLE_CM_1_example,
    "SIMPLE_TH_1": SIMPLE_TH_1_example,
}

test_example_range = example_range  # Same as example_range for simple theories

general_settings = {
    "print_constraints": False,
    "print_z3": False,
    "save_output": False,
}

__all__ = ['semantic_theories', 'example_range', 'test_example_range', 'general_settings']
```

#### 4. `__init__.py` - Public API

```python
"""
SimpleTheory - A semantic theory for ModelChecker

Brief description of theory and its key features.
"""

from .semantic import SimpleSemantics, SimpleProposition, SimpleStructure
from .operators import simple_operators
from .examples import semantic_theories, example_range, general_settings

# For theories with simple APIs, export everything directly
__all__ = [
    'SimpleSemantics', 'SimpleProposition', 'SimpleStructure',
    'simple_operators', 'semantic_theories', 'example_range', 'general_settings'
]
```

## Modular Pattern Architecture

### Directory Structure

```
theory_lib/
└── modular_theory/
    ├── README.md           # Theory documentation
    ├── __init__.py         # Public API with get_theory() function
    ├── semantic.py         # Core semantic framework
    ├── operators.py        # Registry and loading system
    ├── examples.py         # Cross-subtheory examples
    ├── subtheories/        # Organized operator groups
    │   ├── __init__.py
    │   ├── extensional/
    │   │   ├── __init__.py
    │   │   ├── operators.py
    │   │   ├── examples.py
    │   │   └── tests/
    │   ├── modal/
    │   │   ├── __init__.py
    │   │   ├── operators.py
    │   │   ├── examples.py
    │   │   └── tests/
    │   └── constitutive/
    │       ├── __init__.py
    │       ├── operators.py
    │       ├── examples.py
    │       └── tests/
    ├── tests/              # Integration and core tests
    │   ├── __init__.py
    │   ├── test_registry.py
    │   ├── test_semantic_methods.py
    │   └── test_integration.py
    └── notebooks/          # Jupyter demonstrations
        ├── modular_theory_intro.ipynb
        └── subtheory_demos/
            ├── extensional_demo.ipynb
            └── modal_demo.ipynb
```

### Core Implementation Files

#### 1. `semantic.py` - Shared Semantic Framework

```python
from model_checker.model import SemanticDefaults, PropositionDefaults, ModelDefaults

class ModularSemantics(SemanticDefaults):
    """Shared semantic framework for modular theory."""
    
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'max_time': 1,
        # Include settings relevant across subtheories
    }
    
    def __init__(self, settings=None):
        super().__init__(settings)
        self.loaded_subtheories = set()
        
    def load_subtheories(self, subtheory_names):
        """Load specified subtheories into the semantic framework."""
        for name in subtheory_names:
            if name not in self.loaded_subtheories:
                self._load_subtheory_primitives(name)
                self.loaded_subtheories.add(name)
                
    def _load_subtheory_primitives(self, subtheory_name):
        """Load semantic primitives for a specific subtheory."""
        if subtheory_name == "modal":
            self._initialize_modal_primitives()
        elif subtheory_name == "constitutive":
            self._initialize_constitutive_primitives()
        # Add other subtheories...
        
    def _initialize_modal_primitives(self):
        """Initialize modal-specific semantic primitives."""
        self.accessibility = self.z3.Function('accessible', 
                                            self.StateSort, self.StateSort, self.z3.BoolSort())

class ModularProposition(PropositionDefaults):
    """Proposition implementation supporting multiple subtheories."""
    # Implementation that works across subtheories
    
class ModularStructure(ModelDefaults):  
    """Model structure supporting multiple subtheories."""
    # Implementation that handles different operator types

__all__ = ["ModularSemantics", "ModularProposition", "ModularStructure"]
```

#### 2. `operators.py` - Registry and Loading System

```python
from model_checker.syntactic import OperatorCollection

class ModularOperatorRegistry:
    """Registry for loading operators from subtheories."""
    
    def __init__(self):
        self.loaded_subtheories = {}
        self.operator_collection = None
        
    def load_subtheories(self, subtheory_names):
        """Load operators from specified subtheories."""
        all_operators = []
        
        for name in subtheory_names:
            if name not in self.loaded_subtheories:
                operators = self._load_subtheory_operators(name)
                self.loaded_subtheories[name] = operators
                all_operators.extend(operators)
                
        self.operator_collection = OperatorCollection(*all_operators)
        return self.operator_collection
        
    def _load_subtheory_operators(self, subtheory_name):
        """Load operators from a specific subtheory."""
        if subtheory_name == "extensional":
            from .subtheories.extensional import get_operators
            return list(get_operators().values())
        elif subtheory_name == "modal":
            from .subtheories.modal import get_operators  
            return list(get_operators().values())
        # Add other subtheories...
        
    def get_operators(self):
        """Get the current operator collection."""
        return self.operator_collection

__all__ = ["ModularOperatorRegistry"]
```

#### 3. `subtheories/extensional/operators.py` - Subtheory Operators

```python
from model_checker.syntactic import Operator, DefinedOperator

class NegationOperator(Operator):
    """Negation operator for extensional logic."""
    def __init__(self):
        super().__init__("negation", "\\neg", 1)
    
    def semantic_clause(self, sentence):
        """Implement negation semantics."""
        # Implementation using shared semantic framework

class ConjunctionOperator(Operator):
    """Conjunction operator for extensional logic."""
    def __init__(self):
        super().__init__("conjunction", "\\wedge", 2)
    
    def semantic_clause(self, sentence):
        """Implement conjunction semantics."""
        # Implementation...

def get_operators():
    """Return dictionary of extensional operators."""
    return {
        '\\neg': NegationOperator,
        '\\wedge': ConjunctionOperator,
    }

__all__ = ['get_operators']
```

#### 4. `__init__.py` - Modular Public API

```python
"""
ModularTheory - A comprehensive semantic theory for ModelChecker

This theory provides selective loading of operator subtheories.
"""

from .semantic import ModularSemantics, ModularProposition, ModularStructure
from .operators import ModularOperatorRegistry

def get_theory(subtheories=None):
    """
    Get theory instance with specified subtheories.
    
    Args:
        subtheories: List of subtheory names to load, or None for default set
        
    Returns:
        Dict with 'semantics', 'proposition', 'model' classes and 'operators' collection
    """
    registry = ModularOperatorRegistry()
    
    if subtheories is None:
        # Default subtheories
        subtheories = ['extensional', 'modal']
    
    operators = registry.load_subtheories(subtheories)
    
    return {
        'semantics': ModularSemantics,
        'proposition': ModularProposition, 
        'model': ModularStructure,
        'operators': operators
    }

# Convenience exports
Semantics = ModularSemantics
Proposition = ModularProposition
ModelStructure = ModularStructure

__all__ = [
    'get_theory', 'Semantics', 'Proposition', 'ModelStructure'
]
```

## Common Implementation Requirements

### Testing Infrastructure

Both patterns must implement [standardized testing](tests/README.md#theory-testing-framework-guide):

- **Simple Pattern**: Tests in single `tests/` directory
- **Modular Pattern**: Tests at both theory and subtheory levels

### Jupyter Integration

Both patterns must support [Jupyter integration](../jupyter/README.md):

```python
# Both patterns work with:
from model_checker.jupyter.interactive import check_formula
result = check_formula("p → q", theory_name="your_theory")
```

### Documentation Standards

Both patterns require:

- Comprehensive `README.md` following [standard format](README.md)
- Examples demonstrating key features
- API documentation for all public classes and methods

## Pattern Selection Guidelines

### Choose Simple Pattern When:
- Theory has fewer than 10 operators
- Operators don't form natural logical groupings
- Rapid prototyping is priority
- Theory addresses a focused semantic question

### Choose Modular Pattern When:
- Theory has 10+ operators across logical domains
- Operators benefit from categorical organization
- Selective operator loading is valuable
- Multiple developers will contribute
- Theory integrates multiple logical systems

## Migration Between Patterns

### Simple to Modular Migration

1. Create `subtheories/` directory structure
2. Group operators by logical domain
3. Implement operator registry system
4. Add `get_theory()` function with selective loading
5. Update tests to handle both unified and selective testing

### Modular to Simple Migration

1. Flatten all operators into single `operators.py`
2. Remove registry and loading system
3. Simplify `__init__.py` to direct exports
4. Consolidate tests into single directory
5. Update documentation to reflect unified approach

## Best Practices

### For Both Patterns:
- Follow [common interface standards](README.md#common-interface-elements)
- Implement comprehensive testing per [Theory Testing Framework Guide](tests/README.md#theory-testing-framework-guide)
- Provide clear documentation and examples
- Support Jupyter integration
- Use consistent naming conventions

### Simple Pattern Specific:
- Keep operator count reasonable (< 10)
- Organize operators logically within single file
- Focus on clarity and direct access
- Minimize abstraction overhead

### Modular Pattern Specific:
- Organize subtheories by logical domains
- Implement dependency resolution between subtheories
- Provide clear subtheory documentation
- Support selective loading efficiently
- Maintain consistency across subtheories

This architecture documentation ensures both simple and modular theories can be implemented effectively while maintaining consistency and interoperability within the ModelChecker framework.