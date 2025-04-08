# ModelChecker API Refactoring Strategies

This document presents strategies for improving the ModelChecker API architecture with different approaches based on scope, complexity, and backward compatibility considerations.

## Strategy Overview

The following strategies are organized from least to most impactful, with short-term improvements first and more comprehensive architectural changes later.

## Short-Term Improvements

### Strategy 1: Simplified Theory Factory

**Goal**: Create a factory pattern for theory creation that simplifies the API without major refactoring.

**Implementation**:
```python
class TheoryFactory:
    """Factory for creating theory instances."""
    @staticmethod
    def create_theory(name, settings=None):
        """Create a theory instance by name."""
        settings = settings or {}
        if name == "default":
            from model_checker.theory_lib.default import (
                Semantics, Proposition, ModelStructure, default_operators
            )
            return {
                "semantics": Semantics(settings),
                "proposition": Proposition,
                "model": ModelStructure,
                "operators": default_operators,
            }
        elif name == "exclusion":
            # Similar structure for other theories
        else:
            raise ValueError(f"Unknown theory: {name}")
```

**Benefits**:
- Simplified API for common use cases
- No significant architectural changes
- Maintains backward compatibility
- Easier onboarding for new users

**Drawbacks**:
- Less flexibility than other approaches
- May not address deeper architectural issues
- Limited extensibility

### Strategy 2: Module-Level Configuration

**Goal**: Improve configuration management across the framework with a centralized approach.

**Implementation**:
```python
class Configuration:
    """Central configuration for ModelChecker."""
    _instance = None
    
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._init_defaults()
        return cls._instance
    
    def _init_defaults(self):
        self.settings = {
            "print_constraints": False,
            "print_impossible": False,
            "print_z3": False,
            "save_output": False,
            "maximize": False,
            # More settings
        }
        
    def configure(self, **kwargs):
        """Update configuration settings."""
        self.settings.update(kwargs)
        
    def get(self, key, default=None):
        """Get a configuration setting."""
        return self.settings.get(key, default)
```

**Benefits**:
- Consistent configuration across components
- Global defaults with local overrides
- Simplified initialization code
- Centralized documentation of settings

**Drawbacks**:
- Potential for global state issues
- May hide dependencies between components
- Requires careful thread safety consideration

### Strategy 3: API Facade Pattern

**Goal**: Create a simplified API facade that hides implementation details and provides a more intuitive interface.

**Implementation**:
```python
class ModelChecker:
    """High-level API for model checking."""
    def __init__(self, theory_name="default", settings=None):
        self.theory_name = theory_name
        self.settings = settings or {}
        self._theory = self._load_theory()
        
    def _load_theory(self):
        """Load the specified theory."""
        from model_checker.utils import get_theory
        from model_checker.theory_lib import get_examples
        theory = get_theory(self.theory_name)
        theory["examples"] = get_examples(self.theory_name)
        return theory
        
    def check_formula(self, formula, premises=None):
        """Check if a formula follows from premises."""
        example = self._create_example(premises, [formula])
        return self._check_example(example)
        
    def find_model(self, formulas):
        """Find a model satisfying all formulas."""
        example = self._create_example(formulas, [])
        return self._check_example(example)
        
    def _create_example(self, premises, conclusions):
        """Create an example from premises and conclusions."""
        premises = premises or []
        return [premises, conclusions, self.settings]
        
    def _check_example(self, example):
        """Check an example using BuildExample."""
        from model_checker import BuildExample
        model = BuildExample("custom", self._theory, example)
        return model.result
```

**Benefits**:
- Simplified API for common use cases
- Hides implementation details
- More intuitive for new users
- Can evolve independently of internal implementation

**Drawbacks**:
- Additional layer of abstraction
- May limit access to advanced features
- Potential duplication with existing BuildExample functionality

## Medium-Term Improvements

### Strategy 4: Standardized Theory Registry

**Goal**: Create a centralized registry system for theory implementations to reduce redundancy and simplify extension.

**Implementation**:
```python
class TheoryRegistry:
    """Central registry for theory implementations."""
    def __init__(self):
        self._theories = {}
        
    def register(self, name, theory_module):
        """Register a theory implementation."""
        self._theories[name] = theory_module
        
    def get_theory(self, name):
        """Get a registered theory by name."""
        if name not in self._theories:
            self._load_theory(name)
        return self._theories[name]
        
    def get_examples(self, theory_name):
        """Get examples from a theory."""
        theory = self.get_theory(theory_name)
        return self._get_examples_from_theory(theory)
        
    def _load_theory(self, name):
        """Dynamic loading of theory implementations."""
        # Load theory dynamically
```

**Benefits**:
- Centralized management of theories
- Standardized interface for all theories
- Automatic discovery of new theories
- Simplified extension process

**Drawbacks**:
- Requires significant refactoring
- May introduce compatibility issues with existing code
- Adds architectural complexity

### Strategy 5: Enhanced Operator System

**Goal**: Refactor the operator system to support more complex logical operators and reduce duplication.

**Implementation**:
```python
class EnhancedOperator:
    """Base class for logical operators with composition support."""
    def __init__(self, name, symbol, arity):
        self.name = name
        self.symbol = symbol
        self.arity = arity
        
    def compose(self, other_operator):
        """Create a new operator by composition."""
        return ComposedOperator(self, other_operator)
        
    # Core semantic methods
    
class ComposedOperator(EnhancedOperator):
    """An operator composed of multiple operators."""
    def __init__(self, outer, inner):
        self.outer = outer
        self.inner = inner
        super().__init__(
            f"{outer.name}_{inner.name}",
            f"{outer.symbol}({inner.symbol})",
            max(outer.arity, inner.arity)
        )
        
    # Implementation of semantic methods through composition
```

**Benefits**:
- Reduced duplication across theory implementations
- Support for operator composition and transformation
- Centralized operator management
- Easier creation of derived operators

**Drawbacks**:
- Significant refactoring required
- Potential performance impact from abstraction
- May complicate simple theory implementations

### Strategy 6: Inheritance-Based Theory Structure

**Goal**: Refactor theories to use inheritance more effectively, allowing specialized theories to build on general ones.

**Implementation**:
```python
class BaseSemantics:
    """Base semantics shared by all theories."""
    def __init__(self, settings):
        self.settings = settings
        # Common semantics implementation
        
class BaseProposition:
    """Base proposition logic shared by all theories."""
    def __init__(self, formula, model):
        self.formula = formula
        self.model = model
        # Common proposition implementation
```

**Benefits**:
- Clear inheritance hierarchy
- Reduced code duplication
- Easier to create derivative theories
- Better code organization

**Drawbacks**:
- May force unnatural hierarchies in some cases
- Potential for "diamond problem" in multiple inheritance
- Requires careful design of base classes

## Long-Term Improvements

### Strategy 7: Protocol-based Theory Interface

**Goal**: Define formal interfaces for theory implementations to ensure consistency.

**Implementation**:
```python
from typing import Protocol, Dict, Any, List

class SemanticProtocol(Protocol):
    """Protocol for semantic implementations."""
    def __init__(self, settings: Dict[str, Any]) -> None: ...
    def compatible(self, a: Any, b: Any) -> bool: ...
    # Other required methods

class PropositionProtocol(Protocol):
    """Protocol for proposition implementations."""
    def __init__(self, formula: str, model: Any) -> None: ...
    def evaluate(self) -> bool: ...
    # Other required methods

class TheoryProtocol(Protocol):
    """Protocol for complete theory implementations."""
    semantics: type
    proposition: type
    model: type
    operators: Dict[str, Any]
```

**Benefits**:
- Clear contract for theory implementations
- Static type checking support
- Self-documenting interfaces
- Easier debugging of implementation issues

**Drawbacks**:
- Requires Python 3.8+ for full Protocol support
- May constrain flexibility for specialized theories
- Additional validation overhead

### Strategy 8: Composable Model Components

**Goal**: Refactor the core model checking engine to support more flexible composition of components.

**Implementation**:
```python
class ConstraintGenerator:
    """Generates Z3 constraints from logical formulas."""
    def generate_constraints(self, formula, context):
        """Generate constraints for a formula."""
        
class ModelSolver:
    """Solves constraint satisfaction problems."""
    def solve(self, constraints, settings):
        """Find a model satisfying constraints."""
        
class ResultInterpreter:
    """Interprets solver results into semantic terms."""
    def interpret(self, solver_result, context):
        """Interpret solver results."""
```

**Benefits**:
- Greater flexibility in component replacement
- Easier testing of individual components
- Support for alternative constraint solvers beyond Z3
- More modular architecture

**Drawbacks**:
- Significant refactoring required
- May increase complexity for simple use cases
- Potential performance overhead from abstraction

## Implementation Recommendations

### Phased Implementation Approach

For the most effective improvement of the API without disrupting existing functionality:

1. **Phase 1: Quick Wins** (1-2 months)
   - Implement Strategy 1 (Simplified Theory Factory)
   - Add Strategy 3 (API Facade Pattern) as an alternative interface
   - These provide immediate usability improvements

2. **Phase 2: Foundation Improvements** (2-4 months)
   - Implement Strategy 2 (Module-Level Configuration)
   - Begin implementation of Strategy 4 (Standardized Theory Registry)
   - These establish better architectural patterns

3. **Phase 3: Enhanced Architecture** (4-6 months)
   - Complete Strategy 4 (Standardized Theory Registry)
   - Implement Strategy 5 (Enhanced Operator System)
   - Begin Strategy 6 (Inheritance-Based Structure)
   - These improve internal organization and reduce duplication

4. **Phase 4: Advanced Features** (6+ months)
   - Implement Strategy 7 (Protocol-based Interface)
   - Explore Strategy 8 (Composable Components)
   - These provide future-proof architecture with stronger interfaces

### Implementation Priority Matrix

| Strategy | Impact | Effort | Risk | Priority |
|----------|--------|--------|------|----------|
| 1. Simplified Theory Factory | Medium | Low | Low | High |
| 2. Module-Level Configuration | Medium | Low | Medium | High |
| 3. API Facade Pattern | High | Low | Low | High |
| 4. Standardized Theory Registry | High | Medium | Medium | Medium |
| 5. Enhanced Operator System | Medium | High | Medium | Medium |
| 6. Inheritance-Based Structure | Medium | High | High | Medium |
| 7. Protocol-based Interface | Medium | Medium | High | Low |
| 8. Composable Components | High | High | High | Low |

### Development and Testing Considerations

For each implementation phase:

1. **Documentation**: Update documentation to reflect API changes
2. **Backward Compatibility**: Ensure old code still works with new architecture
3. **Testing**: Add tests for new components and interfaces
4. **Deprecation Strategy**: Plan for gradual deprecation of old interfaces
5. **Migration Guide**: Provide guides for users to adopt new patterns

## Conclusion

By implementing these strategies in a phased approach, the ModelChecker API can evolve to be more usable, maintainable, and extensible while preserving backward compatibility for existing users.
