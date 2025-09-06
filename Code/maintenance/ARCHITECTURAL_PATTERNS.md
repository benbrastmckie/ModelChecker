# Architectural Patterns

[← Method Complexity](METHOD_COMPLEXITY.md) | [Back to Maintenance](README.md) | [Utility Organization →](UTILITY_ORGANIZATION.md)

## Overview

This document describes **architectural patterns and design principles** that promote maintainable, testable code in the ModelChecker framework. These patterns build on the successful protocol-based architecture established in the builder/ package and provide guidance for extending these concepts to other components.

**Philosophy:** Good architecture should **emerge from practical needs**, not imposed abstractions. These patterns provide flexible guidance for building clean, maintainable code without over-engineering simple solutions.

## Core Architectural Principles

### 1. Composition Over Inheritance
**Prefer building functionality through composition rather than deep inheritance hierarchies.**

```python
# Good: Composition-based design
class ModelChecker:
    def __init__(self, validator=None, runner=None, formatter=None):
        self.validator = validator or DefaultValidator()
        self.runner = runner or DefaultRunner()
        self.formatter = formatter or DefaultFormatter()
    
    def process_model(self, data):
        if not self.validator.validate(data):
            raise ValidationError("Invalid model data")
        result = self.runner.execute(data)
        return self.formatter.format_result(result)

# Avoid: Deep inheritance for configuration
class BaseModelChecker:
    pass
class ConfigurableModelChecker(BaseModelChecker):
    pass
class ValidatingModelChecker(ConfigurableModelChecker):  # Getting complex...
    pass
```

### 2. Protocol-Based Interfaces
**Build on the proven protocol pattern for clear contracts and testability.**

The builder/ package demonstrates effective protocol usage. Extend this pattern thoughtfully:

```python
# Successful pattern from builder/protocols.py
from typing import Protocol, Any

class IValidator(Protocol):
    """Clear interface for validation functionality."""
    
    def validate(self, data: Any) -> bool:
        """Validate data, returning True if valid."""
        ...
    
    def get_validation_errors(self) -> List[str]:
        """Return list of validation error messages."""
        ...

# Implementation can be simple
class FormulaValidator:
    def __init__(self):
        self.errors = []
    
    def validate(self, formula: str) -> bool:
        self.errors.clear()
        # Validation logic...
        return len(self.errors) == 0
    
    def get_validation_errors(self) -> List[str]:
        return self.errors.copy()
```

### 3. Dependency Injection
**Make dependencies explicit to improve testability and flexibility.**

```python
# Flexible dependency injection - gradual improvement approach
class ExampleProcessor:
    def __init__(self, 
                 validator: IValidator = None,
                 runner: IRunner = None,
                 output_manager: IOutputManager = None):
        """Initialize with dependencies, providing sensible defaults."""
        self.validator = validator or DefaultValidator()
        self.runner = runner or DefaultRunner()  
        self.output_manager = output_manager or DefaultOutputManager()
    
    # Easy to test with mock dependencies
    def process(self, example_data):
        if not self.validator.validate(example_data):
            raise ValidationError(self.validator.get_validation_errors())
        
        result = self.runner.execute(example_data)
        self.output_manager.save_result(result)
        return result
```

## Established Patterns in ModelChecker

### Protocol-Based Component Interfaces

The builder/ package establishes these proven patterns:

```python
# From builder/protocols.py - extend these concepts
class IModuleLoader(Protocol):
    """Interface for loading Python modules with validation."""
    def load_module(self) -> Any: ...
    def load_attribute(self, module: Any, attr_name: str) -> Any: ...

class IModelRunner(Protocol):
    """Interface for executing model checking operations."""
    def run_example(self, example_data: List, theory: Dict) -> Any: ...
    def process_iterations(self, example: Any, iterations: int) -> List: ...

# When creating new components, follow similar patterns
class ITheoryManager(Protocol):
    """Interface for theory loading and management."""
    def load_theory(self, theory_name: str) -> Dict: ...
    def get_available_theories(self) -> List[str]: ...
    def validate_theory(self, theory_data: Dict) -> bool: ...
```

### Component Factory Pattern

For managing component creation and configuration:

```python
# Gradual introduction - start simple
class ComponentFactory:
    """Factory for creating configured components."""
    
    @staticmethod
    def create_validator(validation_type: str = "default") -> IValidator:
        """Create validator with specified configuration."""
        if validation_type == "strict":
            return StrictValidator()
        elif validation_type == "permissive":  
            return PermissiveValidator()
        else:
            return DefaultValidator()
    
    @staticmethod  
    def create_runner(runner_type: str = "default") -> IRunner:
        """Create runner with specified configuration."""
        # Factory logic for different runner types
        return DefaultRunner()
```

### Error Handling Architecture

Build on the successful BuilderError hierarchy:

```python
# Extend the proven error pattern to new packages
class PackageError(Exception):
    """Base error for package-specific exceptions."""
    pass

class ConfigurationError(PackageError):
    """Configuration-related errors with helpful context."""
    
    def __init__(self, message: str, config_key: str = None, 
                 suggestion: str = None):
        formatted_message = message
        if config_key:
            formatted_message += f"\nConfiguration key: {config_key}"
        if suggestion:
            formatted_message += f"\nSuggestion: {suggestion}"
        super().__init__(formatted_message)
```

## Gradual Architectural Improvement

### Start with Current Architecture
**Don't rewrite working code to fit patterns - improve incrementally.**

```python
# Current working code - leave it alone if it works
class WorkingComponent:
    def process_data(self, data):
        # This works fine, no need to change it
        return process(data)

# New code - apply patterns from the start  
class NewComponent:
    def __init__(self, processor: IProcessor = None):
        self.processor = processor or DefaultProcessor()
    
    def process_data(self, data):
        return self.processor.process(data)
```

### Opportunistic Pattern Application

**Apply patterns when making other changes:**

```python
# When fixing bugs or adding features:

# Before: Hard to test
class ModelValidator:
    def validate(self, model):
        # Direct file access - hard to test
        config = json.load(open('config.json'))
        # Validation logic using config...

# After: Dependency injection improvement
class ModelValidator:
    def __init__(self, config_loader=None):
        self.config_loader = config_loader or JsonConfigLoader()
    
    def validate(self, model):
        # Now testable with mock config loader
        config = self.config_loader.load_config()
        # Same validation logic...
```

### Interface Evolution

**Evolve interfaces based on real usage, not theoretical needs:**

```python
# Start simple
class IProcessor(Protocol):
    def process(self, data: Any) -> Any: ...

# Evolve as needs become clear
class IProcessor(Protocol):
    def process(self, data: Any) -> Any: ...
    def validate_input(self, data: Any) -> bool: ...  # Added when needed
    def get_processing_stats(self) -> Dict: ...        # Added when needed
```

## Integration Patterns

### Package Coordination

**For inter-package communication, favor explicit interfaces:**

```python
# Clear package boundaries
class TheoryLibInterface:
    """Interface for theory library operations."""
    
    def get_theory(self, name: str) -> Dict:
        """Load theory by name."""
        # Delegates to appropriate theory package
        return theory_lib.load_theory(name)
    
    def list_theories(self) -> List[str]:
        """List available theories."""
        return theory_lib.get_available_theories()

# Usage in other packages  
class ModelChecker:
    def __init__(self, theory_interface=None):
        self.theory_interface = theory_interface or TheoryLibInterface()
```

### Configuration Management

**Centralized configuration with local overrides:**

```python
# Global configuration with package-specific extensions
class ConfigManager:
    def __init__(self, base_config=None):
        self.config = base_config or self._load_default_config()
    
    def get_package_config(self, package_name: str) -> Dict:
        """Get configuration for specific package."""
        base = self.config.get('default', {})
        package_specific = self.config.get(package_name, {})
        return {**base, **package_specific}  # Package config overrides base
```

## Testing Architecture

### Protocol-Based Testing

**Protocols make testing much easier:**

```python
# Easy to create test doubles for protocols
class MockValidator:
    def __init__(self, will_validate=True):
        self.will_validate = will_validate
        self.validation_calls = []
    
    def validate(self, data):
        self.validation_calls.append(data)
        return self.will_validate

# Test becomes simple and focused
def test_processor_handles_invalid_data():
    mock_validator = MockValidator(will_validate=False)
    processor = ExampleProcessor(validator=mock_validator)
    
    with pytest.raises(ValidationError):
        processor.process("invalid_data")
    
    assert "invalid_data" in mock_validator.validation_calls
```

### Component Integration Testing

**Test component interactions without mocking everything:**

```python
def test_model_checking_workflow():
    """Test real component integration."""
    # Use real components where practical
    validator = FormulaValidator() 
    runner = TestModelRunner()  # Lightweight test version
    processor = ExampleProcessor(validator=validator, runner=runner)
    
    # Test realistic workflow
    result = processor.process(valid_example_data)
    assert result.is_successful()
```

## Performance Considerations

### Lazy Initialization

**Create expensive components only when needed:**

```python
class TheoryManager:
    def __init__(self):
        self._loaded_theories = {}  # Cache loaded theories
        self._theory_loader = None  # Create when needed
    
    @property
    def theory_loader(self):
        if self._theory_loader is None:
            self._theory_loader = TheoryLoader()
        return self._theory_loader
    
    def get_theory(self, name: str):
        if name not in self._loaded_theories:
            self._loaded_theories[name] = self.theory_loader.load(name)
        return self._loaded_theories[name]
```

### Resource Management

**Proper cleanup for expensive resources:**

```python
class Z3ModelRunner:
    def __init__(self):
        self.solver = None
        self.context = None
    
    def __enter__(self):
        self.context = z3.Context()
        self.solver = z3.Solver(ctx=self.context)
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.solver:
            self.solver.reset()
        # Z3 context cleanup happens automatically
```

## Common Anti-Patterns to Avoid

### Over-Abstraction
```python
# Avoid: Too many layers for simple operations
class AbstractFactoryForValidatorCreation:  # Overkill
    def create_abstract_validator_interface(self): ...

# Prefer: Direct, clear construction
validator = FormulaValidator()
```

### Premature Interface Definition
```python
# Avoid: Interfaces for everything without clear need
class IStringHolder(Protocol):  # Probably unnecessary
    def get_string(self) -> str: ...

# Prefer: Introduce interfaces when you have multiple implementations
```

### Configuration Obsession
```python
# Avoid: Making everything configurable without need
class OverConfiguredProcessor:
    def __init__(self, config_loader=None, validator_factory=None, 
                 result_transformer=None, error_handler=None, ...):  # Too much
    
# Prefer: Configure what actually varies
class SimpleProcessor:
    def __init__(self, validator=None):
        self.validator = validator or DefaultValidator()
```

## Success Patterns from ModelChecker

The codebase shows several successful architectural patterns:

### Utility Organization
The `utils/` package provides clean separation:
- `api.py` - Theory access functions
- `bitvector.py` - Bit vector operations  
- `context.py` - Z3 context management
- `formatting.py` - Output formatting

### Theory Package Structure
Consistent structure across theory packages:
```
theory_name/
├── __init__.py     # Clean public API
├── semantic.py     # Core semantics
├── operators.py    # Operator definitions
└── examples.py     # Example formulas
```

### Builder Component Architecture
The builder/ package demonstrates effective component coordination:
- Clear protocols for all major interfaces
- Composition-based component assembly
- Dependency injection for testability
- Hierarchical error handling

## Conclusion

Good architecture in the ModelChecker framework should:

1. **Build on proven patterns** from the builder/ package
2. **Evolve incrementally** based on real needs
3. **Prioritize clarity and testability** over theoretical purity
4. **Respect domain complexity** while maintaining clean boundaries
5. **Support gradual improvement** without requiring massive rewrites

These patterns provide guidance for creating maintainable, testable code without over-engineering simple solutions. Apply them **judiciously** as your components grow and their needs become clear.

---

[← Method Complexity](METHOD_COMPLEXITY.md) | [Back to Maintenance](README.md) | [Utility Organization →](UTILITY_ORGANIZATION.md)