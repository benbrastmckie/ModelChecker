# Architecture Guide

## Overview

This document provides **comprehensive architectural guidance** for the ModelChecker framework, consolidating patterns, design principles, utility organization, and documentation standards. It serves as the definitive reference for maintaining clean, testable, and maintainable architecture across all components.

**Philosophy:** Good architecture should **emerge from practical needs**, not imposed abstractions. These patterns provide flexible guidance for building clean, maintainable code without over-engineering simple solutions.

## Table of Contents

1. [Core Architectural Principles](#core-architectural-principles)
2. [Component Architecture](#component-architecture)
3. [Package Boundaries & Interfaces](#package-boundaries--interfaces)
4. [Utility Organization Architecture](#utility-organization-architecture)
5. [Theory Implementation Architecture](#theory-implementation-architecture)
6. [Dependency Management](#dependency-management)
7. [ASCII Diagram Standards](#ascii-diagram-standards)
8. [Testing Architecture](#testing-architecture)
9. [Performance Architecture](#performance-architecture)
10. [Success Metrics](#success-metrics)
11. [Practical Examples](#practical-examples)

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

## Component Architecture

### Established Patterns in ModelChecker

#### Protocol-Based Component Interfaces

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

#### Component Factory Pattern

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

#### Error Handling Architecture

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

## Package Boundaries & Interfaces

### Package Structure Guidelines

**Follow the established successful patterns:**

```
package_name/
├── __init__.py          # Clean public API exports
├── protocols.py         # Package interface definitions
├── core_module.py       # Main functionality
├── utilities.py         # Package-specific utilities
├── errors.py            # Package-specific error hierarchy
└── tests/               # Package test suite
```

### Inter-Package Communication

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

### Configuration Management Architecture

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

## Utility Organization Architecture

### Shared vs Package-Specific Decision Matrix

**Use shared utilities (`src/model_checker/utils/`) when:**
- Function is used by multiple packages
- Utility provides core framework functionality (Z3 operations, parsing, etc.)
- Function is general-purpose within the domain (bitvector operations, context management)
- Utility could benefit other future packages

**Use package-specific utilities (`package/package_utils.py`) when:**
- Function is specific to one package's internal operations
- Utility contains domain logic specific to that package
- Function was extracted during package refactoring
- Utility requires package-specific imports or knowledge

### Utility Architecture Patterns

#### Shared Utilities Structure

```
utils/
├── __init__.py          # Clean exports organized by category
├── api.py               # Theory and example access functions
├── bitvector.py         # Bit vector operations for Z3
├── context.py           # Z3 context management utilities
├── formatting.py        # Output formatting helpers
├── parsing.py           # Expression parsing utilities  
├── testing.py           # Test execution and validation
├── version.py           # Version management utilities
└── z3_helpers.py        # Z3 wrapper and helper functions
```

#### Clean Export Patterns

```python
# utils/__init__.py - Organized exports
"""ModelChecker utilities package."""

# Theory and configuration utilities
from .api import get_theory, list_theories, load_example_data
from .settings import load_theory_config, validate_settings

# Z3 and solver utilities  
from .z3_helpers import create_solver_context, format_z3_model
from .bitvector import create_bitvector, extract_bitvector_values
from .context import Z3ContextManager

# Output and formatting utilities
from .formatting import format_model_output, format_error_message
from .parsing import parse_formula, validate_syntax

# Test utilities
from .testing import run_theory_tests, validate_example_set

__all__ = [
    # Theory utilities
    'get_theory', 'list_theories', 'load_example_data',
    'load_theory_config', 'validate_settings',
    
    # Z3 utilities
    'create_solver_context', 'format_z3_model', 
    'create_bitvector', 'extract_bitvector_values',
    'Z3ContextManager',
    
    # Output utilities
    'format_model_output', 'format_error_message',
    'parse_formula', 'validate_syntax',
    
    # Test utilities  
    'run_theory_tests', 'validate_example_set'
]
```

## Theory Implementation Architecture

### Theory Package Structure

**Consistent structure across theory packages:**

```
theory_name/
├── __init__.py          # Clean public API
├── semantic.py          # Core semantics
├── operators.py         # Operator definitions
└── examples.py          # Example formulas
```

### Theory Loading Architecture

```python
class TheoryLoader:
    """Centralized theory loading with validation and caching."""
    
    def __init__(self):
        self._loaded_theories = {}  # Cache loaded theories
        self._theory_validators = {}  # Theory-specific validators
    
    def load_theory(self, theory_name: str, validate: bool = True) -> Dict:
        """Load theory with optional validation."""
        if theory_name not in self._loaded_theories:
            theory_data = self._load_theory_data(theory_name)
            
            if validate:
                self._validate_theory(theory_name, theory_data)
            
            self._loaded_theories[theory_name] = theory_data
        
        return self._loaded_theories[theory_name]
    
    def get_available_theories(self) -> List[str]:
        """Discover all available theories."""
        # Implementation for theory discovery
        pass
```

## Dependency Management

### Lazy Initialization Patterns

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

### Resource Management Architecture

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

## ASCII Diagram Standards

### Preferred ASCII Diagram Styles

The ModelChecker framework uses three standardized ASCII diagram styles for consistent, professional documentation.

#### Style 1: Numbered Pipeline Flow

Uses numbered sections to separate stages with clear box boundaries, bullet points, and flow arrows:

```
1. INITIALIZATION
┌────────────────────┐    ┌────────────────────┐
│ Component A        │    │ Component B        │
│ • Detail 1         │───▶│ • Detail 1         │
│ • Detail 2         │    │ • Detail 2         │
└────────────────────┘    └────────────────────┘
         │                           │
         └───────────┬───────────────┘
                     ▼
2. NEXT STAGE
┌─────────────────────────────────────┐
│ Combined Processing                 │
│ • Merged inputs                     │
│ • Unified processing logic          │
│ • Single output stream              │
└─────────────────────────────────────┘
```

**Use for:** Sequential processes, pipelines, multi-stage workflows

#### Style 2: Component Connections

Shows hierarchical component relationships with nested boxes and clear data flow:

```
┌─────────────────────────────────────────────────────────────────┐
│                          Component Name                         │
│                     (Description/Purpose)                       │
│                                                                 │
│  ┌──────────────┐  ┌───────────────┐  ┌───────────────────────┐ │
│  │ Subcomponent │  │ Subcomponent  │  │ Subcomponent        │ │
│  │ • Function   │  │ • Function    │  │ • Function          │ │
│  │ • Details    │  │ • Details     │  │ • Details           │ │
│  └──────────────┘  └───────────────┘  └───────────────────────┘ │
└──────────────────────────┬──────────────────────────────────────┘
                           │
                           ▼
                   Output Processing
```

**Use for:** Component architecture, system hierarchies, module relationships

#### Style 3: Settings/Priority Flow

Shows hierarchy with priorities, multiple inputs, and distributed outputs:

```
High Priority Input ─┐
                     │  ┌─────────────────┐
Medium Priority ─────┼─▶│ Priority        │─┬─▶ Output A
                     │  │ Processor       │ │
Low Priority ────────┘  │ • Merges inputs │ ├─▶ Output B
                        │ • Applies rules │ │
Default Config ────────▶│ • Distributes   │ └─▶ Output C
                        └─────────────────┘
```

**Use for:** Configuration hierarchies, priority systems, data distribution

### ASCII Diagram Guidelines

#### Box Drawing Characters

**Standard Characters:**
- Horizontal lines: `─` (U+2500)
- Vertical lines: `│` (U+2502)  
- Top-left corner: `┌` (U+250C)
- Top-right corner: `┐` (U+2510)
- Bottom-left corner: `└` (U+2514)
- Bottom-right corner: `┘` (U+2518)
- Cross intersection: `┼` (U+253C)
- T-junctions: `┬` `┴` `├` `┤`

**Arrows:**
- Horizontal: `───▶` or `◀───`
- Vertical: `▼` or `▲`
- Simple: `->` `<-` (when Unicode not available)

#### Quality Standards

1. **Consistent Alignment:** All boxes and elements should align properly
2. **Clear Spacing:** Adequate whitespace between elements
3. **Professional Appearance:** Clean, readable diagrams that enhance understanding
4. **Information Preservation:** All diagram content must be equivalent to original
5. **Readable Text:** Bullet points and labels should be clearly formatted

#### Example Template

```
┌─────────────────────────────────────────────────────────────────┐
│                        [Diagram Title]                          │
│                      [Purpose/Context]                          │
│                                                                 │
│  ┌──────────────┐  [connection]  ┌──────────────────────────┐   │
│  │ Component A  │                │ Component B              │   │
│  │ • Function 1 │ ──────────────▶│ • Processes input        │   │
│  │ • Function 2 │                │ • Generates output       │   │
│  │ • Properties │                │ • Handles errors         │   │
│  └──────────────┘                └──────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
                        [Next Stage or Output]
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

### Testing Utility Architecture

```python
# Test utilities separately for clarity
def test_format_model_output_basic():
    """Test basic model output formatting."""
    model = create_test_model(status="satisfiable", variables={"A": True})
    result = format_model_output(model)
    
    assert "satisfiable" in result
    assert "A=True" in result

def test_utility_documentation_examples():
    """Ensure that utility documentation examples work correctly."""
    # Test the examples from docstrings to keep them accurate
    model = get_example_model()  # From docstring example
    formatted = format_model_output(model)
    
    # Verify the example output structure
    assert "Model:" in formatted
    assert "Variables:" in formatted
```

## Performance Architecture

### Resource Management Patterns

**Efficient resource usage for expensive operations:**

```python
class ResourceManager:
    """Manages expensive resources with proper lifecycle."""
    
    def __init__(self):
        self._resource_pool = {}
        self._active_resources = set()
    
    def acquire_resource(self, resource_type: str, config: Dict = None):
        """Acquire resource with automatic cleanup."""
        resource_id = self._generate_resource_id(resource_type, config)
        
        if resource_id not in self._resource_pool:
            self._resource_pool[resource_id] = self._create_resource(
                resource_type, config
            )
        
        self._active_resources.add(resource_id)
        return self._resource_pool[resource_id]
    
    def release_resource(self, resource_id: str):
        """Release resource when no longer needed."""
        if resource_id in self._active_resources:
            self._active_resources.remove(resource_id)
        
        # Clean up unused resources
        self._cleanup_unused_resources()
```

### Caching Architecture

**Smart caching for expensive computations:**

```python
class TheoryCache:
    """Cache theory computations with intelligent invalidation."""
    
    def __init__(self, max_size: int = 100):
        self._cache = {}
        self._access_times = {}
        self._max_size = max_size
    
    def get_or_compute(self, key: str, compute_func: Callable, 
                      cache_policy: str = "default"):
        """Get cached result or compute if not available."""
        if key in self._cache:
            self._access_times[key] = time.time()
            return self._cache[key]
        
        # Compute new result
        result = compute_func()
        
        # Cache with size management
        if len(self._cache) >= self._max_size:
            self._evict_oldest()
        
        self._cache[key] = result
        self._access_times[key] = time.time()
        return result
```

## Success Metrics

### Architectural Quality Indicators

**Measure architectural health with these metrics:**

#### 1. Component Cohesion
- **Target:** Each component should have a single, clear responsibility
- **Metric:** Functions within a component should be highly related
- **Red flag:** Components with multiple unrelated responsibilities

#### 2. Coupling Measures
- **Target:** Low coupling between packages, high cohesion within packages
- **Metric:** Number of cross-package dependencies
- **Good practice:** Dependencies flow in one direction (no circular dependencies)

#### 3. Interface Clarity
- **Target:** Clear, stable public APIs with minimal surface area
- **Metric:** Ratio of public to private methods/functions
- **Success indicator:** Protocols have clear, minimal interfaces

#### 4. Testability Score
- **Target:** All components easily testable in isolation
- **Metric:** Percentage of components that can be unit tested without mocks
- **Best practice:** Components with injectable dependencies

#### 5. Documentation Coverage
- **Target:** All architectural decisions documented with rationale
- **Metric:** ASCII diagrams present for all major system interactions
- **Quality indicator:** Diagrams match actual implementation

### Practical Success Examples

**The ModelChecker framework demonstrates successful patterns:**

#### 1. Utility Organization Success
- **utils/ package:** Clean separation by domain (Z3, parsing, formatting)
- **Package-specific utilities:** builder/runner_utils.py extracted during refactoring
- **Clear imports:** No circular dependencies, clean export patterns

#### 2. Protocol Architecture Success
- **builder/protocols.py:** Clear interfaces for all major components
- **Testing benefits:** Easy to create test doubles and mock dependencies
- **Flexibility:** Multiple implementations possible without changing clients

#### 3. Error Handling Success
- **Hierarchical errors:** BuilderError hierarchy provides clear error categories
- **Contextual information:** Errors include helpful context and suggestions
- **Consistent patterns:** Similar error patterns across packages

## Practical Examples

### Building New Components

**Follow the established architectural patterns:**

```python
# 1. Define protocol first
class INewComponent(Protocol):
    """Clear interface for new component functionality."""
    
    def process_data(self, data: Any) -> ProcessingResult: ...
    def validate_input(self, data: Any) -> bool: ...
    def get_processing_stats(self) -> Dict[str, Any]: ...

# 2. Implement with dependency injection
class NewComponent:
    def __init__(self, 
                 validator: IValidator = None,
                 formatter: IFormatter = None,
                 cache: ICache = None):
        self.validator = validator or DefaultValidator()
        self.formatter = formatter or DefaultFormatter()
        self.cache = cache or InMemoryCache()
    
    def process_data(self, data: Any) -> ProcessingResult:
        # Validate input
        if not self.validator.validate(data):
            raise ValidationError(self.validator.get_errors())
        
        # Check cache
        cache_key = self._generate_cache_key(data)
        if cached_result := self.cache.get(cache_key):
            return cached_result
        
        # Process data
        result = self._do_processing(data)
        
        # Cache and return
        self.cache.set(cache_key, result)
        return result

# 3. Extract utilities as needed
def extract_processing_metadata(result: ProcessingResult) -> Dict:
    """Extract metadata from processing result for reuse."""
    return {
        'processing_time': result.elapsed_time,
        'data_size': result.input_size,
        'success': result.is_successful(),
        'error_count': len(result.errors)
    }
```

### Refactoring Existing Code

**Apply architectural patterns incrementally:**

```python
# Before: Monolithic component
class LegacyProcessor:
    def complex_processing_method(self, data):
        # 100+ lines of mixed concerns
        # Validation logic
        # Processing logic  
        # Formatting logic
        # Error handling
        pass

# After: Refactored with clear separation
class RefactoredProcessor:
    def __init__(self, validator=None, formatter=None, error_handler=None):
        self.validator = validator or DefaultValidator()
        self.formatter = formatter or DefaultFormatter()
        self.error_handler = error_handler or DefaultErrorHandler()
    
    def process(self, data):
        try:
            # Clear separation of concerns
            validated_data = self._validate_data(data)
            processed_data = self._process_data(validated_data)
            return self._format_result(processed_data)
        except ProcessingError as e:
            return self.error_handler.handle_error(e)
    
    def _validate_data(self, data):
        return self.validator.validate_and_transform(data)
    
    def _process_data(self, data):
        # Core processing logic only
        return process_core_logic(data)
    
    def _format_result(self, data):
        return self.formatter.format_result(data)
```

### Integration Architecture

**For complex integrations, use facade patterns:**

```python
class ModelCheckerFacade:
    """Simplified interface for common model checking workflows."""
    
    def __init__(self):
        # Coordinate multiple components
        self.theory_manager = TheoryManager()
        self.validator = FormulaValidator()
        self.runner = ModelRunner()
        self.output_manager = OutputManager()
    
    def check_formula(self, formula: str, theory_name: str, 
                     output_format: str = "default") -> ModelResult:
        """Complete model checking workflow."""
        
        # Load theory
        theory = self.theory_manager.load_theory(theory_name)
        
        # Validate formula
        if not self.validator.validate(formula):
            raise ValidationError(self.validator.get_errors())
        
        # Run model checking
        result = self.runner.run_model_check(formula, theory)
        
        # Format output
        formatted_result = self.output_manager.format_result(
            result, output_format
        )
        
        return formatted_result
    
    def list_available_theories(self) -> List[str]:
        """Convenience method for theory discovery."""
        return self.theory_manager.get_available_theories()
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

### Circular Dependencies
```python
# Avoid: Utilities that import from packages that use them
# utils/helper.py
from model_checker.builder import SomeClass  # Creates circular dependency

# Prefer: Keep utilities independent or use dependency injection
def process_with_handler(data, handler=None):
    """Process data with optional handler injection."""
    handler = handler or default_handler
    return handler.process(data)
```

## Conclusion

Effective architecture in the ModelChecker framework should:

1. **Build on proven patterns** from the builder/ package and utils/ organization
2. **Evolve incrementally** based on real needs, not theoretical requirements
3. **Prioritize clarity and testability** over abstract purity
4. **Respect domain complexity** while maintaining clean boundaries
5. **Support gradual improvement** without requiring massive rewrites
6. **Use consistent ASCII diagrams** for clear visual communication
7. **Maintain clear package boundaries** with explicit interfaces
8. **Follow established utility organization** patterns for code reuse

These architectural guidelines provide **practical, flexible standards** that support maintainable, testable code without over-engineering simple solutions. Apply them **judiciously and incrementally** as components grow and their architectural needs become clear.

The goal is architecture that **serves the code and the developers**, not architecture that the code must serve. Good architecture makes development easier, testing simpler, and maintenance more predictable.