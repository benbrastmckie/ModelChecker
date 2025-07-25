# Python Style Guide: ModelChecker Framework Standards

[← Back to Development Hub](README.md) | [Development Guide →](DEVELOPMENT.md) | [AI Assistant Guide →](../CLAUDE.md)

## Directory Structure
```
docs/
├── README.md                    # Development documentation hub
├── DEVELOPMENT.md               # Development workflow guide
├── STYLE_GUIDE.md               # This file - Python coding standards
├── ARCHITECTURE.md              # System architecture and design
├── TESTS.md                     # Testing methodology
└── INSTALLATION.md              # Environment setup guide
```

## Overview

The **Python Style Guide** establishes comprehensive coding standards, architectural principles, and debugging philosophy for the ModelChecker framework. These standards ensure **consistent code quality**, **maintainable architecture**, and **effective collaboration** across all framework components and semantic theory implementations.

The guide emphasizes **fail-fast philosophy**, **explicit data flow**, and **structural solutions** over defensive programming. It prioritizes **code quality over backward compatibility** and promotes **continuous improvement** through systematic refactoring and architectural evolution.

These standards support both **human developers** and **AI assistants** in maintaining the framework's theoretical rigor while ensuring practical usability and extensibility for computational logic research applications.

## Quick Start

```python
# Core naming conventions
class TheorySemantics:          # PascalCase for classes
    def generate_constraints(self): # snake_case for functions
        pass
        
# Module organization
import os                       # Standard libraries first
import sys
from z3 import *               # Third-party libraries

from model_checker import *     # Local imports last
from .semantic import *

# Documentation requirements
def check_validity(formula: str, settings: dict) -> bool:
    """Check formula validity with given settings.
    
    Args:
        formula: LaTeX-formatted logical formula
        settings: Configuration dictionary with theory-specific options
        
    Returns:
        True if formula is valid, False if countermodel exists
        
    Raises:
        FormulaParseError: If formula syntax is invalid
        TheoryError: If settings incompatible with theory
    """
    pass
```

## Files in This Directory

This style guide serves as the **authoritative reference** for Python coding standards throughout the ModelChecker framework, ensuring consistency across theory implementations, core components, and development tools.

## Subdirectories

Refer to the [Development Documentation Hub](README.md) for complete navigation across all development resources, testing procedures, and architectural documentation.

## Code Formatting Standards

### Naming Conventions

| Element | Convention | Example |
|---------|------------|----------|
| **Functions** | `snake_case` | `check_formula()`, `generate_constraints()` |
| **Classes** | `PascalCase` | `LogosSemantics`, `ModelIterator` |
| **Modules** | `lowercase` | `semantic.py`, `operators.py` |
| **Constants** | `UPPER_SNAKE` | `DEFAULT_SETTINGS`, `MAX_ITERATIONS` |
| **Variables** | `snake_case` | `world_count`, `formula_result` |

### Import Organization

```python
# 1. Standard library imports
import os
import sys
from typing import Dict, List, Optional

# 2. Third-party imports  
import z3
import ipywidgets
from IPython.display import display

# 3. Local framework imports
from model_checker import get_theory
from model_checker.builder import BuildExample

# 4. Relative imports (same package)
from .semantic import SemanticDefaults
from .operators import LogicalOperator
```

### Spacing and Structure

```python
# 4-space indentation (no tabs)
class ExampleSemantics(SemanticDefaults):
    DEFAULT_SETTINGS = {
        'N': 3,                    # Align values for readability
        'max_time': 1000,
        'contingent': False,
    }
    
    def generate_constraints(self):
        # Single blank line between methods
        constraints = []
        
        # Blank line before major sections
        for world in self.worlds:
            constraint = self.world_constraint(world)
            constraints.append(constraint)
            
        return z3.And(*constraints)
```

## Framework Architecture Standards

### Theory Implementation Structure

All theories in `theory_lib/` must follow this standardized structure:

```python
# theory_lib/my_theory/
├── __init__.py            # Theory interface and registration
├── semantic.py           # Core semantic implementation
├── operators.py          # Logical operator definitions
├── examples.py           # Test formulas and validation cases
├── iterate.py            # Model iteration support (if needed)
├── docs/                 # Theory-specific documentation
├── tests/                # Comprehensive test suite
└── notebooks/            # Interactive tutorials
```

### Component Separation Principles

```python
# Maintain clear separation between layers
class TheorySemantics:           # Semantic layer
    def generate_constraints(self): pass
    
class TheoryOperators:           # Syntactic layer  
    def parse_formula(self): pass
    
class TheoryBuilder:             # Coordination layer
    def build_model(self): pass
```

### Design Philosophy

#### Core Principles

1. **Fail Fast Philosophy**
   ```python
   # Correct: Let errors occur naturally
   def check_formula(formula, theory):
       return theory.validate(formula)  # Will raise appropriate exception
       
   # Incorrect: Hide errors with defaults
   def check_formula(formula, theory=None):
       if theory is None:
           theory = get_default_theory()  # Masks missing parameter
   ```

2. **Explicit Parameter Requirements**
   ```python
   # Correct: Explicit world references
   def evaluate_at_world(self, formula: str, world_id: int) -> bool:
       return self.world_evaluations[world_id][formula]
       
   # Incorrect: Implicit conversions
   def evaluate_at_world(self, formula: str, world) -> bool:
       world_id = self._convert_world(world)  # Hidden conversion
   ```

3. **Clear Data Flow**
   ```python
   # Correct: Explicit data passing
   def build_model(self, premises: List[str], conclusions: List[str], settings: Dict):
       constraints = self.generate_constraints(premises, conclusions, settings)
       return self.solve_constraints(constraints)
       
   # Incorrect: Hidden state dependencies
   def build_model(self):
       constraints = self.generate_constraints()  # Depends on hidden state
   ```

## Domain-Specific Guidelines

### Semantic Theory Development

#### World Reference Consistency
```python
# Correct: Explicit world IDs in bimodal logic
class BimodalSemantics:
    def evaluate_temporal(self, formula: str, world_id: int, time_point: int) -> bool:
        return self.temporal_evaluations[world_id][time_point][formula]
        
    def get_accessible_worlds(self, world_id: int) -> List[int]:
        return self.accessibility_relations[world_id]

# Incorrect: Implicit world conversions
def evaluate_temporal(self, formula: str, world) -> bool:
    world_id = self._world_to_id(world)  # Hidden conversion
```

#### Function Composition Over Decorators
```python
# Correct: Explicit utility function calls
def validate_formula(formula: str, theory: str) -> str:
    parsed = parse_formula(formula)
    validated = validate_syntax(parsed, theory)
    return validated
    
# Incorrect: Decorator-based approach
@validate_syntax
@parse_formula  
def process_formula(formula: str) -> str:
    pass  # Execution flow obscured by decorators
```

### Change Management Philosophy

#### Code Quality Over Compatibility

**Breaking Changes Are Encouraged** when they improve:
- **Code clarity and maintainability**
- **Architectural consistency** 
- **Performance and reliability**
- **Developer experience**

```python
# Example: Refactoring for better architecture
# Old API (deprecated)
model.check_formula("p → q", use_bimodal=True, temporal_depth=3)

# New API (improved)
theory = get_theory("bimodal", settings={'M': 3})
model = BuildExample("example", theory)
result = model.check_formula("p → q")
```

#### Systematic Refactoring Approach

1. **Comprehensive Analysis**: Understand full impact across codebase
2. **Unified Solutions**: Address entire system rather than localized fixes
3. **Pattern Consistency**: Update all affected components to follow new patterns
4. **Documentation Updates**: Revise all relevant documentation
5. **Test Coverage**: Ensure comprehensive test coverage for new patterns

## Documentation Standards

### For New Contributors
- **[Development Guide](DEVELOPMENT.md)** - Complete development workflow and environment setup
- **[AI Assistant Guide](../CLAUDE.md)** - Quality standards and mathematical notation guidelines
- **[Installation Guide](INSTALLATION.md)** - Platform-specific setup procedures

### For Theory Developers  
- **[Architecture Guide](ARCHITECTURE.md)** - System design principles and component relationships
- **[Theory Library Guide](../src/model_checker/theory_lib/README.md)** - Theory implementation patterns
- **[Testing Guide](TESTS.md)** - Comprehensive testing methodology

### For Core Developers
- **[Code Quality Standards](#code-formatting-standards)** - Formatting, naming, and structure requirements
- **[Design Philosophy](#framework-architecture-standards)** - Architectural principles and patterns
- **[Debugging Guidelines](#debugging-philosophy)** - Problem-solving approach and quality standards

## Debugging Philosophy

### Problem-Solving Methodology

#### Root Cause Analysis Approach
```python
# Example: Tracing Z3 timeout errors
# 1. Identify symptom
# Z3Exception: timeout

# 2. Trace to source  
# - Complex constraint generation?
# - Inefficient model space?
# - Theory-specific performance issue?

# 3. Address root cause
class OptimizedSemantics(SemanticDefaults):
    def generate_constraints(self):
        # Simplified constraint generation
        return self.optimized_constraint_builder()
        
# Don't just increase timeout (symptom treatment)
# settings = {'max_time': 60000}  # Incorrect approach
```

#### Structural Solutions Over Workarounds
```python
# Correct: Architectural improvement
class ImprovedIterator(BaseIterator):
    def _create_difference_constraint(self, models):
        # Redesigned constraint generation
        return efficient_constraint_algorithm(models)
        
# Incorrect: Conditional workaround
def _create_difference_constraint(self, models):
    if len(models) > 5:  # Workaround for performance
        return simplified_constraint(models)
    else:
        return full_constraint(models)
```

### Testing and Documentation Standards

#### Test-Driven Bug Resolution
```python
# 1. Create regression test first
def test_bimodal_world_reference_consistency():
    theory = get_theory("bimodal")
    model = BuildExample("test", theory)
    
    # Reproduce the bug
    with pytest.raises(WorldReferenceError):
        model.check_formula("\\Box \\future p")
        
# 2. Fix the underlying issue
# 3. Verify test passes
```

#### Error Messages as Documentation
```python
# Correct: Informative error messages
if world_id not in self.world_space:
    raise WorldReferenceError(
        f"World ID {world_id} not found in model space. "
        f"Available worlds: {list(self.world_space.keys())}. "
        f"Check world generation in {self.__class__.__name__}"
    )
    
# Incorrect: Generic error messages
if world_id not in self.world_space:
    raise ValueError("Invalid world")  # Unhelpful
```

### Code Quality Standards

#### Simplification Over Validation
```python
# Correct: Simple, clear interface
def check_formula(formula: str, theory_name: str) -> bool:
    theory = get_theory(theory_name)
    return theory.validate(formula)
    
# Incorrect: Excessive defensive programming
def check_formula(formula, theory_name=None):
    if not formula:
        return False
    if theory_name is None:
        theory_name = "default"
    if not isinstance(formula, str):
        formula = str(formula)
    # ... more defensive checks obscure core logic
```

#### Pattern-Based Error Elimination
```python
# Identify error patterns and eliminate through structure
# Common pattern: Inconsistent settings validation

# Solution: Centralized settings management
class SettingsManager:
    def validate_theory_settings(self, settings: dict, theory_name: str) -> dict:
        theory_defaults = self.get_theory_defaults(theory_name)
        return self.merge_and_validate(settings, theory_defaults)
```

## References

### Implementation Documentation
- Style standards follow fail-fast philosophy with explicit parameter requirements
- Architectural patterns documented with practical examples and anti-patterns

### Related Resources
- **[Development Documentation Hub](README.md)** - Complete development resource navigation
- **[Framework Architecture](ARCHITECTURE.md)** - System design and component relationships  
- **[Maintenance Standards](../MAINTENANCE.md)** - Documentation structure and quality guidelines

## License

Part of the ModelChecker framework, licensed under GPL-3.0.

---

[← Back to Development Hub](README.md) | [Development Guide →](DEVELOPMENT.md) | [AI Assistant Guide →](../CLAUDE.md)