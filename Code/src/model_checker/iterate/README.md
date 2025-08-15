# Model Iteration Framework: Systematic Discovery of Distinct Models

[← Back to Model Checker](../README.md) | [API Reference →](../models/README.md) | [Theory Implementations →](../theory_lib/README.md)

## Directory Structure

```
iterate/
├── README.md                    # This file - framework overview and guide
├── __init__.py                  # Package exports
├── base.py                      # Abstract base class (no decorators)
├── core.py                      # BaseModelIterator orchestration (369 lines)
├── iterator.py                  # Main iteration loop and control (287 lines)
├── constraints.py               # Constraint generation and management (279 lines)
├── models.py                    # Model building, validation, and differences (611 lines)
├── graph.py                     # Graph representation and isomorphism detection (540 lines)
├── metrics.py                   # Progress, statistics, termination, and formatting (321 lines)
├── build_example.py             # BuildExample extension for iteration (153 lines)
└── tests/                       # Comprehensive test suite
    ├── test_base_iterator.py    # Base class and abstract methods
    ├── test_models.py           # Model building and differences
    ├── test_constraints.py      # Constraint generation
    ├── test_isomorphism.py      # Isomorphism detection
    ├── test_graph_utils.py      # Graph representation
    ├── test_iteration_control.py # Progress and termination (tests metrics.py)
    ├── test_validation.py       # Model validation (tests ModelValidator in models.py)
    └── [other test files]       # Additional test coverage
```

## Overview

The **Model Iteration Framework** provides systematic exploration of semantic model spaces for logical theories. It discovers multiple distinct models that satisfy given premises while falsifying conclusions, enabling comprehensive analysis of countermodel diversity and semantic variation.

### Core Capabilities

1. **Automated Model Discovery**: Systematically finds multiple distinct models
2. **Semantic Difference Detection**: Identifies meaningful differences between models
3. **Isomorphism Prevention**: Avoids structurally identical duplicates (requires NetworkX)
4. **Progress Tracking**: Real-time feedback with timing and statistics
5. **Theory Independence**: Abstract framework adaptable to any semantic theory
6. **Comprehensive Logging**: Detailed logging for monitoring and debugging

### Integration Context

The iteration framework integrates with:
- **Theory Library**: Each theory implements specific iteration behavior
- **Builder Module**: Constructs models based on iteration constraints
- **Settings System**: Configures iteration parameters and timeouts
- **CLI Tools**: Provides user interface for iteration requests

## Architecture

### Design Philosophy

The iteration framework follows a **hybrid architecture** balancing modularity with technical requirements. After extensive refactoring (documented in `docs/specs/plans/`), we discovered that the core iteration logic requires tight coupling between components for proper constraint propagation and model building synchronization.

### Core Components

#### BaseModelIterator (`base.py` + `core.py`)

The framework uses a two-file approach:

1. **Abstract Definition** (`base.py`):
```python
class BaseModelIterator:
    """Abstract base class defining the iteration interface."""
    
    def _create_difference_constraint(self, previous_models):
        """Theory-specific: ensure new model differs from previous ones."""
        raise NotImplementedError("Subclasses must implement _create_difference_constraint")
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Theory-specific: prevent structurally identical models."""
        raise NotImplementedError("Subclasses must implement _create_non_isomorphic_constraint")
```

2. **Concrete Implementation** (`core.py`):
```python
from model_checker.iterate.base import BaseModelIterator
from model_checker.iterate.models import evaluate_z3_boolean, DifferenceCalculator

class BaseModelIterator(BaseModelIterator):
    """Orchestrates iteration using modular components."""
    
    def __init__(self, build_example):
        self.iterator_core = IteratorCore(build_example)
        self.constraint_generator = ConstraintGenerator(build_example)
        self.model_builder = ModelBuilder(build_example)
        self.isomorphism_checker = IsomorphismChecker()
        # ... other component initialization
```

### Module Organization

#### Core Modules

1. **iterator.py** - Main iteration loop and control flow
   - Manages iteration state and progress
   - Coordinates between components
   - Handles debug message collection

2. **constraints.py** - Constraint generation and management
   - Creates difference constraints
   - Manages Z3 solver state
   - Preserves original constraints

3. **models.py** - Model operations (consolidated module)
   - `ModelBuilder`: Creates new model structures
   - `DifferenceCalculator`: Calculates semantic differences
   - Validation functions: `evaluate_z3_boolean()`, `is_valid_model()`, etc.

4. **graph.py** - Graph operations (consolidated module)
   - `ModelGraph`: Represents models as graphs
   - `IsomorphismChecker`: Detects structural equivalence
   - NetworkX integration with graceful fallback

5. **metrics.py** - Monitoring and reporting (consolidated module)
   - `IterationProgress`: Real-time progress bars
   - `IterationStatistics`: Performance metrics
   - `TerminationManager`: Stopping conditions
   - `ResultFormatter`: Output formatting

6. **build_example.py** - BuildExample adaptation
   - `IteratorBuildExample`: Extends BuildExample for iteration
   - Handles Z3 model injection
   - Theory-agnostic interface

## Usage

### Basic Model Iteration

```python
from model_checker.builder import BuildExample
from model_checker.iterate import BaseModelIterator

# Create initial model
example = BuildExample(
    semantics_module_name="model_checker.semantics",
    syntax_module_name="model_checker.syntax",
    settings={'max_iterations': 5}
)

# Find countermodel
premises = ["p \\rightarrow q", "q \\rightarrow r"]
conclusions = ["p \\rightarrow r"]
example.interpret_formulas(premises, conclusions)
assert example.check_validity() == "Invalid"

# Iterate to find more models
iterator = BaseModelIterator(example)
models = iterator.iterate()
print(f"Found {len(models)} distinct models")
```

### Theory-Specific Iteration

Each theory extends BaseModelIterator with specialized behavior:

```python
# Logos theory example
from model_checker.theory_lib.logos import LogosIterator

example = BuildExample(
    semantics_module_name="model_checker.theory_lib.logos.semantics",
    syntax_module_name="model_checker.theory_lib.logos.syntax"
)

iterator = LogosIterator(example)
models = iterator.iterate()
```

### Configuration Options

```python
settings = {
    'max_iterations': 10,           # Maximum models to find
    'timeout': 300,                 # Iteration timeout in seconds
    'max_invalid_attempts': 20,     # Stop after N consecutive failures
    'non_empty': True,              # Require non-empty models
    'contingent': False,            # Allow necessary/impossible models
    'use_isomorphism': True,        # Enable isomorphism detection
    'debug': False                  # Enable debug output
}
```

## Logging and Monitoring

The iteration framework provides comprehensive logging to help monitor progress and debug issues. All iteration-related log messages are prefixed with `[ITERATION]` for easy filtering.

### Log Levels

The framework uses Python's standard logging system with the following levels:

- **ERROR** (default): Only critical errors that stop iteration
- **WARNING**: Issues that don't stop iteration but may affect results
- **INFO**: Progress updates and major events during iteration
- **DEBUG**: Detailed information for troubleshooting

### Enabling Verbose Logging

To see iteration progress and events, enable INFO level logging:

```python
import logging

# Enable iteration logging
logger = logging.getLogger('model_checker.iterate')
logger.setLevel(logging.INFO)

# For detailed debugging
logger.setLevel(logging.DEBUG)
```

### Log Output Examples

```
[ITERATION] Starting iteration to find 5 models
[ITERATION] Searching for model 2/5...
[ITERATION] Found distinct model #2
[ITERATION] Model differs in: world_changes={'added': [2], 'removed': []}
[ITERATION] Successfully found all 5 requested models
```

### Performance Monitoring

The framework tracks detailed statistics during iteration:

```python
# Get iteration summary
summary = iterator.get_iteration_summary()
print(f"Models found: {summary['models_found']}")
print(f"Total checked: {summary['total_checked']}")
print(f"Success rate: {summary['success_rate']:.1%}")
print(f"Average time per model: {summary['avg_time_per_model']:.3f}s")
```

## Extension Guide

### Creating Theory-Specific Iterators

To implement iteration for a new theory:

1. **Extend BaseModelIterator**:
```python
from model_checker.iterate import BaseModelIterator

class MyTheoryIterator(BaseModelIterator):
    def _create_difference_constraint(self, previous_models):
        """Create constraints ensuring semantic difference."""
        # Theory-specific logic
        return constraint
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Prevent structurally identical models."""
        # Theory-specific logic
        return constraint
    
    def iterate_generator(self):
        """Optional: Override to add theory-specific differences."""
        for model in super().iterate_generator():
            # Calculate theory-specific differences if we have a previous model
            if len(self.model_structures) >= 2:
                theory_diffs = self._calculate_theory_differences(
                    model, self.model_structures[-2]
                )
                # Merge theory-specific differences with existing generic ones
                if hasattr(model, 'model_differences') and model.model_differences:
                    model.model_differences.update(theory_diffs)
                else:
                    model.model_differences = theory_diffs
            
            yield model
```

2. **Register in Theory's __init__.py**:
```python
from .iterate import MyTheoryIterator

__all__ = ['MyTheoryIterator']
```

3. **Add Tests**:
```python
def test_my_theory_iteration():
    example = BuildExample(...)
    iterator = MyTheoryIterator(example)
    models = iterator.iterate()
    assert len(models) >= 2
```

### Theory-Specific Difference Display

Theories can provide rich semantic difference information by:

1. **Implementing Custom Difference Calculation**:
   - Override `_calculate_differences()` or add theory-specific methods
   - Return structured data describing semantic changes

2. **Overriding iterate_generator()**:
   - Merge theory-specific differences with generic differences
   - Transform data structures to match display expectations

3. **Utilizing print_model_differences()**:
   - Theory's ModelStructure can implement custom display logic
   - Framework automatically calls this method when differences exist

Current theories with enhanced difference display:
- **Logos**: Verification/falsification changes, parthood relations
- **Exclusion**: Verification changes, witness changes, exclusion relations
- **Imposition**: State impositions, proposition changes

### NetworkX Integration

The framework uses NetworkX for isomorphism detection but degrades gracefully if unavailable:

```python
try:
    import networkx as nx
    HAS_NETWORKX = True
except ImportError:
    HAS_NETWORKX = False
    logger.warning(
        "NetworkX not installed. Isomorphism detection disabled. "
        "Install with: pip install networkx"
    )
```

## Testing

The iterate package includes comprehensive tests covering all modules:

```bash
# Run all iterate tests
pytest src/model_checker/iterate/tests/ -v

# Run specific module tests
pytest src/model_checker/iterate/tests/test_models.py -v
pytest src/model_checker/iterate/tests/test_constraints.py -v

# Run with coverage
pytest src/model_checker/iterate/tests/ --cov=src/model_checker/iterate
```

### Test Organization

- **Unit Tests**: Each module has corresponding test file
- **Integration Tests**: End-to-end iteration workflows
- **Theory Tests**: Each theory includes iteration tests
- **Edge Cases**: Timeout, failure, and resource tests

## Performance Considerations

### Constraint Generation

The framework generates increasingly complex constraints as iteration progresses:
- Each new model adds exclusion constraints
- Isomorphism checks add structural constraints
- Theory-specific constraints may grow exponentially

### Optimization Strategies

1. **Early Termination**: Stop when no progress is made
2. **Constraint Simplification**: Combine similar constraints
3. **Parallel Checking**: Use multiprocessing for independent checks
4. **Caching**: Reuse isomorphism results

### Resource Limits

```python
# Set resource limits
settings = {
    'max_time': 60,                 # Timeout for all operations
    'max_solver_memory': 4096,      # MB limit for Z3
    'max_graph_size': 1000          # Node limit for isomorphism
}
```

## Troubleshooting

### Common Issues

1. **No Additional Models Found**
   - Check if the theory space is exhausted
   - Verify constraint generation logic
   - Enable debug logging for details

2. **Timeout During Iteration**
   - Reduce max_iterations
   - Increase timeout values
   - Check for constraint complexity

3. **Memory Usage**
   - Monitor Z3 solver memory
   - Limit graph sizes for isomorphism
   - Use resource limits

### Debug Mode

Enable comprehensive debugging:

```python
import logging
logging.basicConfig(level=logging.DEBUG)

# Debug specific iteration
iterator.settings['debug'] = True
models = iterator.iterate()

# Check debug messages
for msg in iterator.get_debug_messages():
    print(f"DEBUG: {msg}")
```

## References

### Academic Background

- Model enumeration algorithms: [Citation needed]
- Graph isomorphism detection: Nauty algorithm
- Constraint satisfaction: Z3 theorem prover

### Related Documentation

- [Model Builder](../builder/README.md) - Model construction framework
- [Theory Library](../theory_lib/README.md) - Theory implementations
- [Settings System](../settings/README.md) - Configuration management

### Implementation Notes

- Phase 6 modularization attempt documented in `docs/specs/plans/`
- Constraint timing issues prevent full modularization
- Future improvements tracked in GitHub issues

---

[← Back to Model Checker](../README.md) | [API Reference →](../models/README.md) | [Theory Implementations →](../theory_lib/README.md)
