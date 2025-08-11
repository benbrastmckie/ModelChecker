# Model Iteration Framework: Systematic Discovery of Distinct Models

[← Back to Model Checker](../README.md) | [API Reference →](../models/README.md) | [Theory Implementations →](../theory_lib/README.md)

## Directory Structure

```
iterate/
├── README.md                    # This file - framework overview and guide
├── core.py                      # BaseModelIterator abstract class
├── progress.py                  # Progress bar and timing utilities
├── stats.py                     # Model statistics and analysis
├── parallel.py                  # Parallel constraint generation
├── graph_utils.py               # Graph-based isomorphism detection
└── tests/                       # Comprehensive test suite
    ├── test_base_iterator.py    # Abstract method testing
    ├── test_constraint_preservation.py  # Constraint isolation tests
    ├── test_core.py             # Core functionality tests
    ├── test_edge_cases.py       # Boundary condition tests
    └── test_graph_utils.py      # Isomorphism detection tests
```

## Overview

The **Model Iteration Framework** provides systematic exploration of semantic model spaces for logical theories. It discovers multiple distinct models that satisfy given premises while falsifying conclusions, enabling comprehensive analysis of countermodel diversity and semantic variation.

### Core Capabilities

1. **Automated Model Discovery**: Systematically finds multiple distinct models
2. **Semantic Difference Detection**: Identifies meaningful differences between models
3. **Isomorphism Prevention**: Avoids structurally identical duplicates
4. **Progress Tracking**: Real-time feedback with timing and statistics
5. **Theory Independence**: Abstract framework adaptable to any semantic theory

### Integration Context

The iteration framework integrates with:
- **Theory Library**: Each theory implements specific iteration behavior
- **Builder Module**: Constructs models based on iteration constraints
- **Settings System**: Configures iteration parameters and timeouts
- **CLI Tools**: Provides user interface for iteration requests

## Architecture

### Core Components

#### BaseModelIterator (`core.py`)

The abstract base class providing theory-agnostic iteration logic:

```python
class BaseModelIterator(ABC):
    """Abstract base class for model iteration across theories."""
    
    def __init__(self, build_example):
        self.build_example = build_example
        self.max_iterations = build_example.settings.get('iterate', 2)
        self.found_models = [build_example.model_structure]
        self.solver = self._create_persistent_solver()
        # ... initialization continues
    
    @abstractmethod
    def _create_difference_constraint(self, previous_models):
        """Theory-specific: ensure new model differs from previous ones."""
        pass
    
    @abstractmethod
    def _create_non_isomorphic_constraint(self, z3_model):
        """Theory-specific: prevent structurally identical models."""
        pass
```

**Key Responsibilities**:
- Solver lifecycle management with constraint preservation
- Model validation and invalid model rejection
- Isomorphism detection via graph comparison
- Retry logic with escalating constraints
- Progress reporting and statistics collection

#### Progress System (`progress.py`)

Provides real-time iteration feedback:

```python
class IterationProgress:
    """Progress bar for model iteration."""
    
    def __init__(self, total_iterations, description):
        self.total = total_iterations
        self.description = description
        self.start_time = time.time()
        # ... initialization
```

**Features**:
- ASCII progress bars with percentage completion
- Elapsed time tracking
- Model count and check statistics
- Configurable display modes

#### Statistics Collection (`stats.py`)

Tracks iteration performance and model diversity:

```python
class IterationStatistics:
    """Collects statistics about the iteration process."""
    
    def add_model(self, model_structure, differences):
        """Record information about a discovered model."""
        # Tracks timing, differences, and patterns
```

#### Graph Utilities (`graph_utils.py`)

Implements efficient isomorphism detection:

```python
def create_model_graph(model_structure):
    """Convert model structure to graph representation."""
    # Creates networkx graph from semantic relations

def are_models_isomorphic(model1, model2, timeout=1.0):
    """Check if two models are structurally identical."""
    # Uses graph isomorphism with timeout protection
```

#### Parallel Processing (`parallel.py`)

Optimizes constraint generation for complex theories:

```python
def generate_constraints_parallel(constraint_functions, max_workers=None):
    """Generate multiple constraints in parallel."""
    # Uses ProcessPoolExecutor for CPU-bound operations
```

### Theory-Specific Implementations

Each theory extends BaseModelIterator with specialized behavior:

```
theory_lib/
├── logos/iterate.py             # Hyperintensional iteration
├── exclusion/iterate.py         # Unilateral exclusion iteration
├── imposition/iterate.py        # Imposition theory iteration
├── bimodal/iterate.py           # Temporal-modal iteration
└── default/iterate.py           # Classical logic iteration
```

## Usage Patterns

### Basic Example Configuration

Enable iteration in your example settings:

```python
# In theory_lib/logos/examples.py
MODAL_CM_1_settings = {
    'N': 3,
    'iterate': 2,        # Request 2 distinct models
    'expectation': True, # Expect countermodel
    # ... other settings
}
```

### Advanced Configuration

Fine-tune iteration behavior:

```python
settings = {
    # Core iteration
    'iterate': 5,                    # Find up to 5 models
    
    # Failure handling
    'max_invalid_attempts': 5,       # Stop after 5 invalid models
    'escape_attempts': 3,            # Try 3 times to escape isomorphism
    
    # Performance
    'iteration_solver_timeout': 5.0, # Z3 timeout per iteration
    'show_progress': True,           # Display progress bar
    
    # Theory-specific
    'contingent': True,              # Theory-specific settings
    'non_empty': True,               # still apply during iteration
}
```

### Programmatic Usage

Direct API usage for custom applications:

```python
from model_checker.builder import BuildExample
from model_checker.theory_lib.logos import logos_theory
from model_checker.theory_lib.logos.iterate import LogosModelIterator

# Create example
example = BuildExample(
    name="test",
    semantic_theory=logos_theory,
    premises=['(A \\rightarrow B)'],
    conclusions=['(B \\rightarrow A)']
)

# Run initial model check
example.run_single_test()

# Iterate for more models
if example.model_structure:
    iterator = LogosModelIterator(example)
    models = iterator.iterate()
    
    print(f"Found {len(models)} distinct models")
    
    # Access detailed information
    for msg in iterator.debug_messages:
        if msg.startswith('[ITERATION]'):
            print(msg)
```

### CLI Integration

The dev_cli automatically handles iteration:

```bash
# Run examples with iteration enabled
./dev_cli.py src/model_checker/theory_lib/logos/examples.py

# Output shows:
# MODEL 1/2
# [model output]
# Finding 2 models: [████████████████░░░░░] 1/2
# MODEL 2/2
# [model output with differences highlighted]
```

## Technical Implementation

### Two-Phase Model Building

The framework uses a sophisticated two-phase approach to build MODEL 2+:

1. **Phase 1: Constraint Solution**
   - Solve for variable assignments satisfying difference constraints
   - Extract concrete values from iterator's Z3 model

2. **Phase 2: Model Construction**
   - Create fresh ModelConstraints with new Z3 variables
   - Inject concrete values as constraints
   - Build complete model structure with proper proposition linkage

This approach resolves Z3 variable namespace separation issues while maintaining model independence.

**IMPORTANT**: The model building process in `_build_new_model_structure()` duplicates 
some logic from `BuildExample.__init__()`. This duplication is intentional because:
- Iterator needs to inject concrete Z3 values BEFORE model construction
- BuildExample builds from scratch without pre-existing constraints
- The two use cases have fundamentally different requirements

See `tests/test_model_building_sync.py` for tests that ensure both paths remain consistent.
If the model building process changes, both implementations may need updates.

### Constraint Generation Strategy

The framework uses multiple constraint types:

1. **Difference Constraints**: Ensure semantic differences from previous models
2. **Non-Isomorphic Constraints**: Break structural symmetries
3. **Stronger Constraints**: Aggressive constraints for escaping loops
4. **Invalid Model Prevention**: Exclude models with no possible worlds

### Isomorphism Detection

Models are converted to directed graphs where:
- Nodes represent states with properties (world, possible, verifiers, etc.)
- Edges represent semantic relations (part-of, exclusion, imposition, etc.)
- Graph isomorphism determines structural equivalence

## Theory-Specific Behavior

### Logos Theory (Hyperintensional)

Focuses on verification/falsification differences:

```
=== DIFFERENCES FROM PREVIOUS MODEL ===

World Changes:
  + a.b (now a world)
  - b.c (no longer a world)

Verification Changes:
  Letter A:
    + a.b now verifies A
    - a.c no longer verifies A

Falsification Changes:
  Letter B:
    + b.c now falsifies B
```

### Exclusion Theory (Unilateral)

Emphasizes exclusion relations and coherence:

```
=== DIFFERENCES FROM PREVIOUS MODEL ===

Structural Properties:
  Worlds: 1 → 2

Exclusion Changes:
  □ excludes a.b: False → True
  
Coherence Changes:
  a coheres with b: True → False
```

### Imposition Theory

Tracks imposition function changes:

```
=== DIFFERENCES FROM PREVIOUS MODEL ===

Imposition Changes:
  imp(a, b, c) = d → a.d
  imp(□, a, b) = □ → c
```

## Extension Points

### Implementing for New Theories

Extend BaseModelIterator and implement required methods:

```python
class MyTheoryIterator(BaseModelIterator):
    
    def _create_difference_constraint(self, previous_models):
        """Create constraints ensuring difference from all previous models."""
        constraints = []
        semantics = self.build_example.model_constraints.semantics
        
        for prev_model in previous_models:
            # Add theory-specific difference requirements
            differences = self._collect_differences(prev_model, semantics)
            if differences:
                constraints.append(z3.Or(*differences))
        
        return z3.And(*constraints) if constraints else z3.BoolVal(True)
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Prevent structurally identical models."""
        # Return constraints breaking symmetries
        return self._break_symmetries(z3_model)
    
    def _create_stronger_constraint(self, isomorphic_model):
        """Aggressive constraints for escaping isomorphism."""
        # Force specific structural changes
        return self._force_structural_difference(isomorphic_model)
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate semantic differences for display."""
        return {
            "theory_specific": self._get_semantic_differences(...),
            "structural": self._get_structural_differences(...)
        }
```

### Configuration Options

Add theory-specific settings:

```python
# In theory's semantic.py
THEORY_DEFAULTS = {
    'standard_settings': '...',
    # Iteration-specific
    'iteration_strategy': 'breadth_first',  # Theory-specific strategy
    'difference_threshold': 0.1,            # Minimum semantic distance
}
```

## Performance Optimization

### Best Practices

1. **Constraint Ordering**: Place most restrictive constraints first
2. **Early Termination**: Detect when no more models exist
3. **Caching**: Reuse expensive computations (graphs, evaluations)
4. **Parallel Generation**: Use parallel.py for independent constraints

### Common Issues and Solutions

**Issue**: Iteration gets stuck on isomorphic models
- **Solution**: Implement stronger symmetry-breaking constraints
- **Solution**: Add randomization to constraint generation

**Issue**: Slow iteration for large state spaces
- **Solution**: Reduce N for iteration testing
- **Solution**: Add focused constraints on likely differences

**Issue**: Memory usage with many models
- **Solution**: Store only essential model data
- **Solution**: Use lazy evaluation for differences

## Testing

The test suite ensures framework reliability:

- `test_base_iterator.py`: Abstract method enforcement
- `test_constraint_preservation.py`: Solver isolation verification
- `test_core.py`: Core iteration logic
- `test_edge_cases.py`: Boundary conditions and error handling
- `test_graph_utils.py`: Isomorphism detection accuracy

Run tests:
```bash
pytest src/model_checker/iterate/tests/ -v
```

## References

- **Graph Isomorphism**: Uses NetworkX's VF2 algorithm implementation
- **Z3 Constraint Solving**: Leverages Z3's incremental solving capabilities
- **Design Patterns**: Iterator pattern with template method for theory customization

---

[← Back to Model Checker](../README.md) | [API Reference →](../models/README.md) | [Theory Implementations →](../theory_lib/README.md)