# Model Iteration Framework: Systematic Discovery of Distinct Models

[← Back to Model Checker](../README.md) | [API Reference →](../models/README.md) | [Theory Implementations →](../theory_lib/README.md)

## Directory Structure

```
iterate/
├── README.md                    # This file - framework overview and guide
├── core.py                      # BaseModelIterator implementation (monolithic)
├── base.py                      # Abstract base class definition
├── validation.py                # Z3 boolean evaluation utilities
├── differences.py               # Model difference calculation utilities
├── solver.py                    # Solver management (created, not integrated)
├── model_builder.py             # Model construction (created, not integrated)
├── progress.py                  # Progress bar and timing utilities
├── stats.py                     # Model statistics and analysis
├── parallel.py                  # Parallel constraint generation
├── graph_utils.py               # Graph-based isomorphism detection
├── debug.py                     # Debugging infrastructure for iteration
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

### Design Philosophy

The iteration framework follows a **primarily monolithic architecture** with selective modularization. After extensive refactoring attempts (see Phase 6 in `docs/specs/plans/024_iterator_phase6_modular_split.md`), we discovered that the core iteration logic requires tight coupling between components for proper constraint propagation and model building synchronization. The architecture balances maintainability with the technical requirements of Z3 constraint solving.

### Core Components

#### BaseModelIterator (`base.py` + `core.py`)

The framework uses a two-file approach for the base iterator:

1. **Abstract Definition** (`base.py`):
```python
class BaseModelIterator(ABC):
    """Abstract base class defining the iteration interface."""
    
    @abstractmethod
    def _create_difference_constraint(self, previous_models):
        """Theory-specific: ensure new model differs from previous ones."""
        pass
    
    @abstractmethod
    def _create_non_isomorphic_constraint(self, z3_model):
        """Theory-specific: prevent structurally identical models."""
        pass
```

2. **Concrete Implementation** (`core.py`):
```python
from model_checker.iterate.base import BaseModelIterator
from model_checker.iterate.validation import ModelValidator
from model_checker.iterate.differences import DifferenceCalculator

class BaseModelIterator(BaseModelIterator):
    """Concrete implementation with integrated validation module."""
    
    def __init__(self, build_example):
        self.build_example = build_example
        self.max_iterations = build_example.settings.get('iterate', 2)
        self.found_models = [build_example.model_structure]
        self.solver = self._create_persistent_solver()
        # ... initialization continues
    
    def _evaluate_z3_boolean(self, z3_model, expression):
        """Delegates to validation module for clean separation."""
        return ModelValidator.evaluate_z3_boolean(z3_model, expression)
```

**Key Architectural Decision**: The core.py file remains monolithic (except for validation) because:
- Model building requires complex state synchronization between BuildExample, syntax, semantics, and constraints
- Different theories have varying constructor signatures and initialization sequences
- Z3 constraint injection timing is critical and varies by theory
- Attempting full modularization broke iteration for theories like Relevance

#### Validation Module (`validation.py`) ✓ Integrated

Successfully extracted Z3 boolean evaluation logic:

```python
class ModelValidator:
    """Utilities for validating models during iteration."""
    
    @staticmethod
    def evaluate_z3_boolean(z3_model: z3.ModelRef, expression: Any) -> bool:
        """Safely evaluate a Z3 expression to a Python boolean."""
        if expression is None:
            return False
        
        evaluated = z3_model.evaluate(expression, model_completion=True)
        
        if z3.is_true(evaluated):
            return True
        elif z3.is_false(evaluated):
            return False
        # ... sophisticated evaluation logic
```

**Integration**: Used by core.py for all Z3 boolean evaluations, providing a clean abstraction for this specific functionality.

#### Differences Module (`differences.py`) ✓ Created

Utilities for calculating model differences:

```python
class DifferenceCalculator:
    """Calculates differences between model structures."""
    
    @staticmethod
    def calculate_basic_differences(new_structure, previous_structure) -> Dict[str, Any]:
        """Calculate basic theory-agnostic differences between models."""
        # Compares worlds, verifiers, falsifiers, exclusions, etc.
    
    @staticmethod
    def format_differences_for_display(differences: Dict[str, Any]) -> List[str]:
        """Format differences for user-friendly display."""
        # Creates readable difference summaries
```

**Status**: Created and imported by core.py but not fully integrated due to theory-specific difference calculation requirements.

#### Solver Module (`solver.py`) ✗ Not Integrated

Attempted to extract solver management:

```python
class IterationSolver:
    """Manages Z3 solver lifecycle for model iteration."""
    
    def __init__(self, build_example):
        self.build_example = build_example
        self.original_constraints = self._extract_original_constraints()
        self.solver = self._create_persistent_solver()
```

**Why Not Integrated**: Solver state is tightly coupled with constraint generation and model validation logic. Extracting it would require passing complex state between modules, reducing clarity.

#### Model Builder Module (`model_builder.py`) ✗ Not Integrated

Attempted to extract model construction:

```python
class IterationModelBuilder:
    """Builds new model structures during iteration."""
    
    def build_new_model_structure(self, z3_model: z3.ModelRef, 
                                attempt_number: int = 1,
                                total_attempts: int = 1) -> Optional[Any]:
        """Build a new model structure from a Z3 model."""
        # Complex two-phase building process
```

**Why Not Integrated**: Model building is the most complex part of iteration, requiring:
- Deep knowledge of BuildExample internals
- Theory-specific constructor patterns
- Precise Z3 model injection timing
- Syntax/semantics/constraints coordination

The error encountered during integration (`'LogosSemantics' object has no attribute 'premises'`) revealed fundamental ordering issues that would require significant restructuring to resolve.

#### Debug Infrastructure (`debug.py`)

Provides comprehensive debugging tools:

```python
class DebugModelIterator(BaseModelIterator):
    """Instrumented iterator for debugging constraint issues."""
    
    def _log_event(self, event_type: str, data: Dict[str, Any]):
        """Log iteration events with structured data."""
        timestamp = time.time() - self.start_time
        self.events.append({
            'timestamp': timestamp,
            'type': event_type,
            'data': data
        })
```

**Purpose**: Created during Phase 6 to diagnose why modular splits break iteration. Provides detailed constraint flow tracking and event logging.

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

## How the Iterate Subpackage Works

### Conceptual Flow

The iterate subpackage implements a sophisticated model discovery algorithm:

1. **Initialization**: Start with an existing model (MODEL 1) from BuildExample
2. **Constraint Generation**: Create Z3 constraints that force differences from previous models
3. **Solving**: Use Z3 to find variable assignments satisfying the new constraints
4. **Model Building**: Construct a new ModelStructure using the Z3 solution
5. **Validation**: Ensure the new model is valid and non-isomorphic
6. **Iteration**: Repeat until reaching the requested number of models or exhausting possibilities

### Detailed Implementation Flow

```python
# Simplified flow of BaseModelIterator.iterate()
def iterate(self):
    while len(self.found_models) < self.max_iterations:
        # 1. Generate constraints for a different model
        difference_constraint = self._create_difference_constraint(self.found_models)
        self.solver.add(difference_constraint)
        
        # 2. Try to find a solution
        if self.solver.check() == z3.sat:
            z3_model = self.solver.model()
            
            # 3. Build new model structure (two-phase process)
            new_structure = self._build_new_model_structure(z3_model)
            
            # 4. Validate the model
            if self._is_valid_model(new_structure):
                # 5. Check for isomorphism
                if not self._is_isomorphic_to_any(new_structure):
                    self.found_models.append(new_structure)
                else:
                    # Add stronger constraints and retry
                    self._handle_isomorphic_model(z3_model)
        else:
            # No more models possible
            break
    
    return self.found_models
```

### Critical Technical Details

#### Solver State Management

The iterator maintains a **persistent Z3 solver** that accumulates constraints:

```python
def _create_persistent_solver(self):
    # Extract original constraints from MODEL 1
    original_constraints = self._extract_original_constraints()
    
    # Create solver with same context as original
    solver = z3.Solver(ctx=self.build_example.z3_context)
    
    # Add all original constraints
    solver.add(original_constraints)
    
    return solver
```

This ensures each new model satisfies the original premises while differing from previous models.

#### Two-Phase Model Building

The most complex part is building new models:

**Phase 1: Constraint Solution**
```python
# Z3 solver finds concrete values for variables
z3_model = solver.model()  # e.g., A=True, B=False, world_1=True, etc.
```

**Phase 2: Model Construction**
```python
def _build_new_model_structure(self, z3_model):
    # 1. Create fresh syntax (preserves propositions/operators)
    new_syntax = Syntax(premises, conclusions, operators)
    
    # 2. Create fresh semantics (new Z3 variables!)
    new_semantics = SemanticsClass(settings)
    
    # 3. Create constraints that will inject concrete values
    new_constraints = ModelConstraints(syntax, semantics, settings)
    
    # 4. Inject the concrete values from z3_model
    # This is the KEY step - happens inside ModelStructure.__init__
    
    # 5. Build complete model
    new_structure = ModelStructureClass(syntax, semantics, constraints)
    new_structure.z3_model = z3_model
    
    return new_structure
```

The complexity arises because:
- Each ModelStructure needs its own Z3 variable namespace
- Concrete values from solving must be injected at the right time
- Different theories have different constructor requirements
- The injection happens deep inside the initialization chain

#### Module Integration

The current architecture after Phase 6:

```
core.py (monolithic)
    ├── imports validation.py ✓
    │   └── _evaluate_z3_boolean delegates to ModelValidator
    ├── imports differences.py ✓
    │   └── (ready for future integration)
    ├── contains solver management ✗
    │   └── (too coupled to extract)
    └── contains model building ✗
        └── (too complex to extract)
```

### Why Full Modularization Failed

The attempt to fully modularize revealed fundamental coupling:

1. **State Synchronization**: Model building requires coordinated state from:
   - BuildExample (original configuration)
   - Syntax (proposition structure)
   - Semantics (Z3 variables and constraints)
   - ModelConstraints (constraint generation)

2. **Theory Variations**: Different theories have incompatible patterns:
   - Logos: `LogosModelStructure(syntax, semantics, constraints)`
   - Relevance: Different constructor signature
   - Exclusion: Additional initialization requirements

3. **Z3 Timing**: Concrete value injection must happen at a precise point during initialization, which varies by theory.

4. **Error Example**: The `'LogosSemantics' object has no attribute 'premises'` error showed that extracting model building changed the initialization order, breaking assumptions made by theory code.

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

## Maintenance Notes

### Recent Refactoring (2025-01-11)

The iterator package underwent significant robustness improvements:

1. **Z3 Boolean Evaluation**: Simplified `_evaluate_z3_boolean` method
2. **Attribute Access**: Replaced hasattr() with safe getattr() patterns  
3. **Model Building**: Documented duplication with BuildExample
4. **Testing**: Added regression tests and sync validation
5. **Partial Modularization (Phase 6)**: Successfully extracted validation module and created
   supporting modules (differences, solver, model_builder). Full integration failed due to
   model building complexity, but validation.py is now actively used by core.py.

See `docs/specs/plans/023_iterator_robustness_refactor.md` and `024_iterator_phase6_modular_split.md` for details.

### Architecture Trade-offs

The current hybrid architecture represents a pragmatic balance:

**Monolithic Core** (core.py):
- ✓ Maintains critical state synchronization
- ✓ Preserves Z3 constraint timing requirements
- ✓ Supports all theory variations without breaking
- ✗ Harder to understand and modify
- ✗ Contains significant complexity

**Extracted Modules**:
- ✓ Validation module provides clean abstraction
- ✓ Differences module ready for future integration
- ✓ Debug infrastructure aids troubleshooting
- ✗ Solver and model_builder remain unintegrated
- ✗ Full modularization blocked by technical constraints

### Known Technical Debt

**Model Building Duplication**: The `_build_new_model_structure()` method duplicates
logic from `BuildExample.__init__()`. This is intentional but creates maintenance
burden. Both implementations have cross-references and are protected by
`tests/test_model_building_sync.py`.

### Future Improvements (v2)

- Extract common model building logic into shared utility (requires standardizing theory constructors)
- Complete integration of differences.py module for cleaner difference calculation
- Investigate alternative architectures that preserve Z3 constraint timing
- Optimize constraint generation for large state spaces
- Consider more sophisticated isomorphism detection for complex theories

### Summary: Current Architecture

After Phase 6 implementation and testing, the iterate subpackage uses a **hybrid architecture**:

1. **Monolithic Core** (`core.py`): Contains the main iteration logic including:
   - Solver management
   - Model building
   - Constraint generation
   - Isomorphism detection

2. **Integrated Modules**:
   - `validation.py`: Successfully extracted and actively used for Z3 boolean evaluation
   - `base.py`: Abstract interface definition

3. **Supporting Modules** (created but not integrated):
   - `differences.py`: Ready for future integration
   - `solver.py`: Requires deeper refactoring to integrate
   - `model_builder.py`: Blocked by theory-specific complexity
   - `debug.py`: Available for troubleshooting

This architecture represents a pragmatic balance between maintainability and the technical constraints of Z3-based model iteration. The partial modularization achieved with validation.py demonstrates that selective extraction is possible where coupling is minimal.

## References

- **Graph Isomorphism**: Uses NetworkX's VF2 algorithm implementation
- **Z3 Constraint Solving**: Leverages Z3's incremental solving capabilities
- **Design Patterns**: Iterator pattern with template method for theory customization

---

[← Back to Model Checker](../README.md) | [API Reference →](../models/README.md) | [Theory Implementations →](../theory_lib/README.md)