# Iterator Implementation Standards

This document establishes comprehensive standards for implementing and maintaining model iterators in the model checker system. These standards ensure correct constraint preservation, efficient iteration, and consistent behavior across all theory implementations.

## Table of Contents

1. [Architecture Overview](#architecture-overview)
2. [Constraint Preservation Protocol](#constraint-preservation-protocol)
3. [Evaluation Override Implementation](#evaluation-override-implementation)
4. [Structural Difference Detection](#structural-difference-detection)
5. [Isomorphism Checking and Prevention](#isomorphism-checking-and-prevention)
6. [Theory-Specific Iterator Patterns](#theory-specific-iterator-patterns)
7. [Progress Tracking Standards](#progress-tracking-standards)
8. [Termination Conditions](#termination-conditions)
9. [Model Difference Display Standards](#model-difference-display-standards)
10. [Iterator Implementation Protocol](#iterator-implementation-protocol)
11. [Implementation Patterns](#implementation-patterns)
12. [Success Metrics and Validation](#success-metrics-and-validation)
13. [Debugging Guidelines](#debugging-guidelines)
14. [Templates for New Iterators](#templates-for-new-iterators)

## Architecture Overview

The iterator system uses a modular architecture with clear separation of concerns:

### Core Components

```
BaseModelIterator (core.py)
├── IteratorCore (iterator.py)           # Main iteration loop and control flow
├── ConstraintGenerator (constraints.py) # Constraint creation and management
├── ModelBuilder (models.py)             # Model creation and validation
├── IsomorphismChecker (graph.py)        # Graph-based isomorphism detection
├── TerminationManager (metrics.py)      # Termination logic and result formatting
└── DifferenceCalculator (models.py)     # Model difference calculation
```

### Theory-Specific Extensions

```
LogosModelIterator → ExclusionModelIterator → BimodalModelIterator
                  ├── ImpositionModelIterator
                  └── [Custom Theory Iterators]
```

## Constraint Preservation Protocol

### 1. Original Constraint Preservation

**CRITICAL REQUIREMENT**: The iterator MUST preserve all original constraints from the initial model.

```python
def _create_persistent_solver(self) -> z3.Solver:
    """Create a persistent solver with original constraints.
    
    This method MUST:
    1. Preserve all assertions from the original solver
    2. Handle fallback to stored_solver if main solver is None
    3. Raise clear errors if no solver is available
    """
    original_solver = self.build_example.model_structure.solver
    if original_solver is None:
        original_solver = getattr(self.build_example.model_structure, 'stored_solver', None)
        
    if original_solver is None:
        raise RuntimeError("No solver available - both solver and stored_solver are None")
        
    persistent_solver = z3.Solver()
    for assertion in original_solver.assertions():
        persistent_solver.add(assertion)
    return persistent_solver
```

### 2. Constraint Layering Strategy

Constraints MUST be added in layers to ensure correctness:

1. **Base Layer**: Original model constraints (premises, conclusions, theory axioms)
2. **Difference Layer**: Constraints ensuring difference from previous models
3. **Anti-Isomorphism Layer**: Constraints preventing isomorphic duplicates
4. **Stronger Layer**: Additional constraints for escaping isomorphism loops

### 3. Constraint Validation Protocol

```python
def validate_constraint_preservation(self, new_model: z3.ModelRef) -> bool:
    """Validate that new model satisfies all original constraints.
    
    Returns:
        bool: True if all original constraints are satisfied
    """
    for constraint in self.original_constraints:
        if not z3.is_true(new_model.eval(constraint, model_completion=True)):
            logger.error(f"Constraint violation: {constraint}")
            return False
    return True
```

## Evaluation Override Implementation

### 1. Safe Model Evaluation Pattern

When evaluating Z3 expressions against models, ALWAYS use this pattern:

```python
def safe_eval(self, model: z3.ModelRef, expr: z3.ExprRef) -> Any:
    """Safely evaluate Z3 expression against model.
    
    Handles the various return types from Z3 model evaluation:
    - True/False (Python booleans)
    - z3.BoolRef (symbolic expressions)
    - z3.RatNumRef (numeric values)
    - String representations as fallback
    """
    try:
        result = model.eval(expr, model_completion=True)
        
        # Handle boolean results
        if z3.is_true(result):
            return True
        elif z3.is_false(result):
            return False
        
        # Handle numeric results
        if hasattr(result, 'as_long'):
            return result.as_long()
        
        # Handle symbolic expressions (partial evaluation)
        if hasattr(result, 'sort') and result.sort().kind() == z3.Z3_BOOL_SORT:
            # Try to simplify
            simplified = z3.simplify(result)
            if z3.is_true(simplified):
                return True
            elif z3.is_false(simplified):
                return False
            
        # Fallback to string representation
        return str(result)
        
    except z3.Z3Exception as e:
        logger.warning(f"Z3 evaluation failed for {expr}: {e}")
        return None
```

### 2. Model Completion Strategy

ALWAYS use `model_completion=True` when evaluating expressions to ensure deterministic results:

```python
# CORRECT
result = model.eval(expression, model_completion=True)

# INCORRECT - may return partial results
result = model.eval(expression)
```

## Structural Difference Detection

### 1. Multi-Level Difference Detection

Implement difference detection at multiple levels of granularity:

```python
def calculate_differences(self, new_structure, previous_structure) -> Dict[str, Any]:
    """Calculate comprehensive differences between models.
    
    Returns differences at multiple levels:
    - Structural: world counts, state counts
    - Semantic: verification/falsification changes
    - Theory-specific: relation changes, accessibility changes
    """
    differences = {
        "structural": self._calculate_structural_differences(new_structure, previous_structure),
        "semantic": self._calculate_semantic_differences(new_structure, previous_structure),
        "theory_specific": self._calculate_theory_differences(new_structure, previous_structure)
    }
    return differences
```

### 2. State-Level Granularity

Track differences at the individual state level for precise debugging:

```python
def _calculate_verification_differences(self, new_structure, previous_structure):
    """Calculate verification differences at state level."""
    verification_diffs = {}
    
    for state in new_structure.all_states:
        for letter in new_structure.sentence_letters:
            old_verify = self.safe_eval(previous_structure.z3_model, 
                                      semantics.verify(state, letter.sentence_letter))
            new_verify = self.safe_eval(new_structure.z3_model, 
                                      semantics.verify(state, letter.sentence_letter))
            
            if old_verify != new_verify:
                state_str = bitvec_to_substates(state, new_structure.N)
                key = f"{state_str} verifies {letter}"
                verification_diffs[key] = {"old": old_verify, "new": new_verify}
    
    return verification_diffs
```

## Isomorphism Checking and Prevention

### 1. Graph-Based Isomorphism Detection

Use NetworkX for robust isomorphism detection when available:

```python
class IsomorphismChecker:
    """Handles graph-based isomorphism detection between models."""
    
    def __init__(self):
        self.model_graphs = []  # Cache of previously computed graphs
        self.has_networkx = self._check_networkx()
    
    def check_isomorphism(self, new_structure, new_model, previous_structures, previous_models):
        """Check if new model is isomorphic to any previous model.
        
        Returns:
            Tuple[bool, Optional[z3.ModelRef]]: (is_isomorphic, isomorphic_model)
        """
        if not self.has_networkx:
            logger.warning("NetworkX not available - skipping isomorphism check")
            return False, None
        
        new_graph = self._create_model_graph(new_structure, new_model)
        
        for i, cached_graph in enumerate(self.model_graphs):
            if self._graphs_isomorphic(new_graph, cached_graph):
                return True, previous_models[i]
        
        # Cache the new graph
        self.model_graphs.append(new_graph)
        return False, None
```

### 2. Fallback Non-Isomorphic Constraints

When NetworkX is unavailable, implement basic structural constraints:

```python
def _create_basic_difference_constraint(self, previous_model):
    """Create basic structural difference constraint when graph isomorphism unavailable."""
    constraints = []
    
    # Different world count
    world_count_constraint = self._create_world_count_constraint(previous_model)
    if world_count_constraint:
        constraints.append(world_count_constraint)
    
    # Different verification patterns
    verification_constraints = self._create_verification_constraints(previous_model)
    constraints.extend(verification_constraints)
    
    return z3.Or(*constraints) if constraints else z3.BoolVal(True)
```

### 3. Isomorphism Loop Escape

Implement escalating strategies for escaping isomorphism loops:

```python
def _create_stronger_constraint(self, isomorphic_model, attempt_count=1):
    """Create progressively stronger constraints to escape isomorphism loops."""
    
    if attempt_count == 1:
        # First attempt: Exclude specific state configurations
        return self._create_state_exclusion_constraint(isomorphic_model)
    
    elif attempt_count == 2:
        # Second attempt: Require different verification patterns
        return self._create_verification_exclusion_constraint(isomorphic_model)
    
    elif attempt_count >= 3:
        # Final attempt: Aggressive structural constraints
        return self._create_aggressive_difference_constraint(isomorphic_model)
    
    return None
```

## Theory-Specific Iterator Patterns

### 1. Inheritance Hierarchy Standards

Theory iterators MUST follow this inheritance pattern:

```python
class CustomTheoryIterator(LogosModelIterator):
    """Iterator for custom theory extending logos semantics."""
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Override to add theory-specific difference calculation."""
        # Start with base logos differences
        base_differences = super()._calculate_differences(new_structure, previous_structure)
        
        # Add theory-specific differences
        theory_differences = self._calculate_theory_specific_differences(
            new_structure, previous_structure
        )
        
        # Merge maintaining structure
        base_differences.update(theory_differences)
        return base_differences
    
    def _create_difference_constraint(self, previous_models):
        """Override to add theory-specific constraints."""
        # Get base constraints
        base_constraints = super()._create_difference_constraint(previous_models)
        
        # Add theory-specific constraints
        theory_constraints = self._create_theory_constraints(previous_models)
        
        return z3.And(base_constraints, *theory_constraints)
```

### 2. Theory-Specific Constraint Patterns

Each theory MUST implement these methods:

```python
def _create_theory_constraints(self, previous_models: List[z3.ModelRef]) -> List[z3.BoolRef]:
    """Create theory-specific difference constraints.
    
    Examples:
    - Exclusion theory: witness function differences
    - Bimodal theory: accessibility relation differences
    - Custom theories: domain-specific relation differences
    """
    pass

def _calculate_theory_specific_differences(self, new_structure, previous_structure) -> Dict:
    """Calculate theory-specific semantic differences.
    
    Must return structured dict compatible with display system.
    """
    pass
```

### 3. Theory Extension Registry

Maintain a registry for theory-specific extensions:

```python
THEORY_ITERATOR_REGISTRY = {
    'logos': LogosModelIterator,
    'exclusion': ExclusionModelIterator,
    'imposition': ImpositionModelIterator,
    'bimodal': BimodalModelIterator,
    # Add new theories here
}

def get_iterator_for_theory(theory_name: str, build_example) -> BaseModelIterator:
    """Factory function for creating theory-appropriate iterators."""
    iterator_class = THEORY_ITERATOR_REGISTRY.get(theory_name, LogosModelIterator)
    return iterator_class(build_example)
```

## Progress Tracking Standards

### 1. Unified Progress Interface

All iterators MUST support the unified progress interface:

```python
class IteratorProgressProtocol:
    """Protocol for iterator progress tracking."""
    
    def start_model_search(self, model_number: int, start_time: float = None):
        """Signal start of search for specific model number."""
        pass
    
    def model_checked(self):
        """Signal that a potential model was checked."""
        pass
    
    def model_skipped_isomorphic(self):
        """Signal that a model was skipped due to isomorphism."""
        pass
    
    def complete_model_search(self, found: bool):
        """Signal completion of search for current model."""
        pass
```

### 2. Progress Integration Pattern

```python
def iterate_generator(self):
    """Generator that yields models with progress tracking."""
    current_search_model = 0
    
    while self.current_iteration < self.max_iterations:
        model_number = len(self.model_structures) + 1
        
        # Start progress tracking for new model search
        if self.search_progress and current_search_model != model_number:
            self.search_progress.start_model_search(model_number, start_time=self.current_search_start)
            current_search_model = model_number
        
        # ... iteration logic ...
        
        # Update progress during search
        if self.search_progress:
            self.search_progress.model_checked()
        
        # Handle isomorphic models
        if is_isomorphic:
            if self.search_progress:
                self.search_progress.model_skipped_isomorphic()
            continue
        
        # Complete search when model found
        if self.search_progress:
            self.search_progress.complete_model_search(found=True)
        
        yield new_structure
```

## Termination Conditions

### 1. Standard Termination Criteria

Implement these termination conditions in order of priority:

```python
class TerminationManager:
    """Manages iteration termination logic."""
    
    def should_terminate(self, current_iteration, max_iterations, 
                        consecutive_invalid_count, checked_model_count) -> Tuple[bool, str]:
        """Check if iteration should terminate.
        
        Returns:
            Tuple[bool, str]: (should_terminate, reason)
        """
        # 1. Maximum iterations reached
        if current_iteration >= max_iterations:
            return True, f"Found all {max_iterations} requested models"
        
        # 2. Timeout exceeded
        if self.get_elapsed_time() > self.timeout:
            return True, f"Timeout ({self.timeout}s) exceeded"
        
        # 3. Too many consecutive invalid models
        if consecutive_invalid_count >= self.max_invalid_attempts:
            return True, f"Too many consecutive invalid models ({consecutive_invalid_count})"
        
        # 4. Search space exhausted
        if checked_model_count > self.max_search_attempts:
            return True, f"Search space likely exhausted ({checked_model_count} models checked)"
        
        return False, ""
```

### 2. Timeout Management

Implement timeout at multiple levels:

```python
# Per-model search timeout
elapsed = time.time() - self.current_search_start
model_timeout = self.settings.get('max_time', 300)
if elapsed > model_timeout:
    logger.warning(f"Model {model_number} search timeout ({model_timeout}s) reached")
    break

# Overall iteration timeout
total_elapsed = time.time() - iteration_start_time
total_timeout = self.settings.get('iteration_timeout', 1800)  # 30 minutes
if total_elapsed > total_timeout:
    logger.warning(f"Overall iteration timeout ({total_timeout}s) reached")
    break
```

## Model Difference Display Standards

### 1. Structured Difference Format

All difference calculations MUST return this standardized format:

```python
{
    "structural": {
        "worlds": {"old_count": int, "new_count": int},
        "possible_states": {"old_count": int, "new_count": int}
    },
    "semantic": {
        "verify": {
            "letter_name": {
                "state_representation": {"old": bool, "new": bool}
            }
        },
        "falsify": {
            "letter_name": {
                "state_representation": {"old": bool, "new": bool}
            }
        }
    },
    "theory_specific": {
        # Theory-dependent structure
        "accessibility": {...},
        "parthood": {...},
        "exclusion": {...},
        "witnesses": {...}
    }
}
```

### 2. State Representation Standards

Use consistent state representation across all theories:

```python
def format_state_representation(state_bitvector: int, N: int) -> str:
    """Convert state bitvector to human-readable representation.
    
    Args:
        state_bitvector: Integer representing state as bitvector
        N: Number of sentence letters
    
    Returns:
        str: Human-readable state (e.g., "a.b", "¬a.¬b.c")
    """
    return bitvec_to_substates(state_bitvector, N)
```

### 3. Display Integration

Differences MUST be stored on model structures for access by display systems:

```python
# Store differences for access by output systems
new_structure.model_differences = differences

# Merge theory-specific with generic differences
if hasattr(model, 'model_differences') and model.model_differences:
    model.model_differences.update(theory_diffs)
else:
    model.model_differences = theory_diffs
```

## Iterator Implementation Protocol

### 1. Required Interface Implementation

All theory iterators MUST implement this interface:

```python
class TheoryModelIterator(BaseModelIterator):
    """Template for theory-specific model iterators."""
    
    def _calculate_differences(self, new_structure, previous_structure) -> Dict[str, Any]:
        """REQUIRED: Calculate theory-specific differences."""
        raise NotImplementedError("Must implement _calculate_differences")
    
    def _create_difference_constraint(self, previous_models: List[z3.ModelRef]) -> z3.BoolRef:
        """REQUIRED: Create constraints ensuring difference from previous models."""
        raise NotImplementedError("Must implement _create_difference_constraint")
    
    def _create_non_isomorphic_constraint(self, z3_model: z3.ModelRef) -> z3.BoolRef:
        """OPTIONAL: Create constraints preventing isomorphic models."""
        return z3.BoolVal(True)  # Default: no constraint
    
    def _create_stronger_constraint(self, isomorphic_model: z3.ModelRef) -> Optional[z3.BoolRef]:
        """OPTIONAL: Create stronger constraints for escaping isomorphism."""
        return None  # Default: no stronger constraint
```

### 2. Initialization Protocol

```python
def __init__(self, build_example: 'BuildExample') -> None:
    """Standard initialization protocol for theory iterators."""
    
    # 1. Validate build_example
    self._validate_build_example(build_example)
    
    # 2. Call parent constructor
    super().__init__(build_example)
    
    # 3. Initialize theory-specific components
    self._initialize_theory_components()
    
    # 4. Set up theory-specific settings
    self._configure_theory_settings()

def _validate_build_example(self, build_example) -> None:
    """Validate that build_example is compatible with this theory."""
    if not hasattr(build_example, 'semantic_theory'):
        raise ValueError("BuildExample missing semantic_theory")
    
    theory_name = build_example.semantic_theory.get('name', '')
    if not self._is_compatible_theory(theory_name):
        raise ValueError(f"Iterator not compatible with theory: {theory_name}")
```

## Implementation Patterns

### 1. Generator vs List Interface Pattern

Provide both interfaces for compatibility:

```python
def iterate(self) -> List['ModelStructure']:
    """List interface for backward compatibility."""
    return list(self.iterate_generator())

def iterate_generator(self) -> Generator['ModelStructure', None, None]:
    """Generator interface for memory efficiency and progress tracking."""
    # Implementation details...
    yield model_structure
```

### 2. Error Handling Pattern

Use structured error handling with context:

```python
try:
    # Iteration logic
    pass
except z3.Z3Exception as e:
    raise ModelExtractionError(
        model_num=current_iteration,
        reason=f"Z3 error: {str(e)}",
        suggestion="Check formula complexity and solver timeout settings"
    ) from e
except Exception as e:
    raise IterationStateError(
        state="iteration_loop",
        reason=str(e),
        suggestion="Check logs for detailed error information"
    ) from e
```

### 3. Resource Cleanup Pattern

Ensure proper cleanup of Z3 resources:

```python
def __enter__(self):
    return self

def __exit__(self, exc_type, exc_val, exc_tb):
    """Clean up Z3 resources."""
    if hasattr(self, 'solver'):
        # Z3 solvers are automatically garbage collected
        self.solver = None
    
    if hasattr(self, 'constraint_generator'):
        self.constraint_generator = None
```

## Success Metrics and Validation

### 1. Correctness Metrics

Implement these validation checks:

```python
class IteratorValidator:
    """Validates iterator correctness and performance."""
    
    def validate_constraint_preservation(self, models: List[z3.ModelRef]) -> bool:
        """Verify all models satisfy original constraints."""
        for i, model in enumerate(models):
            if not self._model_satisfies_constraints(model, self.original_constraints):
                logger.error(f"Model {i+1} violates original constraints")
                return False
        return True
    
    def validate_model_differences(self, structures: List['ModelStructure']) -> bool:
        """Verify all models are genuinely different."""
        for i in range(len(structures)):
            for j in range(i + 1, len(structures)):
                if self._models_equivalent(structures[i], structures[j]):
                    logger.error(f"Models {i+1} and {j+1} are equivalent")
                    return False
        return True
    
    def validate_termination_conditions(self, iterator) -> bool:
        """Verify iterator terminated for valid reasons."""
        if iterator.current_iteration < iterator.max_iterations:
            # Check if termination was justified
            return self._validate_early_termination(iterator)
        return True
```

### 2. Performance Metrics

Track these performance indicators:

```python
class IteratorMetrics:
    """Tracks iterator performance metrics."""
    
    def __init__(self):
        self.models_checked = 0
        self.isomorphic_skipped = 0
        self.search_times = []
        self.constraint_generation_times = []
        self.isomorphism_check_times = []
    
    def calculate_efficiency_ratio(self) -> float:
        """Calculate ratio of found models to checked models."""
        if self.models_checked == 0:
            return 0.0
        return len(self.search_times) / self.models_checked
    
    def get_average_search_time(self) -> float:
        """Get average time per model search."""
        return sum(self.search_times) / len(self.search_times) if self.search_times else 0.0
```

### 3. Quality Thresholds

Set quality thresholds for iterator performance:

```python
QUALITY_THRESHOLDS = {
    'min_efficiency_ratio': 0.1,      # At least 10% of checked models should be valid
    'max_average_search_time': 60.0,   # Average search time should be under 60 seconds
    'max_isomorphic_ratio': 0.5,       # No more than 50% of models should be isomorphic
    'min_difference_coverage': 0.8     # At least 80% of possible differences should be found
}
```

## Debugging Guidelines

### 1. Debug Information Collection

Implement comprehensive debug information collection:

```python
class IteratorDebugger:
    """Collects and manages debug information during iteration."""
    
    def __init__(self, iterator):
        self.iterator = iterator
        self.debug_messages = []
        self.model_history = []
        self.constraint_history = []
        self.timing_data = {}
    
    def log_model_attempt(self, model_num: int, constraints: List[z3.BoolRef]):
        """Log each model search attempt with constraints."""
        self.debug_messages.append(f"Attempting model {model_num} with {len(constraints)} constraints")
        self.constraint_history.append({
            'model_num': model_num,
            'constraints': [str(c) for c in constraints],
            'timestamp': time.time()
        })
    
    def log_isomorphism_detection(self, model_num: int, isomorphic_to: int):
        """Log isomorphism detection events."""
        self.debug_messages.append(f"Model {model_num} isomorphic to model {isomorphic_to}")
    
    def generate_debug_report(self) -> str:
        """Generate comprehensive debug report."""
        report = []
        report.append("=== Iterator Debug Report ===")
        report.append(f"Total models found: {len(self.iterator.model_structures)}")
        report.append(f"Total models checked: {self.iterator.checked_model_count}")
        report.append(f"Isomorphic models skipped: {self.iterator.isomorphic_model_count}")
        report.append("")
        
        # Add constraint history
        report.append("=== Constraint History ===")
        for entry in self.constraint_history:
            report.append(f"Model {entry['model_num']}: {len(entry['constraints'])} constraints")
        
        return "\n".join(report)
```

### 2. Common Debugging Scenarios

#### Scenario 1: Iterator Finding No Additional Models

```python
def debug_no_additional_models(self):
    """Debug when iterator cannot find models beyond the first."""
    
    # Check 1: Verify constraint generation
    constraints = self._create_difference_constraint([self.found_models[0]])
    self.debug_messages.append(f"Generated constraints: {constraints}")
    
    # Check 2: Test constraint satisfiability
    test_solver = z3.Solver()
    for constraint in self.original_constraints:
        test_solver.add(constraint)
    test_solver.add(constraints)
    
    result = test_solver.check()
    self.debug_messages.append(f"Constraint satisfiability: {result}")
    
    if result == z3.unsat:
        self.debug_messages.append("ISSUE: Difference constraints are unsatisfiable with original constraints")
    
    # Check 3: Examine first model structure
    first_model = self.build_example.model_structure
    self.debug_messages.append(f"First model world count: {len(getattr(first_model, 'z3_world_states', []))}")
    self.debug_messages.append(f"First model possible states: {len(getattr(first_model, 'z3_possible_states', []))}")
```

#### Scenario 2: Iterator Finding Only Isomorphic Models

```python
def debug_isomorphic_models(self):
    """Debug when iterator only finds isomorphic models."""
    
    # Check 1: Verify isomorphism checker is working
    if not hasattr(self.isomorphism_checker, 'has_networkx') or not self.isomorphism_checker.has_networkx:
        self.debug_messages.append("WARNING: NetworkX not available - isomorphism detection disabled")
    
    # Check 2: Examine constraint strength
    self.debug_messages.append(f"Escape attempts: {getattr(self, 'escape_attempts', 0)}")
    
    # Check 3: Check stronger constraint generation
    if len(self.found_models) > 1:
        stronger_constraint = self._create_stronger_constraint(self.found_models[-1])
        self.debug_messages.append(f"Stronger constraint generated: {stronger_constraint is not None}")
```

### 3. Debug Output Standards

Use structured debug output:

```python
def format_debug_output(self) -> str:
    """Format debug information for display."""
    lines = []
    lines.append("=== Iterator Debug Information ===")
    lines.append(f"Theory: {self.build_example.semantic_theory.get('name', 'unknown')}")
    lines.append(f"Max iterations: {self.max_iterations}")
    lines.append(f"Found models: {len(self.model_structures)}")
    lines.append(f"Checked models: {self.checked_model_count}")
    lines.append(f"Isomorphic skipped: {self.isomorphic_model_count}")
    lines.append("")
    
    lines.append("=== Debug Messages ===")
    for i, message in enumerate(self.debug_messages):
        lines.append(f"{i+1:3d}. {message}")
    
    return "\n".join(lines)
```

## Templates for New Iterators

### 1. Basic Theory Iterator Template

```python
"""Template for implementing a new theory iterator.

Copy this template and replace [THEORY_NAME] with your theory name.
Implement all methods marked with # TODO.
"""

import z3
import logging
from typing import Dict, List, Any, Optional
from model_checker.iterate.core import BaseModelIterator
from model_checker.utils import bitvec_to_substates

logger = logging.getLogger(__name__)


class [THEORY_NAME]ModelIterator(BaseModelIterator):
    """Model iterator for [THEORY_NAME] theory.
    
    This iterator extends BaseModelIterator with [THEORY_NAME]-specific
    implementations for finding multiple distinct models.
    """
    
    def _calculate_differences(self, new_structure, previous_structure) -> Dict[str, Any]:
        """Calculate [THEORY_NAME]-specific differences between models.
        
        TODO: Implement theory-specific difference calculation.
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Structured differences between the models
        """
        # Start with structural differences
        differences = {
            "structural": self._calculate_structural_differences(new_structure, previous_structure),
            "semantic": self._calculate_semantic_differences(new_structure, previous_structure),
            "[theory_name]_specific": self._calculate_theory_differences(new_structure, previous_structure)
        }
        
        return differences
    
    def _calculate_theory_differences(self, new_structure, previous_structure) -> Dict[str, Any]:
        """Calculate theory-specific semantic differences.
        
        TODO: Implement specific difference calculation for your theory.
        
        Examples:
        - Accessibility relation changes (modal theories)
        - Part-whole relation changes (mereological theories)
        - Custom relation changes (domain-specific theories)
        """
        theory_diffs = {}
        
        # Example pattern for relation differences
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model
        semantics = new_structure.semantics
        
        # TODO: Replace with your theory's relations
        relation_diffs = {}
        for s1 in new_structure.all_states:
            for s2 in new_structure.all_states:
                if s1 != s2:
                    # TODO: Replace 'custom_relation' with your relation
                    old_rel = previous_model.eval(semantics.custom_relation(s1, s2), model_completion=True)
                    new_rel = new_model.eval(semantics.custom_relation(s1, s2), model_completion=True)
                    
                    if bool(old_rel) != bool(new_rel):
                        s1_str = bitvec_to_substates(s1, new_structure.N)
                        s2_str = bitvec_to_substates(s2, new_structure.N)
                        key = f"{s1_str} [relation] {s2_str}"  # TODO: Replace [relation] with relation name
                        
                        relation_diffs[key] = {
                            "old": bool(old_rel),
                            "new": bool(new_rel)
                        }
        
        if relation_diffs:
            theory_diffs["[relation_name]"] = relation_diffs  # TODO: Replace [relation_name]
        
        return theory_diffs
    
    def _create_difference_constraint(self, previous_models: List[z3.ModelRef]) -> z3.BoolRef:
        """Create constraints ensuring difference from previous models.
        
        TODO: Implement theory-specific constraint generation.
        
        Args:
            previous_models: List of Z3 models to differentiate from
            
        Returns:
            z3.BoolRef: Constraint ensuring difference
        """
        constraints = []
        semantics = self.build_example.model_constraints.semantics
        
        for prev_model in previous_models:
            model_constraints = []
            
            # Start with basic constraints (world count, verification patterns)
            basic_constraints = self._create_basic_constraints(prev_model, semantics)
            model_constraints.extend(basic_constraints)
            
            # Add theory-specific constraints
            theory_constraints = self._create_theory_constraints(prev_model, semantics)
            model_constraints.extend(theory_constraints)
            
            # Combine constraints for this model
            if model_constraints:
                constraints.append(z3.Or(*model_constraints))
        
        return z3.And(*constraints) if constraints else z3.BoolVal(True)
    
    def _create_theory_constraints(self, prev_model: z3.ModelRef, semantics) -> List[z3.BoolRef]:
        """Create theory-specific difference constraints.
        
        TODO: Implement constraints specific to your theory.
        
        Args:
            prev_model: Previous Z3 model to differentiate from
            semantics: Theory semantics object
            
        Returns:
            list: Theory-specific constraints
        """
        constraints = []
        
        # TODO: Add theory-specific constraint generation
        # Example pattern for relation constraints:
        for s1 in range(2**semantics.N):
            for s2 in range(2**semantics.N):
                if s1 != s2:
                    # TODO: Replace with your theory's relation
                    prev_rel = prev_model.eval(semantics.custom_relation(s1, s2), model_completion=True)
                    constraints.append(semantics.custom_relation(s1, s2) != prev_rel)
        
        return constraints
    
    def _create_basic_constraints(self, prev_model: z3.ModelRef, semantics) -> List[z3.BoolRef]:
        """Create basic structural difference constraints."""
        constraints = []
        
        # World count constraint
        world_count_constraint = self._create_world_count_constraint(prev_model, semantics)
        if world_count_constraint:
            constraints.append(world_count_constraint)
        
        # Verification pattern constraints
        verification_constraints = self._create_verification_constraints(prev_model, semantics)
        constraints.extend(verification_constraints)
        
        return constraints
    
    def _create_world_count_constraint(self, prev_model: z3.ModelRef, semantics) -> Optional[z3.BoolRef]:
        """Create constraint requiring different number of worlds."""
        # Count worlds in previous model
        prev_world_count = 0
        for state in range(2**semantics.N):
            if z3.is_true(prev_model.eval(semantics.is_world(state), model_completion=True)):
                prev_world_count += 1
        
        # Current model must have different number of worlds
        current_world_count = z3.Sum([
            z3.If(semantics.is_world(state), 1, 0) 
            for state in range(2**semantics.N)
        ])
        
        return current_world_count != prev_world_count
    
    def _create_verification_constraints(self, prev_model: z3.ModelRef, semantics) -> List[z3.BoolRef]:
        """Create constraints on verification pattern differences."""
        constraints = []
        
        # Get sentence letters
        syntax = self.build_example.example_syntax
        if not hasattr(syntax, 'sentence_letters'):
            return constraints
        
        for letter_obj in syntax.sentence_letters:
            if hasattr(letter_obj, 'sentence_letter'):
                atom = letter_obj.sentence_letter
                
                # Check each state
                for state in range(2**semantics.N):
                    # Get previous values
                    prev_verify = prev_model.eval(semantics.verify(state, atom), model_completion=True)
                    
                    # TODO: Add falsify constraint if your theory supports it
                    # prev_falsify = prev_model.eval(semantics.falsify(state, atom), model_completion=True)
                    
                    # Create constraints for differences
                    constraints.append(semantics.verify(state, atom) != prev_verify)
                    # constraints.append(semantics.falsify(state, atom) != prev_falsify)
        
        return constraints


# Module-level convenience functions
def iterate_example(example, max_iterations=None):
    """Iterate a [THEORY_NAME] theory example to find multiple models.
    
    Args:
        example: A BuildExample instance with [THEORY_NAME] theory.
        max_iterations: Maximum number of models to find.
        
    Returns:
        list: List of model structures with distinct models.
    """
    if max_iterations is not None:
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations
    
    # Create iterator and run
    iterator = [THEORY_NAME]ModelIterator(example)
    models = iterator.iterate()
    
    # Store iterator for debug message access
    example._iterator = iterator
    
    return models


def iterate_example_generator(example, max_iterations=None):
    """Generator version that yields models incrementally.
    
    Args:
        example: A BuildExample instance with [THEORY_NAME] theory.
        max_iterations: Maximum number of models to find.
        
    Yields:
        ModelStructure: Each distinct model as it's found.
    """
    if max_iterations is not None:
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations
    
    # Create iterator
    iterator = [THEORY_NAME]ModelIterator(example)
    
    # Store iterator for debug message access
    example._iterator = iterator
    
    # Use generator interface
    yield from iterator.iterate_generator()


# Mark generator for BuildModule detection
iterate_example_generator.returns_generator = True
iterate_example_generator.__wrapped__ = iterate_example_generator
```

### 2. Testing Template

```python
"""Test template for [THEORY_NAME] iterator.

Copy this template and implement theory-specific tests.
"""

import pytest
import z3
from model_checker.theory_lib.[theory_name].iterate import [THEORY_NAME]ModelIterator
from model_checker.builder.example import BuildExample


class Test[THEORY_NAME]Iterator:
    """Test suite for [THEORY_NAME] model iterator."""
    
    def test_basic_iteration(self, [theory_name]_example):
        """Test basic iteration functionality."""
        # Set up for multiple models
        [theory_name]_example.settings['iterate'] = 3
        
        # Create iterator and run
        iterator = [THEORY_NAME]ModelIterator([theory_name]_example)
        models = iterator.iterate()
        
        # Verify results
        assert len(models) >= 1
        assert all(hasattr(model, 'z3_model_status') for model in models)
        assert all(model.z3_model_status for model in models)
    
    def test_difference_calculation(self, [theory_name]_example):
        """Test theory-specific difference calculation."""
        # Set up for two models
        [theory_name]_example.settings['iterate'] = 2
        
        iterator = [THEORY_NAME]ModelIterator([theory_name]_example)
        models = iterator.iterate()
        
        if len(models) >= 2:
            differences = iterator._calculate_differences(models[1], models[0])
            
            # Verify difference structure
            assert isinstance(differences, dict)
            assert "structural" in differences
            assert "[theory_name]_specific" in differences
            
            # TODO: Add theory-specific assertions
            # Example: assert "custom_relation" in differences["[theory_name]_specific"]
    
    def test_constraint_generation(self, [theory_name]_example):
        """Test theory-specific constraint generation."""
        iterator = [THEORY_NAME]ModelIterator([theory_name]_example)
        
        # Get initial model
        initial_model = [theory_name]_example.model_structure.z3_model
        
        # Generate difference constraints
        constraints = iterator._create_difference_constraint([initial_model])
        
        # Verify constraint structure
        assert isinstance(constraints, z3.BoolRef)
        
        # Test constraint satisfiability
        test_solver = z3.Solver()
        test_solver.add(constraints)
        result = test_solver.check()
        
        # Should be satisfiable (difference possible)
        assert result == z3.sat or result == z3.unknown
    
    def test_error_handling(self, [theory_name]_example):
        """Test iterator error handling."""
        # Test with invalid settings
        [theory_name]_example.settings['iterate'] = -1
        
        with pytest.raises((ValueError, RuntimeError)):
            iterator = [THEORY_NAME]ModelIterator([theory_name]_example)
    
    def test_generator_interface(self, [theory_name]_example):
        """Test generator interface functionality."""
        [theory_name]_example.settings['iterate'] = 3
        
        iterator = [THEORY_NAME]ModelIterator([theory_name]_example)
        models = list(iterator.iterate_generator())
        
        # Verify generator yields correct number of models
        assert len(models) >= 1
        
        # Verify models have differences stored
        for model in models[1:]:
            assert hasattr(model, 'model_differences')


@pytest.fixture
def [theory_name]_example():
    """Fixture providing a basic [THEORY_NAME] example for testing."""
    # TODO: Implement fixture that creates a BuildExample with your theory
    # This should return a BuildExample instance configured for your theory
    pass
```

### 3. Integration Checklist

When implementing a new iterator, verify these integration points:

#### Required Files:
- [ ] `src/model_checker/theory_lib/[theory]/iterate.py` - Main iterator implementation
- [ ] `src/model_checker/theory_lib/[theory]/tests/integration/test_iterate.py` - Integration tests
- [ ] `src/model_checker/theory_lib/[theory]/docs/ITERATE.md` - Theory-specific documentation

#### Required Functions:
- [ ] `iterate_example(example, max_iterations=None)` - Backward compatibility function
- [ ] `iterate_example_generator(example, max_iterations=None)` - Generator interface
- [ ] Mark generator with `returns_generator = True` attribute

#### Required Class Methods:
- [ ] `_calculate_differences(new_structure, previous_structure)` - Theory differences
- [ ] `_create_difference_constraint(previous_models)` - Difference constraints
- [ ] `_create_non_isomorphic_constraint(z3_model)` - Optional isomorphism prevention
- [ ] `_create_stronger_constraint(isomorphic_model)` - Optional stronger constraints

#### Testing Requirements:
- [ ] Basic iteration test (at least 2 models)
- [ ] Difference calculation test
- [ ] Constraint generation test
- [ ] Error handling test
- [ ] Generator interface test

#### Documentation Requirements:
- [ ] Theory-specific difference explanation
- [ ] Constraint generation strategy
- [ ] Performance characteristics
- [ ] Known limitations

---

This standards document provides comprehensive guidelines for implementing robust, maintainable, and efficient model iterators. Following these standards ensures consistency across all theory implementations and enables reliable constraint preservation and model differentiation.