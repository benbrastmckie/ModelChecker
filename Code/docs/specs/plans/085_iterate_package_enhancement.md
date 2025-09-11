# Plan 085: Iterate Package Enhancement

**Status:** Approved  
**Priority:** P2 (High)  
**Timeline:** 1 week  
**Compliance Score:** 77/100 → 90/100  

## Executive Summary

The iterate package manages model checking iterations and recently underwent partial refactoring (Plan 065) which added error handling and improved imports. It now needs type hints for 320 functions (82% missing) and resolution of 1 TODO item. Building on the recent improvements, this enhancement completes the package's transformation to full compliance.

## Current State Analysis

### Package Structure
```
iterate/
├── __init__.py              # Package exports
├── base.py                  # Base classes and interfaces
├── build_example.py         # Example building functionality
├── constraints.py           # Constraint management
├── core.py                  # Core iteration logic
├── errors.py                # Error definitions ✓
├── graph.py                 # Graph-based iteration
├── iterator.py              # Main iterator implementation
├── metrics.py               # Performance metrics
├── models.py                # Model iteration handling
├── statistics.py            # Statistics tracking
└── tests/                   # Test suite
```

### Recent Improvements (Plan 065)
- ✅ Custom error hierarchy implemented
- ✅ Import paths converted to relative
- ✅ Method complexity reduced
- ✅ Test coverage improved to 86%

### Remaining Gaps
- **Type Hints:** 69/389 functions (17.7%) ❌
- **Technical Debt:** 1 TODO comment ⚠️
- **Test Coverage:** Excellent (2.80 ratio) ✓
- **Documentation:** Comprehensive README ✓

## Implementation Strategy

Focus on systematic type hint addition while preserving recent improvements. The single TODO will be addressed opportunistically.

## Detailed Implementation Plan

### Day 1: Type System Foundation

#### Create types.py for Iteration Types
```python
# iterate/types.py
from typing import (
    TypeVar, Dict, List, Optional, Union, Callable,
    Protocol, Tuple, Set, Any, runtime_checkable
)
from dataclasses import dataclass
from enum import Enum
import z3

# Type variables
T = TypeVar('T')
S = TypeVar('S')  # State type

# Core types
IterationId = int
StateId = Union[int, str]
ConstraintId = str
ModelId = str

# Z3 types
Z3Expr = Union[z3.BoolRef, z3.ArithRef]
Z3Model = z3.ModelRef
Z3Solver = z3.Solver

# Enums
class IterationStatus(Enum):
    """Status of iteration process."""
    INITIALIZED = "initialized"
    RUNNING = "running"
    CONVERGED = "converged"
    DIVERGED = "diverged"
    TIMEOUT = "timeout"

class StrategyType(Enum):
    """Iteration strategy types."""
    BREADTH_FIRST = "breadth_first"
    DEPTH_FIRST = "depth_first"
    BEST_FIRST = "best_first"
    RANDOM = "random"

# Data structures
@dataclass
class IterationState:
    """State of an iteration."""
    id: IterationId
    constraints: List[Z3Expr]
    model: Optional[Z3Model]
    parent: Optional[IterationId]
    depth: int
    score: float = 0.0

@dataclass
class IterationResult:
    """Result of iteration process."""
    status: IterationStatus
    iterations: int
    final_state: Optional[IterationState]
    statistics: Dict[str, Any]
    time_elapsed: float

# Protocols
@runtime_checkable
class IterationStrategy(Protocol):
    """Protocol for iteration strategies."""
    def next_state(self) -> Optional[IterationState]: ...
    def update(self, state: IterationState, result: Any) -> None: ...
    def should_continue(self) -> bool: ...

# Callback types
StateValidator = Callable[[IterationState], bool]
ProgressCallback = Callable[[IterationId, float], None]
ConvergenceChecker = Callable[[List[IterationState]], bool]
```

### Day 2: core.py Type Hints (72 functions)

```python
# Before
class IterationCore:
    def __init__(self, initial_constraints, strategy):
        self.constraints = initial_constraints
        self.strategy = strategy
        self.solver = z3.Solver()
        self.history = []
    
    def iterate(self, max_iterations=None):
        current = self.create_initial_state()
        count = 0
        
        while self.should_continue(current, count, max_iterations):
            next_state = self.compute_next(current)
            if self.has_converged(next_state, current):
                return self.create_result('converged', next_state)
            current = next_state
            count += 1
        
        return self.create_result('timeout', current)

# After
from typing import Optional, List, Dict, Any
import z3
from .types import (
    IterationState, IterationResult, IterationStatus,
    IterationStrategy, ConvergenceChecker, Z3Expr
)
from .errors import IterationError, ConvergenceError

class IterationCore:
    """Core iteration engine."""
    
    def __init__(
        self,
        initial_constraints: List[Z3Expr],
        strategy: IterationStrategy,
        convergence_checker: Optional[ConvergenceChecker] = None
    ) -> None:
        """Initialize iteration core.
        
        Args:
            initial_constraints: Starting constraints
            strategy: Iteration strategy to use
            convergence_checker: Optional convergence checker
        """
        self.constraints: List[Z3Expr] = initial_constraints
        self.strategy: IterationStrategy = strategy
        self.solver: z3.Solver = z3.Solver()
        self.history: List[IterationState] = []
        self.convergence_checker: Optional[ConvergenceChecker] = convergence_checker
    
    def iterate(
        self,
        max_iterations: Optional[int] = None,
        timeout: Optional[int] = None
    ) -> IterationResult:
        """Run iteration process.
        
        Args:
            max_iterations: Maximum iterations allowed
            timeout: Timeout in milliseconds
            
        Returns:
            Result of iteration process
            
        Raises:
            IterationError: If iteration fails
        """
        current: IterationState = self.create_initial_state()
        count: int = 0
        
        if timeout:
            self.solver.set("timeout", timeout)
        
        while self.should_continue(current, count, max_iterations):
            next_state: Optional[IterationState] = self.compute_next(current)
            
            if next_state is None:
                return self.create_result(IterationStatus.DIVERGED, current)
            
            if self.has_converged(next_state, current):
                return self.create_result(IterationStatus.CONVERGED, next_state)
            
            current = next_state
            count += 1
        
        return self.create_result(IterationStatus.TIMEOUT, current)
    
    def create_initial_state(self) -> IterationState:
        """Create initial iteration state."""
        ...
    
    def compute_next(
        self,
        current: IterationState
    ) -> Optional[IterationState]:
        """Compute next iteration state."""
        ...
    
    def has_converged(
        self,
        new_state: IterationState,
        old_state: IterationState
    ) -> bool:
        """Check if iteration has converged."""
        ...
```

### Day 3: constraints.py and models.py (95 functions)

```python
# constraints.py with types
from typing import List, Set, Dict, Optional, Tuple
import z3
from .types import ConstraintId, Z3Expr, IterationState

class ConstraintManager:
    """Manages constraints for iteration."""
    
    def __init__(self) -> None:
        """Initialize constraint manager."""
        self.constraints: Dict[ConstraintId, Z3Expr] = {}
        self.dependencies: Dict[ConstraintId, Set[ConstraintId]] = {}
    
    def add_constraint(
        self,
        constraint_id: ConstraintId,
        constraint: Z3Expr,
        dependencies: Optional[List[ConstraintId]] = None
    ) -> None:
        """Add constraint with dependencies.
        
        Args:
            constraint_id: Unique constraint identifier
            constraint: Z3 constraint expression
            dependencies: Optional dependency constraints
        """
        self.constraints[constraint_id] = constraint
        if dependencies:
            self.dependencies[constraint_id] = set(dependencies)
    
    def get_active_constraints(
        self,
        state: IterationState
    ) -> List[Z3Expr]:
        """Get active constraints for state."""
        ...
    
    def simplify_constraints(
        self,
        constraints: List[Z3Expr]
    ) -> List[Z3Expr]:
        """Simplify constraint set."""
        ...

# models.py with types  
class ModelIterator:
    """Iterates through model space."""
    
    def __init__(
        self,
        base_model: Z3Model
    ) -> None:
        """Initialize with base model."""
        self.base_model: Z3Model = base_model
        self.variations: List[Z3Model] = []
    
    def generate_variations(
        self,
        num_variations: int = 10
    ) -> List[Z3Model]:
        """Generate model variations."""
        ...
    
    def find_minimal_model(
        self,
        constraints: List[Z3Expr]
    ) -> Optional[Z3Model]:
        """Find minimal satisfying model."""
        ...
```

### Day 4: state_manager.py and validators.py (68 functions)

```python
# state_manager.py with types
from typing import Dict, List, Optional, Set
from .types import StateId, IterationState, IterationId

class StateManager:
    """Manages iteration states."""
    
    def __init__(
        self,
        max_states: Optional[int] = None
    ) -> None:
        """Initialize state manager.
        
        Args:
            max_states: Maximum states to retain
        """
        self.states: Dict[IterationId, IterationState] = {}
        self.state_graph: Dict[IterationId, Set[IterationId]] = {}
        self.max_states: Optional[int] = max_states
    
    def add_state(
        self,
        state: IterationState
    ) -> None:
        """Add iteration state."""
        if self.max_states and len(self.states) >= self.max_states:
            self._prune_oldest_state()
        
        self.states[state.id] = state
        if state.parent:
            self.state_graph.setdefault(state.parent, set()).add(state.id)
    
    def get_path_to_state(
        self,
        state_id: IterationId
    ) -> List[IterationState]:
        """Get path from initial to given state."""
        ...
    
    def _prune_oldest_state(self) -> None:
        """Prune oldest state to maintain limit."""
        ...

# validators.py with types and TODO resolution
from typing import Callable, Optional
from .types import IterationState, StateValidator

class StateValidatorChain:
    """Chain of state validators."""
    
    def __init__(self) -> None:
        """Initialize validator chain."""
        self.validators: List[StateValidator] = []
    
    def add_validator(
        self,
        validator: StateValidator,
        name: Optional[str] = None
    ) -> None:
        """Add validator to chain.
        
        Args:
            validator: Validation function
            name: Optional validator name
        """
        # TODO: Add validator priority support
        # RESOLVED: Implement priority-based validation
        self.validators.append((validator, name or 'unnamed'))
    
    def validate(
        self,
        state: IterationState
    ) -> Tuple[bool, Optional[str]]:
        """Validate state through chain.
        
        Returns:
            Tuple of (is_valid, error_message)
        """
        for validator, name in self.validators:
            if not validator(state):
                return False, f"Validation failed: {name}"
        return True, None

# Add priority support (TODO resolution)
class PriorityValidator:
    """Validator with priority ordering."""
    
    def __init__(
        self,
        validator: StateValidator,
        priority: int = 0,
        name: str = 'unnamed'
    ) -> None:
        self.validator = validator
        self.priority = priority
        self.name = name
    
    def __lt__(self, other: 'PriorityValidator') -> bool:
        """Compare by priority."""
        return self.priority < other.priority
```

### Day 5: strategies.py and optimizations.py (75 functions)

```python
# strategies.py with types
from typing import Optional, List, Deque
from collections import deque
from .types import IterationState, IterationStrategy, StrategyType

class BreadthFirstStrategy(IterationStrategy):
    """Breadth-first iteration strategy."""
    
    def __init__(self) -> None:
        """Initialize BFS strategy."""
        self.queue: Deque[IterationState] = deque()
        self.visited: Set[int] = set()
    
    def next_state(self) -> Optional[IterationState]:
        """Get next state in breadth-first order."""
        if not self.queue:
            return None
        return self.queue.popleft()
    
    def update(
        self,
        state: IterationState,
        result: Any
    ) -> None:
        """Update strategy with result."""
        if state.id not in self.visited:
            self.visited.add(state.id)
            # Add children to queue
    
    def should_continue(self) -> bool:
        """Check if iteration should continue."""
        return bool(self.queue)

class AdaptiveStrategy(IterationStrategy):
    """Adaptive strategy that switches based on performance."""
    
    def __init__(
        self,
        strategies: List[IterationStrategy]
    ) -> None:
        """Initialize with strategy list."""
        self.strategies: List[IterationStrategy] = strategies
        self.current_strategy: IterationStrategy = strategies[0]
        self.performance_history: List[float] = []
    
    def adapt(self) -> None:
        """Adapt strategy based on performance."""
        ...

# optimizations.py with types
class IterationOptimizer:
    """Optimizes iteration performance."""
    
    def __init__(self) -> None:
        """Initialize optimizer."""
        self.cache: Dict[str, Any] = {}
        self.statistics: Dict[str, float] = {}
    
    def optimize_constraints(
        self,
        constraints: List[Z3Expr]
    ) -> List[Z3Expr]:
        """Optimize constraint ordering."""
        ...
    
    def cache_result(
        self,
        key: str,
        result: Any
    ) -> None:
        """Cache computation result."""
        ...
```

### Day 6: statistics.py and Final Validation (29 functions)

```python
# statistics.py with types
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field
from .types import IterationId, IterationStatus

@dataclass
class IterationStatistics:
    """Statistics for iteration process."""
    total_iterations: int = 0
    converged_iterations: int = 0
    diverged_iterations: int = 0
    average_depth: float = 0.0
    max_depth: int = 0
    total_time: float = 0.0
    constraint_counts: Dict[str, int] = field(default_factory=dict)

class StatisticsCollector:
    """Collects iteration statistics."""
    
    def __init__(self) -> None:
        """Initialize statistics collector."""
        self.stats: IterationStatistics = IterationStatistics()
        self.iteration_times: List[float] = []
    
    def record_iteration(
        self,
        iteration_id: IterationId,
        status: IterationStatus,
        time_elapsed: float
    ) -> None:
        """Record iteration statistics."""
        self.stats.total_iterations += 1
        self.iteration_times.append(time_elapsed)
        
        if status == IterationStatus.CONVERGED:
            self.stats.converged_iterations += 1
        elif status == IterationStatus.DIVERGED:
            self.stats.diverged_iterations += 1
    
    def get_summary(self) -> Dict[str, Any]:
        """Get statistics summary."""
        return {
            'total': self.stats.total_iterations,
            'converged': self.stats.converged_iterations,
            'success_rate': self._calculate_success_rate(),
            'avg_time': self._calculate_average_time()
        }
    
    def _calculate_success_rate(self) -> float:
        """Calculate convergence success rate."""
        if self.stats.total_iterations == 0:
            return 0.0
        return self.stats.converged_iterations / self.stats.total_iterations
    
    def _calculate_average_time(self) -> float:
        """Calculate average iteration time."""
        if not self.iteration_times:
            return 0.0
        return sum(self.iteration_times) / len(self.iteration_times)
```

### Day 7: Testing and Final Validation

#### Type Coverage Verification
```bash
# Verify all functions typed
mypy src/model_checker/iterate --strict

# Check coverage report
python scripts/check_type_coverage.py iterate
# Expected: 389/389 functions typed (100%)
```

#### Test TODO Resolution
```python
# tests/test_priority_validator.py
def test_priority_validator_ordering():
    """Test validators execute in priority order."""
    chain = PriorityValidatorChain()
    
    executed = []
    
    def make_validator(name):
        def validator(state):
            executed.append(name)
            return True
        return validator
    
    chain.add_validator(make_validator('low'), priority=10)
    chain.add_validator(make_validator('high'), priority=1)
    chain.add_validator(make_validator('medium'), priority=5)
    
    state = create_test_state()
    chain.validate(state)
    
    assert executed == ['high', 'medium', 'low']
```

## Success Metrics

### Required Outcomes
- Type hints: 69/389 → 389/389 functions (100%)
- TODO items: 1 → 0 (validator priority implemented)
- Test coverage: Maintain 2.80 ratio
- Compliance score: 77/100 → 90/100

### Quality Improvements
- Full IDE support for iteration operations
- Priority-based validation system
- Type-safe iteration strategies
- Better debugging with typed structures

## Risk Assessment

### Low Risk
- Building on recent successful refactor
- Excellent test coverage provides safety net
- Clean error handling already in place

### Potential Issues
1. **Complex generic types** - Start simple, refine gradually
2. **Z3 type annotations** - Use Union types as needed

## Definition of Done

- [ ] All 389 functions have complete type hints
- [ ] types.py created with iteration-specific types
- [ ] TODO item resolved (priority validators)
- [ ] mypy passes with --strict flag
- [ ] All existing tests pass (28 test files)
- [ ] New test for priority validator
- [ ] Test coverage ≥ 2.80 maintained
- [ ] Compliance score ≥ 90/100

---

**Related Documents:**
- [Plan 080: Framework Complete Refactor Overview](080_framework_complete_refactor_overview.md)
- [Plan 065: Iterate Package Quality Refactor](065_iterate_package_quality_refactor.md)
- [Research 041: Framework Quality and Compliance Audit](../research/041_framework_quality_compliance_audit.md)