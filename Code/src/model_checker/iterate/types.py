"""Type definitions for the iterate package.

This module provides comprehensive type definitions for iteration operations,
including type aliases, protocols, and data structures used throughout the
iterate package.
"""

from typing import (
    TYPE_CHECKING, Any, Callable, Dict, List, Optional, Set, Tuple, Union,
    Protocol, TypeVar, FrozenSet, Sequence
)
from enum import Enum

if TYPE_CHECKING:
    import z3
    from z3 import BoolRef, ArithRef, ModelRef, Solver

# Type variables
T = TypeVar('T')
S = TypeVar('S')  # State type
M = TypeVar('M')  # Model type

# Core type aliases
IterationId = int
StateId = Union[int, str]
ConstraintId = str
ModelId = str
FormulaString = str
OperatorName = str

# Z3 type aliases
Z3Expr = Union['BoolRef', 'ArithRef']
Z3Model = 'ModelRef'
Z3Solver = 'Solver'
Z3Constraint = 'BoolRef'

# Collection types
ConstraintSet = List[Z3Expr]
StateSet = Set[StateId]
ModelMap = Dict[ModelId, Z3Model]
FormulaList = List[FormulaString]
SettingsDict = Dict[str, Any]

# Enumerations
class IterationStatus(Enum):
    """Status of iteration process."""
    INITIALIZED = "initialized"
    RUNNING = "running"
    CONVERGED = "converged"
    DIVERGED = "diverged"
    TIMEOUT = "timeout"
    ERROR = "error"

class StrategyType(Enum):
    """Iteration strategy types."""
    BREADTH_FIRST = "breadth_first"
    DEPTH_FIRST = "depth_first"
    BEST_FIRST = "best_first"
    RANDOM = "random"
    ADAPTIVE = "adaptive"

class ConstraintType(Enum):
    """Types of constraints."""
    HARD = "hard"
    SOFT = "soft"
    OPTIMIZATION = "optimization"

# Data structures
class IterationState:
    """State of an iteration."""
    
    def __init__(
        self,
        id: IterationId,
        constraints: ConstraintSet,
        model: Optional[Z3Model] = None,
        parent: Optional[IterationId] = None,
        depth: int = 0,
        score: float = 0.0
    ) -> None:
        """Initialize iteration state.
        
        Args:
            id: Unique iteration identifier
            constraints: Active constraints
            model: Optional Z3 model
            parent: Parent iteration ID
            depth: Depth in iteration tree
            score: Quality score for state
        """
        self.id = id
        self.constraints = constraints
        self.model = model
        self.parent = parent
        self.depth = depth
        self.score = score

class IterationResult:
    """Result of iteration process."""
    
    def __init__(
        self,
        status: IterationStatus,
        iterations: int,
        final_state: Optional[IterationState] = None,
        statistics: Optional[Dict[str, Any]] = None,
        time_elapsed: float = 0.0,
        error: Optional[str] = None
    ) -> None:
        """Initialize iteration result.
        
        Args:
            status: Final iteration status
            iterations: Number of iterations performed
            final_state: Final iteration state
            statistics: Iteration statistics
            time_elapsed: Total time taken
            error: Error message if failed
        """
        self.status = status
        self.iterations = iterations
        self.final_state = final_state
        self.statistics = statistics or {}
        self.time_elapsed = time_elapsed
        self.error = error

class ConstraintInfo:
    """Information about a constraint."""
    
    def __init__(
        self,
        id: ConstraintId,
        constraint: Z3Expr,
        type: ConstraintType = ConstraintType.HARD,
        dependencies: Optional[Set[ConstraintId]] = None,
        priority: int = 0
    ) -> None:
        """Initialize constraint info.
        
        Args:
            id: Unique constraint identifier
            constraint: Z3 constraint expression
            type: Constraint type
            dependencies: Dependent constraint IDs
            priority: Constraint priority (lower = higher priority)
        """
        self.id = id
        self.constraint = constraint
        self.type = type
        self.dependencies = dependencies or set()
        self.priority = priority

# Protocol definitions
class IterationStrategy(Protocol):
    """Protocol for iteration strategies."""
    
    def next_state(self) -> Optional[IterationState]:
        """Get next state to explore.
        
        Returns:
            Next state or None if exhausted
        """
        ...
    
    def update(self, state: IterationState, result: Any) -> None:
        """Update strategy with result.
        
        Args:
            state: Current state
            result: Result of processing state
        """
        ...
    
    def should_continue(self) -> bool:
        """Check if iteration should continue.
        
        Returns:
            True if should continue
        """
        ...

class StateValidator(Protocol):
    """Protocol for state validators."""
    
    def validate(self, state: IterationState) -> Tuple[bool, Optional[str]]:
        """Validate iteration state.
        
        Args:
            state: State to validate
            
        Returns:
            Tuple of (is_valid, error_message)
        """
        ...

class ConvergenceChecker(Protocol):
    """Protocol for convergence checkers."""
    
    def has_converged(
        self,
        current: IterationState,
        history: List[IterationState]
    ) -> bool:
        """Check if iteration has converged.
        
        Args:
            current: Current iteration state
            history: Previous states
            
        Returns:
            True if converged
        """
        ...

class ModelEvaluator(Protocol):
    """Protocol for model evaluators."""
    
    def evaluate(
        self,
        model: Z3Model,
        formula: FormulaString
    ) -> bool:
        """Evaluate formula in model.
        
        Args:
            model: Z3 model
            formula: Formula to evaluate
            
        Returns:
            Evaluation result
        """
        ...

# Callback types
ProgressCallback = Callable[[IterationId, float], None]
StateTransformer = Callable[[IterationState], IterationState]
ConstraintGenerator = Callable[[IterationState], ConstraintSet]
ScoreFunction = Callable[[IterationState], float]

# Result types
ValidationResult = Tuple[bool, Optional[str]]
ConvergenceResult = Tuple[bool, str]
OptimizationResult = Tuple[Optional[Z3Model], float]

# Configuration types
class IterationConfig:
    """Configuration for iteration process."""
    
    def __init__(
        self,
        max_iterations: Optional[int] = None,
        timeout: Optional[int] = None,
        strategy: StrategyType = StrategyType.BREADTH_FIRST,
        convergence_threshold: float = 0.001,
        enable_caching: bool = True,
        parallel: bool = False
    ) -> None:
        """Initialize iteration configuration.
        
        Args:
            max_iterations: Maximum iterations allowed
            timeout: Timeout in milliseconds
            strategy: Iteration strategy type
            convergence_threshold: Convergence threshold
            enable_caching: Enable result caching
            parallel: Enable parallel processing
        """
        self.max_iterations = max_iterations
        self.timeout = timeout
        self.strategy = strategy
        self.convergence_threshold = convergence_threshold
        self.enable_caching = enable_caching
        self.parallel = parallel

# Graph types
NodeId = Union[int, str]
EdgeWeight = float
GraphPath = List[NodeId]
AdjacencyList = Dict[NodeId, Set[NodeId]]

# Metric types
MetricValue = Union[int, float]
MetricsDict = Dict[str, MetricValue]
TimeSeries = List[Tuple[float, MetricValue]]

# Build types
BuildConfig = Dict[str, Any]
BuildResult = Union[Tuple[bool, Any], Tuple[bool, Any, str]]
ExampleDict = Dict[str, Any]