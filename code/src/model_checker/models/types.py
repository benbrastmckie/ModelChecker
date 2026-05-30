"""
Type definitions for the models package.

This module provides type aliases and protocol definitions used throughout
the models package to ensure type safety and clear interfaces.
"""

from typing import (
    TypeVar, Union, Dict, List, Any, Protocol, Optional,
    Tuple, Set, Callable, TYPE_CHECKING
)

if TYPE_CHECKING:
    from model_checker import z3_shim as z3
    from .proposition import PropositionDefaults
    from .semantic import Semantics
    from model_checker.syntactic import Syntax, Sentence
    from model_checker.solver.types import SolverExpr, SolverModel

# Type variables for generic functions
T = TypeVar('T')

# Solver type aliases (use Any at runtime, specific types for TYPE_CHECKING)
if TYPE_CHECKING:
    Z3Expr = Union[z3.BoolRef, z3.ArithRef, z3.BitVecRef]
    Z3Model = z3.ModelRef
    Z3Solver = z3.Solver
    Z3Status = z3.CheckSatResult
else:
    # At runtime, use Any to support both z3 and cvc5 backends
    Z3Expr = Any
    Z3Model = Any
    Z3Solver = Any
    Z3Status = Any

# Model checking types
Settings = Dict[str, Any]
OperatorDict = Dict[str, Any]
SentenceDict = Dict[str, 'Sentence']
EvaluationPoint = Dict[str, Any]

# Constraint types
if TYPE_CHECKING:
    ConstraintList = List[z3.BoolRef]
    ConstraintGenerator = Callable[[], z3.BoolRef]
else:
    ConstraintList = List[Any]
    ConstraintGenerator = Callable[[], Any]

# Semantic structure types (uses Any to support both backends)
WorldState = Union[int, Any]
StateSpace = List[WorldState]
RelationSet = Set[Tuple[WorldState, WorldState]]

# Protocol for proposition interface
class IProposition(Protocol):
    """Protocol defining the interface for proposition implementations."""
    
    def truth_value_at(self, eval_point: EvaluationPoint) -> bool:
        """Get truth value at evaluation point."""
        ...
    
    def print_proposition(
        self, 
        eval_point: EvaluationPoint, 
        indent: int, 
        use_colors: bool
    ) -> None:
        """Print proposition evaluation."""
        ...