"""
Type definitions for the models package.

This module provides type aliases and protocol definitions used throughout
the models package to ensure type safety and clear interfaces.
"""

from typing import (
    TypeVar, Union, Dict, List, Any, Protocol, Optional, 
    Tuple, Set, Callable, TYPE_CHECKING
)
import z3

if TYPE_CHECKING:
    from .proposition import PropositionDefaults
    from .semantic import Semantics
    from model_checker.syntactic import Syntax, Sentence

# Type variables for generic functions
T = TypeVar('T')

# Z3 type aliases
Z3Expr = Union[z3.BoolRef, z3.ArithRef, z3.BitVecRef]
Z3Model = z3.ModelRef
Z3Solver = z3.Solver
Z3Status = z3.CheckSatResult

# Model checking types
Settings = Dict[str, Any]
OperatorDict = Dict[str, Any]
SentenceDict = Dict[str, 'Sentence']
EvaluationPoint = Dict[str, Any]

# Constraint types  
ConstraintList = List[z3.BoolRef]
ConstraintGenerator = Callable[[], z3.BoolRef]

# Semantic structure types
WorldState = Union[int, z3.BitVecRef, Any]
StateSpace = List[WorldState]
RelationSet = Set[Tuple[WorldState, WorldState]]

# Protocol for semantics interface
class ISemantics(Protocol):
    """Protocol defining the interface for semantic implementations."""
    
    def generate_constraints(self) -> ConstraintList:
        """Generate Z3 constraints for the semantics."""
        ...
    
    def true_at(self, world: WorldState, sentence: Any) -> z3.BoolRef:
        """Check if sentence is true at world."""
        ...
    
    def false_at(self, world: WorldState, sentence: Any) -> z3.BoolRef:
        """Check if sentence is false at world."""
        ...

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