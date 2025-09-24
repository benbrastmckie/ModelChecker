"""
Type system foundation for theory library.

Follows ARCHITECTURE.md protocol-based interfaces and
CODE_STANDARDS.md type annotation requirements.
"""
from typing import (
    TypeVar, Dict, List, Optional, Union, Any,
    Protocol, Callable, Tuple, Set, runtime_checkable
)
from abc import ABC, abstractmethod

import z3

# Local framework imports (per import standards)
from model_checker.defaults import SemanticDefaults

# Type variables with clear bounds
T = TypeVar('T')
S = TypeVar('S', bound='Semantics')
P = TypeVar('P', bound='Proposition')
M = TypeVar('M', bound='ModelStructure')

# Core types with descriptive aliases
TheoryName = str
OperatorName = str
PropositionName = str
StateId = Union[int, str]
WorldId = Union[int, str]

# Z3 types for solver integration
Z3Expr = Union[z3.BoolRef, z3.ArithRef]
Z3Model = z3.ModelRef
Z3Solver = z3.Solver

# Configuration types
TheoryConfig = Dict[str, Any]
OperatorRegistry = Dict[OperatorName, 'Operator']

# Protocol interfaces following ARCHITECTURE.md patterns
@runtime_checkable
class Semantics(Protocol):
    """
    Protocol for semantic implementations.

    Follows protocol-based interface pattern from ARCHITECTURE.md.
    """
    def evaluate(self, formula: str, model: Any) -> bool:
        """Evaluate formula in model."""
        ...

    def generate_constraints(self) -> List[Z3Expr]:
        """Generate Z3 constraints."""
        ...


@runtime_checkable
class Proposition(Protocol):
    """Protocol for proposition implementations."""
    name: str

    def to_z3(self) -> Z3Expr:
        """Convert to Z3 expression."""
        ...


@runtime_checkable
class ModelStructure(Protocol):
    """Protocol for model structures."""
    def get_states(self) -> List[StateId]:
        """Get all states in model."""
        ...

    def get_relations(self) -> Dict[str, Any]:
        """Get relational structure."""
        ...


@runtime_checkable
class Operator(Protocol):
    """Protocol for operators with clear interface."""
    name: str
    arity: int

    def apply(self, *args: Any) -> Any:
        """Apply operator to arguments."""
        ...


# Callback types for dependency injection
FormulaValidator = Callable[[str], bool]
ModelValidator = Callable[[Any], bool]
ConstraintGenerator = Callable[[], List[Z3Expr]]