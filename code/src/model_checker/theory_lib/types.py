"""
Type system foundation for theory library.

Follows ARCHITECTURE.md protocol-based interfaces and
CODE_STANDARDS.md type annotation requirements.
"""
from typing import (
    TypeVar, Dict, List, Optional, Union, Any,
    Protocol, Callable, Tuple, Set, runtime_checkable, TYPE_CHECKING
)
from abc import ABC, abstractmethod

if TYPE_CHECKING:
    from model_checker import z3_shim as z3

# Local framework imports (commented out - not currently used)
# from model_checker.defaults import SemanticDefaults

# Type variables with clear bounds
T = TypeVar('T')
P = TypeVar('P', bound='Proposition')
M = TypeVar('M', bound='ModelStructure')

# Core types with descriptive aliases
TheoryName = str
OperatorName = str
PropositionName = str
StateId = Union[int, str]
WorldId = Union[int, str]

# Solver types (backend-agnostic at runtime)
if TYPE_CHECKING:
    Z3Expr = Union[z3.BoolRef, z3.ArithRef]
    Z3Model = z3.ModelRef
    Z3Solver = z3.Solver
else:
    Z3Expr = Any
    Z3Model = Any
    Z3Solver = Any

# Configuration types
TheoryConfig = Dict[str, Any]
OperatorRegistry = Dict[OperatorName, 'Operator']

# Protocol interfaces following ARCHITECTURE.md patterns


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

# Theory-specific protocol definitions
@runtime_checkable
class WitnessSemantics(Protocol):
    """Protocol for witness-based semantic implementations (Exclusion theory)."""
    def has_witness_for(self, formula: str, state: StateId) -> bool:
        """Check if state has witness for formula."""
        ...

    def get_witness_predicates(self) -> Dict[str, Any]:
        """Get witness predicate functions."""
        ...


@runtime_checkable
class WitnessRegistry(Protocol):
    """Protocol for witness predicate management."""
    def register_witness_predicates(self, formula_str: str) -> Tuple[Any, Any]:
        """Register witness predicates for formula."""
        ...

    def get_all_predicates(self) -> Dict[str, Any]:
        """Get all registered predicates."""
        ...

    def clear(self) -> None:
        """Clear all registered predicates."""
        ...


@runtime_checkable
class ModelIterator(Protocol):
    """Protocol for model iteration implementations."""
    def __iter__(self) -> 'ModelIterator':
        """Iterator protocol."""
        ...

    def __next__(self) -> ModelStructure:
        """Get next distinct model."""
        ...

    def _calculate_differences(self, new_structure: ModelStructure, previous_structure: ModelStructure) -> Dict[str, Any]:
        """Calculate differences between models."""
        ...


# Enhanced type aliases for better clarity
ExampleDict = Dict[str, Tuple[List[str], List[str], Dict[str, Any]]]  # premises, conclusions, settings
OperatorDict = Dict[str, type]
TheoryDict = Dict[str, Union[type, OperatorDict]]