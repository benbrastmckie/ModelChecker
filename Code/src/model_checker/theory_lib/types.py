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

# Local framework imports (commented out - not currently used)
# from model_checker.defaults import SemanticDefaults

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
    def register_witness_predicates(self, formula_str: str) -> Tuple[z3.FuncDeclRef, z3.FuncDeclRef]:
        """Register witness predicates for formula."""
        ...

    def get_all_predicates(self) -> Dict[str, z3.FuncDeclRef]:
        """Get all registered predicates."""
        ...

    def clear(self) -> None:
        """Clear all registered predicates."""
        ...


@runtime_checkable
class ImpositionSemantics(Protocol):
    """Protocol for imposition-based semantic implementations."""
    def calculate_outcome_worlds(self, verifiers: Set[StateId], eval_point: Dict[str, Any], model_structure: 'ModelStructure') -> Set[StateId]:
        """Calculate outcome worlds for imposition operation."""
        ...

    def alt_imposition(self, state_y: StateId, state_w: StateId, state_u: StateId) -> bool:
        """Check alternative imposition relation."""
        ...


@runtime_checkable
class SubtheoryProtocol(Protocol):
    """Protocol for logos subtheory implementations."""
    def get_operators(self) -> Dict[str, type]:
        """Get subtheory operator classes."""
        ...

    def get_examples(self) -> Dict[str, Any]:
        """Get subtheory example definitions."""
        ...

    def validate_config(self, config: Dict[str, Any]) -> bool:
        """Validate subtheory configuration."""
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