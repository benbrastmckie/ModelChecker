"""
Protocol definitions for the Logos theory subtheory system.

This module defines the standardized interfaces that all subtheories must implement
to ensure proper integration with the main Logos theory framework.
"""

from typing import Protocol, Dict, Type, Any, Set, Optional, Union, TypeVar, Generic
from typing_extensions import runtime_checkable
import z3

from model_checker.syntactic import Operator, Sentence


# Type variables for generic type hints
TOperator = TypeVar('TOperator', bound=Operator)
TSemantics = TypeVar('TSemantics')
TModelStructure = TypeVar('TModelStructure')

# Evaluation point type for semantic operations
EvaluationPoint = Dict[str, Union[z3.BitVecRef, int]]

# State type for hyperintensional semantics
StateType = Union[z3.BitVecRef, int]

# Z3 constraint type
Z3Constraint = z3.BoolRef

# Settings dictionary type
SettingsDict = Dict[str, Any]


@runtime_checkable
class SubtheoryProtocol(Protocol):
    """
    Standard interface for all Logos subtheories.

    Every subtheory must implement these methods to be properly integrated
    into the Logos theory framework.
    """

    def get_operators(self) -> Dict[str, Type[TOperator]]:
        """
        Get all operators provided by this subtheory.

        Returns:
            Dictionary mapping operator names to their classes
        """
        ...

    def get_examples(self) -> Dict[str, Any]:
        """
        Get example formulas and tests for this subtheory.

        Returns:
            Dictionary containing example categories (countermodels, theorems, etc.)
        """
        ...

    def validate_config(self, config: SettingsDict) -> bool:
        """
        Validate configuration settings for this subtheory.

        Args:
            config: Dictionary of configuration settings

        Returns:
            True if configuration is valid, False otherwise
        """
        ...


@runtime_checkable
class OperatorProtocol(Protocol):
    """
    Protocol for all Logos theory operators.

    Defines the interface that all operators must implement for
    hyperintensional truthmaker semantics.
    """

    def true_at(self, *arguments: Sentence, eval_point: EvaluationPoint) -> Z3Constraint:
        """
        Determine if the operator's formula is true at an evaluation point.

        Args:
            *arguments: The sentences that are arguments to this operator
            eval_point: The evaluation point (typically containing 'world' key)

        Returns:
            Z3 constraint expressing the truth condition
        """
        ...

    def false_at(self, *arguments: Sentence, eval_point: EvaluationPoint) -> Z3Constraint:
        """
        Determine if the operator's formula is false at an evaluation point.

        Args:
            *arguments: The sentences that are arguments to this operator
            eval_point: The evaluation point (typically containing 'world' key)

        Returns:
            Z3 constraint expressing the falsity condition
        """
        ...

    def extended_verify(self, state: StateType, *arguments: Sentence,
                       eval_point: EvaluationPoint) -> Z3Constraint:
        """
        Determine if a state verifies the operator's formula.

        Args:
            state: The state being tested as a verifier
            *arguments: The sentences that are arguments to this operator
            eval_point: The evaluation point context

        Returns:
            Z3 constraint expressing the verification condition
        """
        ...

    def extended_falsify(self, state: StateType, *arguments: Sentence,
                        eval_point: EvaluationPoint) -> Z3Constraint:
        """
        Determine if a state falsifies the operator's formula.

        Args:
            state: The state being tested as a falsifier
            *arguments: The sentences that are arguments to this operator
            eval_point: The evaluation point context

        Returns:
            Z3 constraint expressing the falsification condition
        """
        ...

    def find_verifiers_and_falsifiers(self, *arguments: Sentence,
                                     eval_point: EvaluationPoint) -> tuple[Set[StateType], Set[StateType]]:
        """
        Find all states that verify or falsify the operator's formula.

        Args:
            *arguments: The sentences that are arguments to this operator
            eval_point: The evaluation point context

        Returns:
            Tuple of (verifiers, falsifiers) sets
        """
        ...


@runtime_checkable
class SemanticsProtocol(Protocol):
    """
    Protocol for Logos theory semantics classes.

    Defines the core semantic interface for hyperintensional truthmaker
    semantics with support for modular operator loading.
    """

    # Z3 function signatures
    verify: z3.FuncDeclRef
    falsify: z3.FuncDeclRef
    possible: z3.FuncDeclRef

    # Frame constraints
    frame_constraints: list[Z3Constraint]

    # Main evaluation point
    main_world: z3.BitVecRef
    main_point: EvaluationPoint

    def load_subtheories(self, subtheories: Optional[list[str]] = None) -> list[Any]:
        """
        Load specified subtheories into the semantics.

        Args:
            subtheories: List of subtheory names to load, defaults to standard set

        Returns:
            List of loaded subtheory modules
        """
        ...

    def true_at(self, sentence: Sentence, eval_point: EvaluationPoint) -> Z3Constraint:
        """
        Determine if a sentence is true at an evaluation point.

        Args:
            sentence: The sentence to evaluate
            eval_point: The evaluation point

        Returns:
            Z3 constraint expressing the truth condition
        """
        ...

    def false_at(self, sentence: Sentence, eval_point: EvaluationPoint) -> Z3Constraint:
        """
        Determine if a sentence is false at an evaluation point.

        Args:
            sentence: The sentence to evaluate
            eval_point: The evaluation point

        Returns:
            Z3 constraint expressing the falsity condition
        """
        ...

    def extended_verify(self, state: StateType, sentence: Sentence,
                       eval_point: EvaluationPoint) -> Z3Constraint:
        """
        Determine if a state verifies a sentence.

        Args:
            state: The state being tested
            sentence: The sentence to check
            eval_point: The evaluation point context

        Returns:
            Z3 constraint expressing verification
        """
        ...

    def extended_falsify(self, state: StateType, sentence: Sentence,
                        eval_point: EvaluationPoint) -> Z3Constraint:
        """
        Determine if a state falsifies a sentence.

        Args:
            state: The state being tested
            sentence: The sentence to check
            eval_point: The evaluation point context

        Returns:
            Z3 constraint expressing falsification
        """
        ...

    def is_world(self, state: StateType) -> Z3Constraint:
        """
        Determine if a state represents a possible world.

        Args:
            state: The state to check

        Returns:
            Z3 constraint expressing world condition
        """
        ...

    def compatible(self, state_x: StateType, state_y: StateType) -> Z3Constraint:
        """
        Determine if two states are compatible (can be fused).

        Args:
            state_x: First state
            state_y: Second state

        Returns:
            Z3 constraint expressing compatibility
        """
        ...


@runtime_checkable
class RegistryProtocol(Protocol):
    """
    Protocol for the operator registry system.

    Manages loading and coordination of subtheories and their operators.
    """

    def load_subtheory(self, name: str) -> Any:
        """
        Load a specific subtheory by name.

        Args:
            name: Name of the subtheory to load

        Returns:
            The loaded subtheory module

        Raises:
            ValueError: If subtheory cannot be loaded
        """
        ...

    def load_subtheories(self, names: list[str]) -> list[Any]:
        """
        Load multiple subtheories.

        Args:
            names: List of subtheory names to load

        Returns:
            List of loaded subtheory modules
        """
        ...

    def get_operators(self) -> Any:
        """
        Get the operator collection with all loaded operators.

        Returns:
            OperatorCollection containing all loaded operators
        """
        ...

    def get_loaded_subtheories(self) -> list[str]:
        """
        Get list of currently loaded subtheory names.

        Returns:
            List of loaded subtheory names
        """
        ...

    def validate_operator_compatibility(self) -> list[str]:
        """
        Validate compatibility of all loaded operators.

        Returns:
            List of compatibility issues (empty if no issues)
        """
        ...


@runtime_checkable
class PropositionProtocol(Protocol):
    """
    Protocol for Logos theory propositions.

    Defines the interface for propositions in hyperintensional semantics
    with verifier and falsifier sets.
    """

    # Core attributes
    verifiers: Set[StateType]
    falsifiers: Set[StateType]
    sentence: Sentence
    eval_world: StateType

    def find_proposition(self) -> tuple[Set[StateType], Set[StateType]]:
        """
        Compute the verifier and falsifier sets for this proposition.

        Returns:
            Tuple of (verifiers, falsifiers) sets
        """
        ...

    def truth_value_at(self, eval_world: StateType) -> bool:
        """
        Determine the truth value of the proposition at a given world.

        Args:
            eval_world: The world at which to evaluate

        Returns:
            True if the proposition is true at the world, False otherwise
        """
        ...

    def proposition_constraints(self, sentence_letter: Any) -> list[Z3Constraint]:
        """
        Generate Z3 constraints for atomic propositions.

        Args:
            sentence_letter: The atomic sentence letter

        Returns:
            List of Z3 constraints governing the proposition
        """
        ...


@runtime_checkable
class ModelIteratorProtocol(Protocol[TModelStructure]):
    """
    Protocol for model iterators in the Logos theory.

    Defines the interface for finding multiple non-isomorphic models
    with theory-specific difference detection.
    """

    def iterate(self) -> list[TModelStructure]:
        """
        Find multiple non-isomorphic models.

        Returns:
            List of distinct model structures
        """
        ...

    def iterate_generator(self) -> TModelStructure:
        """
        Generator interface for finding models incrementally.

        Yields:
            Each distinct model as it's discovered
        """
        ...


# Convenience type aliases for common patterns
SubtheoryModule = Any  # Runtime module type
OperatorClass = Type[TOperator]
OperatorDict = Dict[str, OperatorClass]
ExampleDict = Dict[str, Any]

# Union types for flexible interfaces
StateOrInt = Union[StateType, int]
ConstraintList = list[Z3Constraint]