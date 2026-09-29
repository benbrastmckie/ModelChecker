"""
Operator collection management for the ModelChecker framework.

This module provides the OperatorCollection class which serves as a registry
for all logical operators available in the model checking system.
"""

from typing import Dict, List, Optional, Iterator, Type, Union, Any

from model_checker.solver.expressions import Const
from .atoms import get_atom_sort
from .types import OperatorName, PrefixList
from .errors import DuplicateOperatorError, UnknownOperatorError


class OperatorCollection:
    """A registry for all logical operators available in the model checking system.
    
    This class acts as a container for operator classes (both primitive and defined),
    organizing them by name for easy lookup and application. It provides methods for
    adding operators to the collection and applying them to expressions.
    
    The collection is used by the Syntax class to convert string representations
    of operators into their corresponding operator classes during sentence parsing.
    
    Attributes:
        operator_dictionary (dict): Maps operator names to their corresponding classes.
            An operator class declaring `aliases` is registered under multiple keys (its
            canonical `name` plus each alias), so several dictionary keys may map to the
            same class object; `__iter__`/`items()` yield one entry per key, not per
            class, and `__getitem__` resolves any of those keys to the same class.
    """

    def __init__(self, *input: Any) -> None:
        self.operator_dictionary = {}
        if input:
            self.add_operator(input)

    def __iter__(self) -> Iterator[OperatorName]:
        yield from self.operator_dictionary

    def __getitem__(self, value: OperatorName) -> Type['Operator']:
        try:
            return self.operator_dictionary[value]
        except KeyError:
            raise UnknownOperatorError(
                value, available_operators=sorted(self.operator_dictionary)
            ) from None
    
    def items(self) -> Iterator[tuple]:
        yield from self.operator_dictionary.items()

    def add_operator(self, operator: Union[Type['Operator'], List, tuple, 'OperatorCollection']) -> None:
        """Adds one or more operator classes to the operator collection.

        This method accepts either a single operator class or multiple operator classes
        in a container (list, tuple, or set) and adds them to the operator dictionary.
        It also handles adding operators from another OperatorCollection instance.

        For each operator added, its name is used as the key in the operator dictionary,
        and it is additionally registered under every string in its (optional) `aliases`
        class attribute -- typically a user-facing Unicode spelling such as "∧" alongside
        the canonical LaTeX `name` "\\wedge". The `aliases` list is only ever read, never
        mutated, so a subclass that declares no `aliases` of its own safely shares the
        empty-list default on the base `Operator` class without risk of leaking another
        subclass's aliases.

        Duplicate handling is conflict-aware, not a blanket skip/raise: re-registering
        the SAME class under a key (name or alias) it already owns is a silent no-op --
        required for idempotent re-registration via `OperatorCollection` merging and via
        `builder/serialize.py::deserialize_operators`, which calls `add_operator` once per
        serialized dictionary key, i.e. once per name/alias of the same class. Registering
        a DIFFERENT class under an already-taken name or alias raises
        `DuplicateOperatorError` naming both the key and the existing class.

        Args:
            operator: Can be one of:
                - A single operator class (type)
                - A list/tuple/set of operator classes
                - An OperatorCollection instance

        Raises:
            TypeError: If the input is not an operator class, collection of operator
                      classes, or OperatorCollection instance
            ValueError: If an operator class doesn't have a name defined
            DuplicateOperatorError: If a different class already owns the name or one of
                      the aliases being registered

        Examples:
            collection.add_operator(AndOperator)  # Add single operator
            collection.add_operator([AndOperator, OrOperator])  # Add multiple operators
            collection.add_operator(other_collection)  # Merge collections

            class AndOperator(Operator):
                name = "\\wedge"
                arity = 2
                aliases = ["∧"]

            collection.add_operator(AndOperator)
            collection["\\wedge"] is collection["∧"] is AndOperator  # True
        """
        if isinstance(operator, OperatorCollection):
            for op_name, op_class in operator.items():
                self.add_operator(op_class)
        elif isinstance(operator, (list, tuple, set)):
            for operator_class in operator:
                self.add_operator(operator_class)
        elif isinstance(operator, type):
            if getattr(operator, "name", None) is None:
                raise ValueError(f"Operator class {operator.__name__} has no name defined.")

            aliases = getattr(operator, "aliases", []) or []
            for key in (operator.name, *aliases):
                self._register_key(key, operator)
        else:
            raise TypeError(f"Unexpected input type {type(operator)} for add_operator.")

    def _register_key(self, key: OperatorName, operator: Type['Operator']) -> None:
        """Register a single name/alias key for `operator`, applying the
        conflict-aware duplicate policy documented on `add_operator`: a re-registration
        of the SAME class already owning `key` is a silent no-op; a DIFFERENT class
        claiming `key` raises `DuplicateOperatorError`.
        """
        existing = self.operator_dictionary.get(key)
        if existing is None:
            self.operator_dictionary[key] = operator
        elif existing is not operator:
            raise DuplicateOperatorError(key, existing.__name__)

    def apply_operator(self, prefix_sentence: PrefixList) -> Any:
        """Converts a prefix notation sentence into a list of operator classes and atomic terms.

        This method processes a sentence in prefix notation, converting operator strings to their
        corresponding operator classes from the collection and handling atomic sentences and
        extremal operators (\\top, \\bot). It recursively processes all subexpressions.

        Args:
            prefix_sentence (list): A sentence in prefix notation where operators and atoms
                                     are represented as strings

        Returns:
            list: A nested list structure where:
                - String operators are replaced with their operator classes
                - String atomic sentences are converted to Z3 Const objects
                - Extremal operators (\\top, \\bot) are converted to their operator classes

        Raises:
            ValueError: If an atomic term is not a valid sentence letter
            TypeError: If an operator is not provided as a string
            UnknownOperatorError: If an operator token is not registered in this
                collection under its `name` or any declared `aliases`

        Examples:
            ["∧", ["p"], ["q"]] -> [AndOperator, Const("p", AtomSort), Const("q", AtomSort)]
            ["\\top"] -> [TopOperator]
            ["p"] -> [Const("p", AtomSort)]
        """
        if len(prefix_sentence) == 1:
            atom = prefix_sentence[0]

            # Handle extremal operators
            if isinstance(atom, str) and atom in {"\\top", "\\bot"}:
                return [self[atom]]

            # Handle string atoms as sentence letters
            if isinstance(atom, str) and atom.isalnum():
                return [Const(atom, get_atom_sort())]

            raise ValueError(f"The atom {atom} is invalid in apply_operator.")

        op, arguments = prefix_sentence[0], prefix_sentence[1:]

        activated = [self.apply_operator(arg) for arg in arguments]
        if isinstance(op, str):
            activated.insert(0, self[op])
        else:
            raise TypeError(f"Expected operator name as a string, got {type(op).__name__}.")
        return activated