"""
Operator collection management for the ModelChecker framework.

This module provides the OperatorCollection class which serves as a registry
for all logical operators available in the model checking system.
"""

from z3 import Const

from .atoms import AtomSort


class OperatorCollection:
    """A registry for all logical operators available in the model checking system.
    
    This class acts as a container for operator classes (both primitive and defined),
    organizing them by name for easy lookup and application. It provides methods for
    adding operators to the collection and applying them to expressions.
    
    The collection is used by the Syntax class to convert string representations
    of operators into their corresponding operator classes during sentence parsing.
    
    Attributes:
        operator_dictionary (dict): Maps operator names to their corresponding classes
    """

    def __init__(self, *input):
        self.operator_dictionary = {}
        if input:
            self.add_operator(input)

    def __iter__(self):
        yield from self.operator_dictionary

    def __getitem__(self, value):
        return self.operator_dictionary[value]
    
    def items(self):
        yield from self.operator_dictionary.items()

    def add_operator(self, operator):
        """Adds one or more operator classes to the operator collection.

        This method accepts either a single operator class or multiple operator classes
        in a container (list, tuple, or set) and adds them to the operator dictionary.
        It also handles adding operators from another OperatorCollection instance.

        For each operator added, its name is used as the key in the operator dictionary.
        If an operator with the same name already exists, it is skipped.

        Args:
            operator: Can be one of:
                - A single operator class (type)
                - A list/tuple/set of operator classes
                - An OperatorCollection instance

        Raises:
            TypeError: If the input is not an operator class, collection of operator
                      classes, or OperatorCollection instance
            ValueError: If an operator class doesn't have a name defined

        Examples:
            collection.add_operator(AndOperator)  # Add single operator
            collection.add_operator([AndOperator, OrOperator])  # Add multiple operators
            collection.add_operator(other_collection)  # Merge collections
        """
        if isinstance(operator, OperatorCollection):
            for op_name, op_class in operator.items():
                self.add_operator(op_class)
        elif isinstance(operator, (list, tuple, set)):
            for operator_class in operator:
                self.add_operator(operator_class)
        elif isinstance(operator, type):
            if operator.name in self.operator_dictionary.keys():
                return
            if getattr(operator, "name", None) is None:
                raise ValueError(f"Operator class {operator.__name__} has no name defined.")
            self.operator_dictionary[operator.name] = operator
        else:
            raise TypeError(f"Unexpected input type {type(operator)} for add_operator.")

    def apply_operator(self, prefix_sentence):
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
                - Atomic sentences are converted to Z3 Const objects
                - Extremal operators (\\top, \\bot) are converted to their operator classes

        Raises:
            ValueError: If an atomic term is neither a valid sentence letter nor an extremal operator
            TypeError: If an operator is not provided as a string

        Examples:
            ["∧", "p", "q"] -> [AndOperator, Const("p", AtomSort), Const("q", AtomSort)]
            ["\\top"] -> [TopOperator]
            ["p"] -> [Const("p", AtomSort)]
        """
        if len(prefix_sentence) == 1:
            atom = prefix_sentence[0]
            if atom in {"\\top", "\\bot"}:  # Handle extremal operators
                return [self[atom]]
            if atom.isalnum():  # Handle atomic sentences
                return [Const(atom, AtomSort)]
            raise ValueError(f"The atom {atom} is invalid in apply_operator.")
        op, arguments = prefix_sentence[0], prefix_sentence[1:]
        activated = [self.apply_operator(arg) for arg in arguments]
        if isinstance(op, str):
            activated.insert(0, self[op])
        else:
            raise TypeError(f"Expected operator name as a string, got {type(op).__name__}.")
        return activated