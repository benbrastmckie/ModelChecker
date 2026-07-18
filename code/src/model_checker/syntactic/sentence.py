"""
Sentence representation for logical formulas.

This module provides the Sentence class, which represents logical formulas
and handles their transformation between infix and prefix notation. It stores
all metadata needed for evaluation including operator linkages, semantic
bindings, and proposition values.
"""

from typing import List, Optional, Dict, Any, Union, Tuple, TYPE_CHECKING

from model_checker.utils import parse_expression
from .atoms import get_atom_sort
from .types import FormulaString, PrefixList
from .errors import InvalidFormulaError, ParseError
from .formulas import is_syntactically_wff

if TYPE_CHECKING:
    from .collection import OperatorCollection
    from model_checker.z3_shim import ExprRef


class Sentence:
    """Represents a logical sentence with support for both infix and prefix notation.
    
    This class provides the foundation for representing logical formulas in the model checker.
    It handles conversion between infix notation (human-readable) and prefix notation 
    (machine-processable), and stores all metadata needed for evaluation.
    
    The lifecycle of a Sentence instance involves multiple update phases:
    1. Creation: Stores infix and converts to prefix notation
    2. Type Update: In Syntax.initialize_sentences(), links to operator classes
    3. Object Update: In ModelConstraints, links to semantic operators
    4. Proposition Update: In ModelStructure, builds proposition for evaluation
    
    Attributes:
        name (str): The original infix representation of the sentence
        prefix_sentence (list): The sentence in prefix notation
        complexity (int): The nesting depth of the sentence
        original_arguments (list): Sentence objects for subexpressions
        original_operator (str/obj): The main operator (initially a string)
        arguments (list): Updated sentence objects (after type update)
        operator (obj): Semantic operator object (after object update)
        sentence_letter (obj): For atomic sentences, their Z3 representation
        proposition (obj): The proposition representing this sentence (after proposition update)
    """

    def __init__(self, infix_sentence: FormulaString, _internal: bool = False) -> None:
        """Initialize sentence from infix notation.

        Args:
            infix_sentence: Formula in infix notation
            _internal: If True, skip WFF validation (for internal subformula construction)

        Raises:
            InvalidFormulaError: If formula is empty or invalid
            ParseError: If formula cannot be parsed (unless _internal=True)
        """
        if not infix_sentence:
            raise InvalidFormulaError(
                "Formula cannot be empty",
                formula="",
                context={'suggestion': 'Provide a non-empty formula'}
            )

        # Store internal flag for subformula creation
        self._internal = _internal

        # store input, prefix string, complexity, and sentences for arguments
        self.name = infix_sentence
        self.prefix_sentence, self.complexity = self.prefix(infix_sentence)

        # Validate well-formedness: check WFF grammar and closedness
        # Skip validation for internal subformula construction (e.g., lambda bodies)
        if not _internal:
            self._validate_well_formedness()

        # recursive clause: initially stores infix_arguments and infix_operator
        # updated by initialize_sentences in Syntax with operator_collection
        # updated by instantiate in ModelConstraints with semantics
        if self.complexity > 0:
            first_op = self.prefix_sentence[0]
            self.original_arguments = [  # store infix_arguments
                self.infix(arg)
                for arg in self.prefix_sentence[1:]
            ]
            # updated by update_types:
            self.original_operator = first_op
        else:
            self.original_arguments = None
            # Handle atomic cases: \top, \bot, and atomic sentences
            first_elem = self.prefix_sentence[0]
            if isinstance(first_elem, str) and first_elem in {'\\top', '\\bot'}:
                self.original_operator = first_elem
            else:
                self.original_operator = None
        self.arguments = None # updated by initialize_types
        self.operator = None # updated by update_types

        # update_types via initialize_sentences in Syntax: operator_collection
        self.sentence_letter = None

        # update_proposition via interpret in ModelStructure: z3_model
        self.proposition = None

    def __str__(self) -> str:
        return self.name
    
    def __repr__(self) -> str:
        return self.name

    def _validate_well_formedness(self) -> None:
        """Validate that the parsed formula is well-formed.

        Raises:
            ParseError: If the input is not a well-formed formula.
        """
        is_wff, error_msg = is_syntactically_wff(self.prefix_sentence)
        if not is_wff:
            raise ParseError(
                f"Invalid sentence '{self.name}': {error_msg}",
                formula=self.name,
                position=0
            )

    def prefix(self, infix_sentence: FormulaString) -> Tuple[PrefixList, int]:
        """Converts infix notation to prefix notation.

        Transforms a logical expression from infix format (e.g., "(p ∧ q)") to prefix format
        (e.g., ["∧", "p", "q"]) for easier processing by the model checker. This conversion
        works without prior knowledge of specific operators in the language.

        Args:
            infix_sentence (str): A logical expression in infix notation

        Returns:
            tuple: A pair containing:
                - list: The expression in prefix notation
                - int: The complexity (nesting depth) of the expression
        """
        tokens = infix_sentence.replace("(", " ( ").replace(")", " ) ").split()
        derived_object, complexity = parse_expression(tokens)
        return derived_object, complexity

    def infix(self, prefix: PrefixList) -> FormulaString:
        """Converts prefix notation to infix notation.

        Transforms a logical expression from prefix format (e.g., ["∧", "p", "q"]) to infix
        format (e.g., "(p ∧ q)"), handling various input types including sentence objects,
        Z3 expressions, strings, and nested lists.

        Args:
            prefix: The expression in prefix notation, which can be:
                - A Sentence object (with a 'name' attribute)
                - A Z3 ExprRef object
                - A string (already in infix form)
                - A list/tuple (in prefix order: [operator, arg1, arg2, ...])

        Returns:
            str: The expression converted to infix notation

        Raises:
            TypeError: If the input has an unsupported type
        """
        if hasattr(prefix, 'name'):
            return prefix.name
        if isinstance(prefix, str):
            return prefix
        if isinstance(prefix, (list, tuple)):
            if len(prefix) == 1:
                return self.infix(prefix[0])
            operator = prefix[0]
            op_str = self.infix(operator)

            if len(prefix) == 2:
                return f"{op_str} {self.infix(prefix[1])}"
            left_expr, right_expr = prefix[1], prefix[2]
            return f"({self.infix(left_expr)} {op_str} {self.infix(right_expr)})"
        # Handle solver expressions (z3.ExprRef, cvc5 expressions)
        # Check after list/tuple to avoid matching Python lists (which also have .sort())
        if hasattr(prefix, 'sort') and callable(getattr(prefix, 'sort', None)):
            return str(prefix)
        raise TypeError(f"The prefix {prefix} has a type error in infix().")

    def update_types(self, operator_collection: 'OperatorCollection') -> None:
        """Updates the sentence with proper operator types from the operator collection.
        
        This method uses the operator_collection to replace the string representation
        of operators in the prefix_sentence with actual operator class objects, and
        to replace sentence letters with Z3 AtomSort objects. For defined operators,
        it also handles the derivation of the types based on their definitions.
        
        The method updates the following attributes:
        - original_operator: The main operator class (if not an atomic sentence)
        - operator: The derived operator class after handling defined operators
        - arguments: The arguments to the operator (after type updates)
        - sentence_letter: For atomic sentences, their Z3 representation
        
        Args:
            operator_collection (OperatorCollection): Collection of available operators
        """

        def primitive_operator(original_type):
            """Checks if the main operator is primitive."""
            return getattr(original_type[0], "primitive", True)

        def derive_type(original_type):
            """This function translates a original_type possibly with defined
            operators to a derived_type without defined operators."""
            if primitive_operator(original_type):
                return original_type
            operator, args = original_type[0], original_type[1:]
            if not hasattr(operator, "primitive"):
                raise TypeError(f"Operator {operator} is not a subclass of Operator.")
            if isinstance(operator, type):
                derivation =  operator('a').derived_definition(*args)
            else:
                raise TypeError(
                    f"The operator {operator} is of type {type(operator)} " +
                    f"which is not an operator class."
                )
            return derive_type(derivation)

        def store_types(derived_type):
            # Detection logic:
            # - Sentence letters: Z3 Const objects (from atomic parsing)
            # - Extremal operators: \top, \bot
            # - Complex sentences: operator + arguments

            from model_checker.solver.expressions import is_const

            first_elem = derived_type[0]

            # Check for sentence letter (Z3 Const from apply_operator)
            if len(derived_type) == 1 and is_const(first_elem):
                return None, None, first_elem

            # Check for extremal operator
            if self.name in {'\\top', '\\bot'}:
                return first_elem, None, None

            # Complex sentence with operator and arguments
            if len(derived_type) > 1:
                operator_type, argument_types = first_elem, derived_type[1:]
                infix_arguments = [self.infix(arg_type) for arg_type in argument_types]
                return operator_type, infix_arguments, None

            raise ValueError(f"the derived_type for {self} is invalid in store_types().")

        original_type = operator_collection.apply_operator(self.prefix_sentence)
        if self.original_operator:
            self.original_operator = original_type[0]
        derived_type = derive_type(original_type)
        self.operator, self.arguments, self.sentence_letter = store_types(derived_type)
    
    def update_objects(self, model_constraints: Any) -> None:
        """Links the sentence to concrete operator instances with semantics.
        
        Given an instance of ModelConstraints, this method updates the operator
        references from operator classes to actual operator instances initialized
        with the specific semantics implementation from model_constraints.
        
        This step is crucial for connecting the syntactic representation to the
        semantic evaluation framework, allowing operators to access the semantic
        methods needed for truth/falsity evaluation.
        
        Args:
            model_constraints (ModelConstraints): The model constraints object containing
                the semantics implementation to use for operator instantiation
        """

        def activate_operator(some_type):
            if some_type is None: # operator is None if sentence_letter
                return None
            op_dict = model_constraints.operators
            # # NOTE: required for update operator_collection strategy
            # op_dict = model_constraints.operator_collection.operator_dictionary
            return op_dict[some_type.name]

        self.original_operator = activate_operator(self.original_operator)
        self.operator = activate_operator(self.operator)

    def update_proposition(self, model_structure: Any) -> None:
        """Builds a proposition object for the sentence given the model_structure."""
        self.proposition = model_structure.proposition_class(self, model_structure)

    @classmethod
    def from_prefix(cls, prefix_list: 'PrefixList') -> 'Sentence':
        """Create a Sentence directly from a prefix list, bypassing the infix parser.

        This classmethod provides a programmatic construction path for Sentence
        objects when the formula is already in prefix-list format (e.g., from
        json_to_prefix()). It avoids the parse-then-validate round-trip of
        __init__ and is suitable for formulas that may not have a unique canonical
        infix representation parseable by the default parser.

        The returned Sentence has its core attributes set:
        - prefix_sentence: the input prefix_list
        - name: an infix string derived from prefix_list (via Sentence.infix)
        - complexity: nesting depth computed from prefix_list structure
        - original_operator: the operator symbol string (or None for atoms)
        - original_arguments: list of infix-string arguments (or None for atoms)
        - arguments, operator, sentence_letter, proposition: all None (set later
          by update_types, update_objects, update_proposition as in __init__)

        Args:
            prefix_list: A prefix list in ModelChecker format, e.g.
                ["p"], ["\\neg", ["p"]], ["\\wedge", ["p"], ["q"]]

        Returns:
            A new Sentence instance with attributes set from prefix_list.

        Example:
            sentence = Sentence.from_prefix(["\\neg", ["p"]])
            # sentence.name == "\\neg p"
            # sentence.prefix_sentence == ["\\neg", ["p"]]
            # sentence.complexity == 1
            # sentence.original_operator == "\\neg"
        """
        # Create a sentinel instance that bypasses __init__ entirely
        # by using object.__new__ to avoid any parsing or validation
        instance = object.__new__(cls)

        # Set the prefix list directly
        instance.prefix_sentence = prefix_list

        # Compute the infix name using Sentence.infix (which is an instance method
        # but only depends on the input, not on `self` state)
        instance.name = _compute_infix_from_prefix(prefix_list)

        # Compute complexity: nesting depth of the prefix list
        instance.complexity = _compute_prefix_complexity(prefix_list)

        # Set internal flag (no WFF validation was done)
        instance._internal = True

        # Set original_operator and original_arguments
        if len(prefix_list) == 1:
            # Atom or nullary operator
            first_elem = prefix_list[0]
            instance.original_arguments = None
            # Check for nullary operators like \\bot, \\top
            if isinstance(first_elem, str) and first_elem in {'\\top', '\\bot'}:
                instance.original_operator = first_elem
            else:
                instance.original_operator = None
        else:
            # Operator + arguments
            instance.original_operator = prefix_list[0]
            # Store arguments as infix strings (matching __init__ behavior)
            instance.original_arguments = [
                _compute_infix_from_prefix(arg)
                for arg in prefix_list[1:]
            ]

        # Initialize lifecycle-updated attributes to None
        instance.arguments = None
        instance.operator = None
        instance.sentence_letter = None
        instance.proposition = None

        return instance


def _compute_infix_from_prefix(prefix_list) -> str:
    """Compute infix string from prefix list without creating a Sentence.

    This standalone helper mirrors Sentence.infix() for the common cases
    used in from_prefix (string atoms, nullary, unary, binary operators).

    Args:
        prefix_list: A prefix list (list of str/list, no Term objects).

    Returns:
        Infix string representation.
    """
    if not isinstance(prefix_list, list):
        return str(prefix_list)

    if len(prefix_list) == 1:
        return str(prefix_list[0])

    head = prefix_list[0]
    op_str = str(head)

    if len(prefix_list) == 2:
        arg_str = _compute_infix_from_prefix(prefix_list[1])
        return f"{op_str} {arg_str}"

    if len(prefix_list) == 3:
        left_str = _compute_infix_from_prefix(prefix_list[1])
        right_str = _compute_infix_from_prefix(prefix_list[2])
        return f"({left_str} {op_str} {right_str})"

    # Higher arity: fall back to space-separated
    args_str = " ".join(_compute_infix_from_prefix(a) for a in prefix_list[1:])
    return f"{op_str} {args_str}"


def _compute_prefix_complexity(prefix_list) -> int:
    """Compute nesting depth (complexity) of a prefix list.

    Matches the complexity values that Sentence.__init__ produces via
    parse_expression:
    - Atoms / nullary: 0
    - Operator + arguments: 1 + max(complexity of each argument sublist)

    Args:
        prefix_list: A prefix list.

    Returns:
        Non-negative integer complexity.
    """
    if not isinstance(prefix_list, list) or len(prefix_list) <= 1:
        return 0
    sub_complexities = [
        _compute_prefix_complexity(arg)
        for arg in prefix_list[1:]
        if isinstance(arg, list)
    ]
    return 1 + (max(sub_complexities) if sub_complexities else 0)