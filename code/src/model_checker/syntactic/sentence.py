"""
Sentence representation for logical formulas.

This module provides the Sentence class, which represents logical formulas
and handles their transformation between infix and prefix notation. It stores
all metadata needed for evaluation including operator linkages, semantic
bindings, and proposition values.
"""

from typing import List, Optional, Dict, Any, Union, Tuple, TYPE_CHECKING

from model_checker.utils import parse_expression, tokenize_first_order, parse_first_order_expression
from .atoms import get_atom_sort
from .types import FormulaString, PrefixList
from .errors import InvalidFormulaError, ParseError
from .terms import Term, Variable
from .formulas import compute_formula_free_variables, is_syntactically_wff

if TYPE_CHECKING:
    from .collection import OperatorCollection
    from z3 import ExprRef


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
            # Handle first-order operators differently
            first_op = self.prefix_sentence[0]
            if first_op in {"\\lambda", "\\forall", "\\exists", "\\lambdaApp"}:
                # For binders, arguments after the variable are the body
                # Store in a way that's compatible with the original system
                self.original_arguments = [
                    self.infix(arg)
                    for arg in self.prefix_sentence[1:]
                    if not isinstance(arg, Variable)  # Skip the bound variable
                ]
            else:
                self.original_arguments = [  # store infix_arguments
                    self.infix(arg)
                    for arg in self.prefix_sentence[1:]
                ]
            # updated by update_types:
            self.original_operator = first_op
        else:
            self.original_arguments = None
            # Handle atomic cases: \top, \bot, variables, and atomic predicates
            first_elem = self.prefix_sentence[0]
            if isinstance(first_elem, str) and first_elem in {'\\top', '\\bot'}:
                self.original_operator = first_elem
            elif isinstance(first_elem, Variable):
                # Variable as atomic sentence
                self.original_operator = None
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

        Performs two-level validation per the Logos Theory manual:
        1. Syntactic category check: Is this a formula (not a bare term or lambda)?
        2. Closedness check: Does the formula have free variables?

        A sentence is a closed well-formed formula (WFF). Open formulas with
        free variables are valid WFFs but not valid sentences.

        Raises:
            ParseError: If the input is not a WFF (e.g., bare term or lambda)
            ParseError: If the formula has free variables (open formula)
        """
        # Level 1: Check syntactic well-formedness
        is_wff, error_msg = is_syntactically_wff(self.prefix_sentence)
        if not is_wff:
            raise ParseError(
                f"Invalid sentence '{self.name}': {error_msg}",
                formula=self.name,
                position=0
            )

        # Level 2: Check closedness (no free variables)
        free_vars = compute_formula_free_variables(self.prefix_sentence)
        if free_vars:
            var_names = sorted(str(v) for v in free_vars)
            var_list = ", ".join(var_names)
            raise ParseError(
                f"Invalid sentence '{self.name}': formula has free variable(s): {var_list}. "
                f"Sentences must be closed formulas. Consider quantifying: "
                f"'\\forall {var_names[0]}. {self.name}'",
                formula=self.name,
                position=0
            )

    def prefix(self, infix_sentence: FormulaString) -> Tuple[PrefixList, int]:
        """Converts infix notation to prefix notation.

        Transforms a logical expression from infix format (e.g., "(p ∧ q)") to prefix format
        (e.g., ["∧", "p", "q"]) for easier processing by the model checker. This conversion
        works without prior knowledge of specific operators in the language.

        Supports both propositional and first-order syntax:
        - Variables: v_x, v_1, v_foo_bar
        - Predicates: F[t1, t2, ...]
        - Functions: f<t1, t2, ...>
        - Lambda: \\lambda v.phi
        - Quantifiers: \\forall v.phi, \\exists v.phi

        Args:
            infix_sentence (str): A logical expression in infix notation

        Returns:
            tuple: A pair containing:
                - list: The expression in prefix notation
                - int: The complexity (nesting depth) of the expression
        """
        # Check if the sentence contains first-order syntax markers
        # Use first-order parser if we detect: v_ prefix, [ ], < >, or binding operators
        first_order_markers = ['v_', '[', '<', '\\lambda', '\\forall', '\\exists']
        uses_first_order = any(marker in infix_sentence for marker in first_order_markers)

        if uses_first_order:
            # Use first-order tokenizer and parser
            tokens = tokenize_first_order(infix_sentence)
            derived_object, complexity = parse_first_order_expression(tokens)
            return derived_object, complexity
        else:
            # Use original propositional parser for backward compatibility
            tokens = infix_sentence.replace("(", " ( ").replace(")", " ) ").split()
            derived_object, complexity = parse_expression(tokens)
            return derived_object, complexity

    def infix(self, prefix: PrefixList) -> FormulaString:
        """Converts prefix notation to infix notation.

        Transforms a logical expression from prefix format (e.g., ["∧", "p", "q"]) to infix
        format (e.g., "(p ∧ q)"), handling various input types including sentence objects,
        Z3 expressions, strings, Term objects, and nested lists.

        Args:
            prefix: The expression in prefix notation, which can be:
                - A Sentence object (with a 'name' attribute)
                - A Z3 ExprRef object
                - A string (already in infix form)
                - A Term object (Variable, Constant, FunctionApplication)
                - A list/tuple (in prefix order: [operator, arg1, arg2, ...])

        Returns:
            str: The expression converted to infix notation

        Raises:
            TypeError: If the input has an unsupported type
        """
        # Handle Term objects (Variable, Constant, FunctionApplication)
        if isinstance(prefix, Term):
            return str(prefix)

        if hasattr(prefix, 'name') and not isinstance(prefix, Term):
            return prefix.name
        if hasattr(prefix, 'sort') and callable(getattr(prefix, 'sort', None)):
            # This handles both z3.ExprRef and cvc5 expressions
            return str(prefix)
        if isinstance(prefix, str):
            return prefix
        if isinstance(prefix, (list, tuple)):
            if len(prefix) == 1:
                return self.infix(prefix[0])
            operator = prefix[0]
            op_str = self.infix(operator)

            # Handle lambda abstraction: ["\\lambda", variable, body]
            if op_str == "\\lambda":
                var = self.infix(prefix[1])
                body = self.infix(prefix[2])
                return f"{op_str} {var}. {body}"

            # Handle Church-style quantifiers: ["\\forall", lambda_term]
            # where lambda_term = ["\\lambda", variable, body]
            # After apply_operator, lambda_term may be [LambdaOperator, [variable], body]
            if op_str in {"\\forall", "\\exists"}:
                lambda_term = prefix[1]
                if isinstance(lambda_term, list) and len(lambda_term) >= 3:
                    # Check if it's a lambda term (either string "\\lambda" or LambdaOperator class)
                    lambda_head = lambda_term[0]
                    is_lambda = (
                        lambda_head == "\\lambda" or
                        (hasattr(lambda_head, 'name') and lambda_head.name == "\\lambda")
                    )
                    if is_lambda:
                        # Get variable - may be in list after apply_operator
                        var_elem = lambda_term[1]
                        if isinstance(var_elem, list) and len(var_elem) == 1:
                            var_elem = var_elem[0]
                        var = self.infix(var_elem)
                        body = self.infix(lambda_term[2])
                        return f"{op_str} {var}. {body}"
                # Fallback: print as is
                return f"{op_str}({self.infix(lambda_term)})"

            # Handle lambda application
            if op_str == "\\lambdaApp":
                var = self.infix(prefix[1])
                body = self.infix(prefix[2])
                arg = self.infix(prefix[3])
                return f"(\\lambda {var}. {body})({arg})"

            # Handle predicates with term arguments
            if len(prefix) > 1 and isinstance(prefix[1], Term):
                args = ", ".join(self.infix(arg) for arg in prefix[1:])
                return f"{op_str}[{args}]"

            if len(prefix) == 2:
                return f"{op_str} {self.infix(prefix[1])}"
            left_expr, right_expr = prefix[1], prefix[2]
            return f"({self.infix(left_expr)} {op_str} {self.infix(right_expr)})"
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
            # Task 14: Detection logic updated for new convention
            # - Sentence letters: Z3 Const objects (from P[] syntax)
            # - Constants: Term objects (from bare or explicit <> syntax)
            # - Extremal operators: \top, \bot
            # - Complex sentences: operator + arguments

            from z3 import is_const
            from .terms import Term

            first_elem = derived_type[0]

            # Check for sentence letter (Z3 Const from apply_operator)
            if len(derived_type) == 1 and is_const(first_elem):
                return None, None, first_elem

            # Check for constant (Term object from parser)
            if len(derived_type) == 1 and isinstance(first_elem, Term):
                # Constants don't have sentence_letter representation
                # They'll be handled in semantic evaluation
                return None, None, None

            # Check for extremal operator
            if self.name in {'\\top', '\\bot'}:
                return first_elem, None, None

            # Check for predicate with term arguments: [name, Term1, Term2, ...]
            # Predicates have a string name and all arguments are Term objects
            # They should NOT have an operator - semantic evaluation handles them
            if (len(derived_type) > 1 and
                isinstance(first_elem, str) and
                all(isinstance(arg, Term) for arg in derived_type[1:])):
                # Predicate application: store as None operator with no sentence_letter
                # The predicate info is in prefix_sentence for semantic evaluation
                return None, None, None

            # Complex sentence with operator and arguments
            if len(derived_type) > 1:
                operator_type, argument_types = first_elem, derived_type[1:]

                # Task 21: For lambda operators, preserve Variable as Term
                # Lambda structure after apply_operator: [LambdaOperator, [Variable], [body]]
                # The variable may be wrapped in a singleton list, unwrap it
                if hasattr(operator_type, 'name') and operator_type.name == "\\lambda":
                    processed_args = []
                    for arg_type in argument_types:
                        # Check for singleton list containing a Term
                        if (isinstance(arg_type, list) and len(arg_type) == 1 and
                            isinstance(arg_type[0], Term)):
                            # Unwrap and keep the Term object
                            processed_args.append(arg_type[0])
                        elif isinstance(arg_type, Term):
                            # Keep Term objects (Variable, Constant) as-is
                            processed_args.append(arg_type)
                        else:
                            # Convert formula to infix string
                            processed_args.append(self.infix(arg_type))
                    return operator_type, processed_args, None

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