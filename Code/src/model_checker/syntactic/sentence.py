"""
Sentence representation for logical formulas.

This module provides the Sentence class, which represents logical formulas
and handles their transformation between infix and prefix notation. It stores
all metadata needed for evaluation including operator linkages, semantic
bindings, and proposition values.
"""

from z3 import ExprRef

from model_checker.utils import parse_expression
from .atoms import AtomSort


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

    def __init__(self, infix_sentence):
        
        # store input, prefix string, complexity, and sentences for arguments
        self.name = infix_sentence
        self.prefix_sentence, self.complexity = self.prefix(infix_sentence)

        # recursive clause: initially stores infix_arguments and infix_operator
        # updated by initialize_sentences in Syntax with operator_collection
        # updated by instantiate in ModelConstraints with semantics
        if self.complexity > 0: 
            self.original_arguments = [ # store infix_arguments
                self.infix(arg)
                for arg in self.prefix_sentence[1:]
            ]
            # updated by update_types:
            self.original_operator = self.prefix_sentence[0]
        else:
            self.original_arguments = None
            self.original_operator = self.prefix_sentence[0] if self.name in {'\\top', '\\bot'} else None
        self.arguments = None # updated by initialize_types
        self.operator = None # updated by update_types

        # update_types via initialize_sentences in Syntax: operator_collection
        self.sentence_letter = None

        # update_proposition via interpret in ModelStructure: z3_model
        self.proposition = None

    def __str__(self):
        return self.name
    
    def __repr__(self):
        return self.name

    def prefix(self, infix_sentence):
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

    def infix(self, prefix):
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
        if isinstance(prefix, ExprRef):
            return str(prefix)
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
        raise TypeError(f"The prefix {prefix} has a type error in infix().")

    def update_types(self, operator_collection): # used in Syntax
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
            if self.name.isalnum(): # sentence letter
                return None, None, derived_type[0]
            if self.name in {'\\top', '\\bot'}: # extremal operator
                return derived_type[0], None, None
            if len(derived_type) > 1: # complex sentence
                operator_type, argument_types = derived_type[0], derived_type[1:]
                infix_arguments = [self.infix(arg_type) for arg_type in argument_types]
                return operator_type, infix_arguments, None
            raise ValueError(f"the derived_type for {self} is invalid in store_types().")

        original_type = operator_collection.apply_operator(self.prefix_sentence)
        if self.original_operator:
            self.original_operator = original_type[0]
        derived_type = derive_type(original_type)
        self.operator, self.arguments, self.sentence_letter = store_types(derived_type)
    
    def update_objects(self, model_constraints): # used in ModelConstraints init
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

    def update_proposition(self, model_structure): # used in ModelStructure init
        """Builds a proposition object for the sentence given the model_structure."""
        self.proposition = model_structure.proposition_class(self, model_structure)