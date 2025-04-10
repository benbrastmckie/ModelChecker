"""
This module provides the core syntactic components for logical formula processing and
operator management in the model checker. It defines five main classes:

    - Sentence: Represents logical formulas and handles their transformation between
      infix and prefix notation. It maintains all metadata needed for evaluation,
      including operator linkages, semantic bindings, and proposition values.

    - Operator: Abstract base class for all logical operators. Defines the interface
      for operator behavior and provides common functionality for instantiation,
      equality testing, and result visualization.

    - DefinedOperator: Extends Operator to support complex operators that can be
      expressed in terms of more primitive ones. Ensures proper validation of
      operator definitions and arity matching.

    - OperatorCollection: Registry and management system for all logical operators.
      Provides methods for operator registration, lookup, and application while
      ensuring operator uniqueness and proper typing.

    - Syntax: Orchestrates the parsing and structuring of logical arguments.
      Processes premises and conclusions, builds a comprehensive sentence hierarchy,
      validates operator dependencies, and prepares the logical structure for
      semantic evaluation.

The module forms the foundation for translating user-input logical formulas into
a structured representation that can be evaluated by the model checker's semantic
components. It ensures proper typing, handles operator definitions, and validates
the logical structure before semantic processing begins.
"""

from .utils import (
    bitvec_to_substates,
    not_implemented_string,
    flatten,
    parse_expression,
    pretty_set_print,
)

import time

import inspect

from z3 import Const, DeclareSort, ExprRef

AtomSort = DeclareSort("AtomSort")

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


class Operator:
    """Base class for all logical operators in the model checker.
    
    This abstract class defines the interface and common functionality for all logical
    operators in the system. It provides core functionality for operator instantiation,
    equality testing, and printing methods used in result visualization.
    
    Concrete operator classes must implement specific semantic functions such as:
    - true_at/false_at: For truth/falsity conditions
    - extended_verify/extended_falsify: For hyperintensional semantics 
    - find_verifiers_and_falsifiers: For finding exact verification sets
    - print_method: For displaying evaluation details
    
    Class Attributes:
        name (str): The symbol representing this operator
        arity (int): The number of arguments this operator takes
        primitive (bool): Whether this operator is primitive (default: True)
    
    Attributes:
        semantics (object): The semantics object this operator uses for evaluation
    """

    name = None
    arity = None
    primitive = True

    def __init__(self, semantics):
        op_class = self.__class__.__name__
        if self.__class__ == Operator:
            raise NotImplementedError(not_implemented_string(op_class))
        if self.name is None or self.arity is None:
            raise NameError(
                f"Your operator class {op_class} is missing a name or an arity. "
                + f"Please add them as class properties of {op_class}."
            )
        self.semantics = semantics

    def __str__(self):
        return str(self.name)

    def __repr__(self):
        return str(self.name)

    def __eq__(self, other):
        if isinstance(other, Operator):
            return self.name == other.name and self.arity == other.arity
        return False

    def __hash__(self):
        return hash((self.name, self.arity))

    def general_print(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints a general evaluation of a sentence at a given evaluation point.

        This method provides a standard way to print a sentence's evaluation results,
        including the sentence itself and its subformulas (arguments) recursively.

        Args:
            sentence_obj (Sentence): The sentence object to be printed
            eval_point (dict): The evaluation point containing world, time, and other context
            indent_num (int): The number of indentation levels for formatting
            use_colors (bool): Whether to use ANSI color codes in the output

        The method first prints the proposition for the sentence at the given evaluation
        point, then recursively prints all subformulas (if any) with increased indentation.
        """
        proposition = sentence_obj.proposition
        model_structure = proposition.model_structure

        proposition.print_proposition(eval_point, indent_num, use_colors)
        indent_num += 1

        if sentence_obj.original_arguments:
            for arg in sentence_obj.original_arguments:
                model_structure.recursive_print(arg, eval_point, indent_num, use_colors)

    # TODO: make this method more deterministic
    def print_over_worlds(self, sentence, eval_point, all_worlds, indent_num, use_colors):
        """Print evaluation details for modal/counterfactual operators across possible worlds.

        This method handles the printing of evaluation results for modal and counterfactual
        operators, showing both the evaluation in the current world and in alternative worlds.
        For counterfactuals, it prints the antecedent in the evaluation world and the
        consequent in each alternative world.

        Args:
            sentence (Sentence): The sentence object being evaluated
            eval_point (dict): The current evaluation point containing world and time info
            all_worlds (list): List of all relevant alternative worlds to consider
            indent_num (int): Number of spaces to indent the output
            use_colors (bool): Whether to use ANSI color codes in output

        The output format shows:
        1. The full sentence evaluation at the current point
        2. For unary operators: evaluation in each alternative world
        3. For binary operators: antecedent evaluation, followed by consequent
           evaluation in each alternative world
        """
        # Move to class or config for flexibility
        if use_colors:
            CYAN, RESET = '\033[36m', '\033[0m'
        else:
            CYAN, RESET = '', ''

        arguments = sentence.original_arguments
        proposition = sentence.proposition
        model_structure = proposition.model_structure
        N = proposition.N

        # TODO: make more deterministic
        # Handle both world_id and traditional world approaches for compatibility
        # In the bimodal theory, we're now using world_id but the base code expects world
        if "world" in eval_point:
            current_world_id = eval_point["world"]
            if "world" not in eval_point and hasattr(model_structure, "get_world_array"):
                eval_point["world"] = model_structure.get_world_array(current_world_id)
        else:
            current_world = eval_point.get("world")

        proposition.print_proposition(eval_point, indent_num, use_colors)
        indent_num += 1

        if len(arguments) == 1:
            sentence = arguments[0]
            for world in all_worlds:
                pass_point = eval_point.copy()
                # Set the world directly - could be a world_id (int) or world array
                # The downstream print_proposition method should handle both appropriately
                pass_point["world"] = world
                model_structure.recursive_print(sentence, pass_point, indent_num, use_colors)
                
        if len(arguments) == 2:
            left_argument, right_argument = arguments
            model_structure.recursive_print(left_argument, eval_point, indent_num, use_colors)
            indent_num += 1
            
            # TODO: is there an approach that is agnostic about what the eval_point includes?
            # Handle displaying world state for both traditional and new approach
            if "world" in eval_point:
                if "time" in eval_point and hasattr(eval_point["world"], "__getitem__"):
                    # Bimodal case: world is an array/mapping indexed by time
                    current_world_state = bitvec_to_substates(eval_point["world"][eval_point["time"]], N)
                elif hasattr(eval_point["world"], "as_ast") or isinstance(eval_point["world"], int):
                    # Default case: world is directly a bitvec
                    current_world_state = bitvec_to_substates(eval_point["world"], N)
                else:
                    # Any other case
                    current_world_state = str(eval_point["world"])
            else:
                current_world_state = "current world"
                
            other_world_strings = set()
            for world in all_worlds:
                try:
                    # Try to get the world state at the current time
                    if "time" in eval_point and hasattr(world, "__getitem__"):
                        # Bimodal case: world is an array/mapping indexed by time
                        world_state = bitvec_to_substates(world[eval_point["time"]], N)
                        other_world_strings.add(str(world_state))
                    elif hasattr(world, "as_ast") or isinstance(world, int):
                        # Default case: world is directly a bitvec
                        world_state = bitvec_to_substates(world, N)
                        other_world_strings.add(str(world_state))
                    else:
                        other_world_strings.add(str(world))
                except Exception as e:
                    # Add error information if needed for debugging
                    # print(f"Error getting world state: {e}")
                    other_world_strings.add(str(world))
                    
            print(
                f'{"  " * indent_num}{CYAN}|{left_argument}|-alternatives '
                f'to {current_world_state} = '
                f'{pretty_set_print(other_world_strings)}{RESET}'
            )
            
            indent_num += 1
            for alt_world in all_worlds:
                alt_point = eval_point.copy()
                # Set the world directly - could be a world_id (int) or world array
                # The downstream print_proposition method should handle both appropriately
                alt_point["world"] = alt_world
                model_structure.recursive_print(right_argument, alt_point, indent_num, use_colors)
    
    def print_over_times(self, sentence_obj, eval_point, other_times, indent_num, use_colors):
        """Print evaluation details for temporal operators across different time points.

        This method handles the printing of evaluation results for temporal operators,
        showing both the evaluation at the current time point and at other relevant
        time points. For binary temporal operators, it prints the first argument at
        the evaluation time and the second argument at each alternative time point.

        Args:
            sentence_obj (Sentence): The sentence object being evaluated
            eval_point (dict): The current evaluation point containing world and time info
            other_times (list): List of all relevant alternative time points to consider
            indent_num (int): Number of spaces to indent the output
            use_colors (bool): Whether to use ANSI color codes in output
        """
        if use_colors:
            CYAN, RESET = '\033[36m', '\033[0m'
        else:
            CYAN, RESET = '', ''

        arguments = sentence_obj.original_arguments
        proposition = sentence_obj.proposition
        model_structure = proposition.model_structure
        
        # Store the original time value to restore it later
        original_time = eval_point["time"]

        # Print the main proposition
        proposition.print_proposition(eval_point, indent_num, use_colors)
        indent_num += 1

        if len(arguments) == 1:
            # For unary operators like Future/Past, we evaluate at different times
            argument = arguments[0]
            for time in other_times:
                # Create a copy with updated time but same world
                temp_point = eval_point.copy()
                temp_point["time"] = time
                model_structure.recursive_print(argument, temp_point, indent_num, use_colors)
            
            # Restore the original time value
            eval_point["time"] = original_time
                
        if len(arguments) == 2:
            # For binary operators
            left_argument, right_argument = arguments
            model_structure.recursive_print(left_argument, eval_point, indent_num, use_colors)
            indent_num += 1
            
            # Display the time alternatives
            print(
                f'{"  " * indent_num}{CYAN}|{left_argument}|-alternatives '
                f'to time {eval_point["time"]} = '
                f'{pretty_set_print([f"t={t}" for t in other_times])}{RESET}'
            )
            
            indent_num += 1
            for alt_time in other_times:
                alt_point = eval_point.copy()
                alt_point["time"] = alt_time
                model_structure.recursive_print(right_argument, alt_point, indent_num, use_colors)
    
class DefinedOperator(Operator):
    """Represents a logical operator defined in terms of other operators.
    
    Defined operators are non-primitive operators that can be expressed using 
    combinations of more basic operators. For example, implication (→) can be 
    defined in terms of negation and disjunction (¬p ∨ q).
    
    Subclasses must implement the derived_definition method which specifies
    how the operator can be expressed in terms of other operators. The class
    validates that the arity matches the defined derivation.
    
    Class Attributes:
        primitive (bool): Always False for defined operators
        
    Required methods for subclasses:
        derived_definition(*args): Returns the definition in terms of other operators
    """

    primitive = False

    def derived_definition(self, *args):
        """
        Returns the definition of the operator in terms of other operators.
        
        This method specifies how a defined operator can be expressed using other
        (typically primitive) operators. For example, an implementation for implication
        might return ['∨', ['¬', arg1], arg2] where arg1 and arg2 are the arguments.
        
        Args:
            *args: The arguments to the operator (number must match the operator's arity)
            
        Returns:
            list: A nested list structure representing the definition in prefix notation
            
        Raises:
            NotImplementedError: This method must be implemented by all subclasses
        """
        raise NotImplementedError(
            f"Derived operator class {self.__class__.__name__} must implement the derived_definition method."
        )

    def __init__(self, semantics):
        super().__init__(semantics)
        self._validate_arity()

    def _validate_arity(self):
        """
        Validates that the operator's declared arity matches its implementation.
        
        This method ensures consistency between the operator's declared 'arity' class attribute
        and the number of parameters in its 'derived_definition' method. This validation is
        crucial for maintaining type safety and preventing runtime errors.
        
        For example, if an operator declares arity=2 but its derived_definition method
        only accepts one argument (plus self), this validation will fail.
        
        Raises:
            AttributeError: If the operator class doesn't define an 'arity' attribute
            ValueError: If the declared arity doesn't match the number of parameters
                       in the derived_definition method
        """
        # Retrieve the signature of the derived_definition method
        signature = inspect.signature(self.derived_definition)
        params = list(signature.parameters.values())

        # Exclude 'self' if present
        if params and params[0].name == 'self':
            params = params[1:]

        derived_def_num_args = len(params)

        # Check if 'arity' is defined
        if not hasattr(self, 'arity'):
            raise AttributeError(
                f"{self.__class__.__name__} must define an 'arity' attribute."
            )

        # Validate that 'arity' matches the number of arguments
        if self.arity != derived_def_num_args:
            raise ValueError(
                f"The specified arity of {self.arity} for {self.__class__.__name__} does not match "
                f"the number of arguments ({derived_def_num_args}) for its 'derived_definition' method."
            )


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


class Syntax:
    """Processes logical formulas and builds a structured representation of an argument.
    
    This class takes premises and conclusions in infix notation along with an operator
    collection, and constructs a comprehensive representation of the logical argument.
    It handles parsing sentences, organizing them hierarchically, and preparing them
    for semantic evaluation.
    
    The class performs several key functions:
    1. Parses infix sentences into structured objects
    2. Creates a dictionary of all sentences and subsentences
    3. Links operators in sentences to their operator classes
    4. Extracts all atomic sentence letters used in the argument
    5. Validates that defined operators don't have circular dependencies
    
    Attributes:
        infix_premises (list): Original premise sentences in infix notation
        infix_conclusions (list): Original conclusion sentences in infix notation
        operator_collection (OperatorCollection): Available logical operators
        all_sentences (dict): Maps sentence strings to their Sentence objects
        sentence_letters (list): All atomic sentence letters in the argument
        premises (list): Sentence objects for all premises
        conclusions (list): Sentence objects for all conclusions
        start_time (float): When the syntax processing began
    """

    def __init__(
        self,
        infix_premises,
        infix_conclusions,
        operator_collection,
    ):

        # start timer
        self.start_time = time.time()

        # store inputs
        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.operator_collection = operator_collection

        # initialize inputs
        self.all_sentences = {} # updated in build_sentence
        # self.operators_used = []
        self.sentence_letters = [] # updated in build_sentence
        self.premises = self.initialize_sentences(self.infix_premises)
        self.conclusions = self.initialize_sentences(self.infix_conclusions)

        # check for interdefined operators
        self.circularity_check(operator_collection)

    def initialize_sentences(self, infix_sentences):
        """Processes a list of sentences and builds a comprehensive dictionary of all sentences and their subsentences.
        
        This method takes a list of infix sentences and:
        1. Converts each sentence into a Sentence object
        2. Recursively processes all subsentences
        3. Stores all sentences and subsentences in self.all_sentences
        4. Updates sentence types using the operator collection
        5. Identifies and stores atomic sentence letters
        
        Args:
            infix_sentences (list): A list of strings representing logical formulas in infix notation
            
        Returns:
            list: A list of Sentence objects corresponding to the input sentences
            
        Side Effects:
            - Updates self.all_sentences with all sentences and subsentences
            - Updates self.sentence_letters with atomic sentence letters found
        """

        def build_sentence(infix_sentence):
            if infix_sentence in self.all_sentences.keys():
                return self.all_sentences[infix_sentence]
            sentence = Sentence(infix_sentence)
            # TODO: confirm not needed
            # if sentence.original_operator:
            #     self.operators_used.append(sentence.original_operator)
            self.all_sentences[sentence.name] = sentence
            if sentence.original_arguments is None:
                if sentence.name.isalnum():
                    self.sentence_letters.append(sentence)
                return sentence
            sentence_arguments = []
            for infix_arg in sentence.original_arguments:
                sentence_arg = build_sentence(infix_arg)
                sentence_arguments.append(sentence_arg)
            sentence.original_arguments = sentence_arguments
            return sentence

        def initialize_types(sentence):
            """Initializes sentence types using the operator collection.
            
            This method performs two key functions:
            1. Replaces operator strings with their corresponding operator classes from
               the operator collection
            2. Updates the sentence's type information (original_type, arguments)
            
            For non-primitive operators (defined operators), this also processes their
            derived arguments according to their definitions.
            
            Args:
                sentence (Sentence): The sentence object to initialize
                
            Side Effects:
                - Updates sentence.original_type with operator classes
                - Updates sentence.arguments for defined operators
            """
            # TODO: confirm not needed with derived operators
            # if sentence.original_arguments:
            #     for argument in sentence.original_arguments:
            #         initialize_types(argument)
            sentence.update_types(self.operator_collection)
            if sentence.arguments: # NOTE: must happen after arguments are stored
                sentence_arguments = []
                for infix_arg in sentence.arguments:
                    argument = build_sentence(infix_arg)
                    initialize_types(argument)
                    sentence_arguments.append(argument)
                sentence.arguments = sentence_arguments 

        sentence_objects = []
        for infix_sent in infix_sentences:
            # TODO: this check/continue leads to errors
            # if infix_sent in self.all_sentences.keys():
            #     continue
            sentence = build_sentence(infix_sent)
            initialize_types(sentence)
            sentence_objects.append(sentence)
        return sentence_objects

    def circularity_check(self, operator_collection):
        """Validates operator dependencies and detects circular definitions.
        
        This method performs two key validation checks on the operator collection:
        1. Ensures all operator dependencies are defined within the collection
        2. Detects any circular dependencies between defined operators
        
        For example, if operator A is defined in terms of B, and B is defined in
        terms of A, this would be detected as a circular dependency. Similarly,
        if an operator references an undefined operator C, this would raise an error.
        
        Args:
            operator_collection (OperatorCollection): The collection of operators to validate
            
        Raises:
            ValueError: If an operator depends on undefined operators
            RecursionError: If circular dependencies are detected between operators
            
        Example:
            If operator Implies is defined as (¬p ∨ q) but ¬ is not in the collection,
            this would raise a ValueError. If Implies is defined using Or and Or is
            defined using Implies, this would raise a RecursionError.
        """
        dependency_graph = {}
        operator_set = set(operator_collection.operator_dictionary.values())

        # Build the dependency graph
        for operator_class in operator_collection.operator_dictionary.values():
            if operator_class.primitive:
                continue
            # Ensure derived_definition is callable
            if isinstance(operator_class, type) and callable(getattr(operator_class, 'derived_definition', None)):
                sig = inspect.signature(operator_class.derived_definition)
                num_params = len(sig.parameters)
                dummy_args = [None] * num_params
                dependencies = {
                    elem for elem in flatten(operator_class.derived_definition(*dummy_args))
                    if isinstance(elem, type)
                }
                # Identify missing dependencies if any
                missing_dependencies = dependencies - operator_set
                if missing_dependencies:
                    missing_names = [op.name for op in missing_dependencies]
                    raise ValueError(
                        f"Operator '{operator_class.name}' depends on undefined operators: {missing_names}"
                    )
                # Update the dependency graph
                if operator_class not in dependency_graph:
                    dependency_graph[operator_class] = set()
                dependency_graph[operator_class].update(dependencies)
                continue
            raise ValueError(
                f"Error processing operator '{operator_class.name}'"
            )

        visited = set()
        recursion_stack = []

        def dfs(current):
            if current in recursion_stack:
                cycle = " -> ".join(op.name for op in recursion_stack) + f" -> {current.name}"
                raise RecursionError(
                    f"Circular definition detected in {current.name}.\n\nCYCLE: {cycle}\n"
                )
            if current in visited:
                return
            recursion_stack.append(current)
            for dependent in dependency_graph.get(current, set()):
                dfs(dependent)
            recursion_stack.remove(current)
            visited.add(current)

        # Perform DFS for each operator to detect cycles
        for operator in operator_collection.operator_dictionary.values():
            if not operator.primitive and operator not in visited:
                dfs(operator)
