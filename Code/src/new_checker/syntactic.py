"""
This module defines the following classes, culminating in the Syntax class
which is passed to ModelConstraints:
    - **Sentence:** this class is responsible for carrying all values relevant to
    each infix_sentence input by the user in the premises or conclusions.
    - **Operator:** this class sets a number of general defaults that are used by
    the operators the user defines as well as the DefinedOperator class.
    - **DefinedOperator:** ... TODO
    - **OperatorCollection:** this class is responsible for storing all user
    defined operators, passing this collection of operators to Syntax.
    - **Syntax:** this class is responsible for generating a dictionary of sentence
    objects for all premises, conclusions, and their subsentences. By drawing
    on the input operator_collection, all sentences in the dictionary are
    initialized to generate and store original_types for each.
"""

from collections import defaultdict

from hidden_helpers import (
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
    """Given an infix_sentence as input, an instance of this class store the
    original infix_sentence which is used to name the class instance, as well
    as converting and storing that infix_sentence as a prefix_sentence. The
    class instance is later updated in: (1) Syntax to store a original_type which
    depends on an operator_collection; (2) ModelConstraints to store a
    derived_object and operator which depend on the semantics; and (3)
    ModelStructure to store a proposition for the sentence."""

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
            self.original_operator = None
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
        """For converting from infix to prefix notation without knowing which
        which operators the language includes."""
        tokens = infix_sentence.replace("(", " ( ").replace(")", " ) ").split()
        derived_object, complexity = parse_expression(tokens)
        return derived_object, complexity

    def infix(self, prefix):
        """Takes a sentence in prefix notation (in any of the three kinds)
        and translates it to infix notation (a string)."""

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
        """Draws on the operator_collection to apply the operators that occur
        in the prefix_sentence in order to generate a original_type which has
        operator classes in place of operator strings and AtomSorts in place
        of sentence letters. If the operator is not primitive, then ."""

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
        """Given an instance of ModelConstraints, this method updates the values
        of self.derived_object and self.operator with the semantics that
        model_constraints includes."""

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
    """Defaults inherited by every operator."""

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

    def general_print(self, sentence_obj, eval_world, indent_num):
        proposition = sentence_obj.proposition
        model_structure = proposition.model_structure

        proposition.print_proposition(eval_world, indent_num)
        indent_num += 1

        for arg in sentence_obj.original_arguments:
            model_structure.recursive_print(arg, eval_world, indent_num)

    def print_over_worlds(self, sentence_obj, eval_world, other_worlds, indent_num):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        # Move to class or config for flexibility
        CYAN, RESET = '\033[36m', '\033[0m'

        arguments = sentence_obj.original_arguments
        proposition = sentence_obj.proposition
        model_structure = proposition.model_structure
        N = proposition.N

        proposition.print_proposition(eval_world, indent_num)
        indent_num += 1

        if len(arguments) == 1:
            argument = arguments[0]
            for world in other_worlds:
                model_structure.recursive_print(argument, world, indent_num)
        if len(arguments) == 2:
            left_argument, right_argument = arguments
            model_structure.recursive_print(left_argument, eval_world, indent_num)
            indent_num += 1
            other_world_strings = {bitvec_to_substates(u, N) for u in other_worlds}
            print(
                f'{"  " * indent_num}{CYAN}|{left_argument}|-alternatives '
                f'to {bitvec_to_substates(eval_world, N)} = '
                f'{pretty_set_print(other_world_strings)}{RESET}'
            )
            indent_num += 1
            for alt_world in other_worlds:
                model_structure.recursive_print(right_argument, alt_world, indent_num)
    
class DefinedOperator(Operator):
    """Represents an operator defined in terms of other operators."""

    primitive = False

    def derived_definition(self, *args):
        """
        Returns the definition of the operator in terms of other operators.
        Must be implemented by subclasses.
        """
        raise NotImplementedError(
            f"Derived operator class {self.__class__.__name__} must implement the derived_definition method."
        )

    def __init__(self, semantics):
        super().__init__(semantics)
        self._validate_arity()

    def _validate_arity(self):
        """
        Validates that the 'arity' attribute matches the number of arguments
        in the 'derived_definition' method (excluding 'self').
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
    """Stores the operators that will be passed to Syntax."""

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

    def add_operator(self, input):
        """Input is either an operator class (of type 'type') or a list/tuple of operator classes."""
        if isinstance(input, (list, tuple, set)):
            for operator_class in input:
                self.add_operator(operator_class)
        elif isinstance(input, type):
            if input.name in self.operator_dictionary.keys():
                return
            if getattr(input, "name", None) is None:
                raise ValueError(f"Operator class {input.__name__} has no name defined.")
            self.operator_dictionary[input.name] = input
        else:
            raise TypeError(f"Unexpected input type {type(input)} for add_operator.")

    def apply_operator(self, prefix_sentence):
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

    # # NOTE: UPDATE OP STRATEGY
    # def duplicate(self):
    #     """Creates a shallow copy of the OperatorCollection."""
    #     new_collection = OperatorCollection()
    #     new_collection.operator_dictionary = self.operator_dictionary.copy()
    #     return new_collection
    #
    # # NOTE: UPDATE OP STRATEGY
    # def update_operators(self, semantics):
    #     operators = self.operator_dictionary
    #     for key in operators.keys():
    #         if isinstance(operators[key], type):
    #             operators[key] = operators[key](semantics)


class Syntax:
    """Takes infix_premises, infix_conclusions, and operator_collection as
    arguments, generating and storing instances of the Sentence class.
    Draws on Sentence instances for the premises and conclusions in order to
    store a dictionary which includes all subsentences for each before drawing
    on the operator_collection in order to initialize the original_types in each
    sentence object in the dictionary. Lists are then stored for the premises,
    conclusions, and all sentence_letters that occur in theses sentences."""

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
        # self.sentence_letters = [
        #     self.all_sentences[key]
        #     for key in self.all_sentences.keys()
        #     if key.isalnum()
        # ] # updated in build_sentence

        # check for interdefined operators
        self.circularity_check(operator_collection)

    def initialize_sentences(self, infix_sentences):
        """Takes a list of sentences composing the dictionaries of subsentences
        for each, resulting in a dictionary that includes all subsentences."""

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
                    print(f"SENT LET {sentence} TYPE {type(sentence)}")
                return sentence
            sentence_arguments = []
            for infix_arg in sentence.original_arguments:
                sentence_arg = build_sentence(infix_arg)
                sentence_arguments.append(sentence_arg)
            sentence.original_arguments = sentence_arguments
            return sentence

        def initialize_types(sentence):
            """Draws on the operator_collection in order to initialize all sentences
            in the input by replacing operator strings with operator classes and
            updating original_type in that sentence_obj. If the main operator is not
            primitive, derived_arguments are updated with derived_types."""
            # TODO: confirm not needed
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
        """Detects circular dependencies among operators and ensures all dependencies are within the collection."""
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
