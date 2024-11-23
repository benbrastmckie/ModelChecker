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

from hidden_helpers import (
    bitvec_to_substates,
    not_implemented_string,
    flatten,
    pretty_set_print,
)

import inspect

from z3 import Const, DeclareSort

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

        if len(self.prefix_sentence) > 1: 
            self.original_arguments = [ # sentece_objects
                Sentence(self.infix(arg))
                for arg in self.prefix_sentence[1:]
            ]
        else:
            self.original_arguments = None

        # # set defaults to None for prefix values with defined operators if any
        # # TODO: can the derived_type attribute be dropped?
        # self.original_type = None # updated in Syntax with operator_collection
        # # TODO: can the prefix_object attribute be dropped?
        # self.prefix_object = None # updated in ModelConstraints with semantics

        # set defaults to None before updating in Syntax and ModelConstraints
        self.original_operator = None # 
        self.operator = None # 
        self.arguments = None # sentece_objects
        self.sentence_letter = None # 

        # TODO: would be nice to remove this attribute if there is a better way
        self.updated_objects = False

        # # TODO: can the derived_type attribute be dropped?
        # self.derived_type = None # updated in Syntax from original_type
        # # TODO: can the derived_sentence attribute be dropped?
        # self.derived_sentence = None # updated in Syntax with update_types
        # # TODO: can the derived_object attribute be dropped?
        # self.derived_object = None # updated in ModelConstraints with semantics

        # set proposition to None to be updates later
        self.proposition = None # updated in ModelStructure with Z3 model

    def __str__(self):
        return self.name
    
    def __repr__(self):
        return self.name

    def op_left_right(self, tokens):
        """Divides whatever is inside a pair of parentheses into the left argument,
        right argument, and the operator."""

        def balanced_parentheses(tokens):
            """Check if parentheses are balanced in the argument."""
            stack = []
            for token in tokens:
                if token == "(":
                    stack.append(token)
                elif token == ")":
                    if not stack:
                        return False
                    stack.pop()
            return len(stack) == 0

        def check_right(tokens, operator):
            if not tokens:
                raise ValueError(f"Expected an argument after the operator {operator}")
            if not balanced_parentheses(tokens):
                raise ValueError("Unbalanced parentheses")
            return tokens  # Remaining tokens are the right argument

        def cut_parentheses(left, tokens):
            count = 1  # To track nested parentheses
            while tokens:
                token = tokens.pop(0)
                if token == "(":
                    count += 1
                    left.append(token)
                elif token == ")":
                    count -= 1
                    left.append(token)
                elif count > 0:
                    left.append(token)
                elif not tokens:
                    raise ValueError(f"Extra parentheses in {tokens}.")
                else:
                    operator = token
                    right = check_right(tokens, operator)
                    return operator, left, right
            raise ValueError(f"The expression {tokens} is incomplete.")

        def process_operator(tokens):
            if tokens:
                return tokens.pop(0)
            raise ValueError("Operator missing after operand")

        def extract_arguments(tokens):
            """Extracts the left argument and right argument from tokens."""
            left = []
            while tokens:
                token = tokens.pop(0)
                if token == "(":
                    left.append(token)
                    return cut_parentheses(left, tokens)
                elif token.isalnum() or token in {"\\top", "\\bot"}:
                    left.append(token)
                    operator = process_operator(tokens)
                    right = check_right(tokens, operator)
                    return operator, left, right
                else:
                    left.append(token)
            raise ValueError("Invalid expression or unmatched parentheses")

        result = extract_arguments(tokens)
        if result is None:
            raise ValueError("Failed to extract arguments")
        return result

    def parse_expression(self, tokens):
        """Parses a list of tokens representing a propositional expression and returns
        the expression in prefix notation.
        At this point, prefix is with strings for everything, I think
        """
        if not tokens:  # Check if tokens are empty before processing
            raise ValueError("Empty token list")
        token = tokens.pop(0)  # Get the next token
        if token == "(":  # Handle binary operator case (indicated by parentheses)
            closing_parentheses = tokens.pop()  # Remove the closing parenthesis
            if closing_parentheses != ")":
                raise SyntaxError(
                    f"The sentence {tokens} is missing a closing parenthesis."
                )
            operator, left, right = self.op_left_right(tokens)
            left_arg, left_comp = self.parse_expression(left)  # Parse the left argument
            right_arg, right_comp = self.parse_expression(right)  # Parse the right argument
            complexity = left_comp + right_comp + 1
            return [operator, left_arg, right_arg], complexity 
        if token.isalnum():  # Handle atomic sentences
            return [token], 0
        elif token in {"\\top", "\\bot"}:  # Handle extremal operators
            return [token], 0
        arg, comp = self.parse_expression(tokens)
        return [token, arg], comp + 1 
        
    def prefix(self, infix_sentence):
        """For converting from infix to prefix notation without knowing which
        which operators the language includes."""
        tokens = infix_sentence.replace("(", " ( ").replace(")", " ) ").split()
        derived_object, complexity = self.parse_expression(tokens)
        return derived_object, complexity

    def infix(self, prefix_sent):
        """Takes a sentence in prefix notation (in any of the three kinds)
        and translates it to infix notation (a string)."""
        # Base case: if prefix_sent is an operator class
        # if hasattr(prefix_sent[0], "primitive"):
        #     return prefix_sent.name  # or prefix_sent.name
        # If prefix_sent is a list or tuple (recursive case)
        if not isinstance(prefix_sent, (list, tuple)):
            raise ValueError(f"prefix_sent {prefix_sent} is not of type list.")
        if len(prefix_sent) == 1:
            return str(prefix_sent[0])
        op = prefix_sent[0]
        # Extract the operator's symbol or name
        op_str = str(op)
        if len(prefix_sent) == 2:
            return f"{op_str} {self.infix(prefix_sent[1])}"
        left_expr = prefix_sent[1]
        right_expr = prefix_sent[2]
        return f"({self.infix(left_expr)} {op_str} {self.infix(right_expr)})"
        # return str(prefix_sent)

    def operator_is_defined(self, original_type):
        """
        checks if there are defined operators in a prefix type.
        Returns True or False
        """
        if hasattr(original_type[0], "primitive"):
            operator = original_type[0]
            if operator.primitive is False:
                return True
        return False

    def update_types(self, operator_collection):
        """Draws on the operator_collection to apply the operators that occur
        in the prefix_sentence in order to generate a original_type which has
        operator classes in place of operator strings and AtomSorts in place
        of sentence letters. If the operator is not primitive, then ."""

        def derive_type(original_type):
            """This function translates a original_type possibly with defined
            operators to a derived_type without defined operators."""
            if not self.operator_is_defined(original_type):
                if len(original_type) > 1:
                    operator, args = original_type[0], original_type[1:]
                    # TODO: I don't think full recursion is needed here
                    # derived_args = [derive_type(arg) for arg in args]
                    # return [operator] + derived_args
                    return [operator] + args
                return original_type
            operator, args = original_type[0], original_type[1:]
            # derived_args = [derive_type(arg) for arg in args]
            if not hasattr(operator, "primitive"):
                raise TypeError(f"Operator {operator} is not a subclass of Operator.")
            # TODO: can the dummy variable be avoided?
            derivation = operator('a').derived_definition(*args)
            # derivation = operator('a').derived_definition(*derived_args)
            return derivation

        def store_types(derived_type):
            if self.name.isalnum(): # sentence letter
                return None, None, derived_type[0]
            # TODO: return a list of the extremals and change def in derived_op
            if self.name in {'\\top', '\\bot'}: # extremal operator
                return derived_type[0], None, None
            if len(derived_type) > 1: # complex sentence
                operator_type, argument_types = derived_type[0], derived_type[1:]
                arguments = [Sentence(self.infix(arg_type)) for arg_type in argument_types]
                return operator_type, arguments, None
            raise ValueError(f"the derived_type for {self} is invalid in store_types().")

        original_type = operator_collection.apply_operator(self.prefix_sentence)
        if self.original_arguments:
            self.original_operator = original_type[0]

        derived_type = derive_type(original_type)
        self.operator, self.arguments, self.sentence_letter = store_types(derived_type)
        # print(f"STORE TYPES: {self} has sentence_letter {self.sentence_letter} of TYPE {type(self.sentence_letter)}")

        # print("ARGUMENTS STORED:", self.arguments)
        # print("SENT LET STORED:", self.sentence_letter)
        # # TODO: remove derived_sentence attribute
        # if self.operator_is_defined(self.original_type):
        #     derived_infix = self.infix(self.derived_type)
        #     self.derived_sentence = Sentence(derived_infix)
    
    # def update_derived(self):
    #     if self.original_type is None:
    #         raise ValueError(f"original_type for {self} is None in update_derived_type.")
    #     self.derived_type = self.derive_type(self.original_type)
    #     if self.operator_is_defined(self.original_type):
    #         derived_infix = self.infix(self.derived_type)
    #         self.derived_sentence = Sentence(derived_infix)
    
    def update_objects(self, model_constraints): # happens in ModelConstraints init
        """Given an instance of ModelConstraints, this method updates the values
        of self.derived_object and self.operator with the semantics that
        model_constraints includes."""

        def activate_operator(some_type):
            if some_type is None: # operator is None if sentence_letter
                return None
            # TODO: fix check
            # if isinstance(some_type, type):
            #     return some_type
            return model_constraints.operators[some_type.name]

        self.original_operator = activate_operator(self.original_operator)
        self.operator = activate_operator(self.operator)

        # TODO: why are these needed if all objects in the dict get updated?
        if self.original_arguments:
            for argument in self.original_arguments:
                argument.update_objects(model_constraints)
        if self.arguments:
            for argument in self.arguments:
                argument.update_objects(model_constraints)


    def update_proposition(self, model_structure): # happens in ModelStructure init
        """Builds a proposition object for the sentence given the model_structure."""
        # TODO: add check
        # if self.derived_object is None:
        #     raise ValueError(f"derived_object for {self} is None when calling update_proposition.")
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

    def general_print(self, sentence_obj, eval_world, indent_num):
        proposition = sentence_obj.proposition
        model_structure = proposition.model_structure

        proposition.print_proposition(eval_world, indent_num)
        indent_num += 1

        # print(f"ARGUMENTS: {sentence_obj.original_arguments}")
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
            # indent_num += 1
            for world in other_worlds:
                model_structure.recursive_print(argument, world, indent_num)
        if len(arguments) == 2:
            left_argument, right_argument = arguments
            # indent_num += 1
            model_structure.recursive_print(left_argument, eval_world, indent_num)
            other_world_strings = {bitvec_to_substates(u, N) for u in other_worlds}
            print(
                f'{"  " * indent_num}{CYAN}|{left_argument}|-alternatives '
                f'to {bitvec_to_substates(eval_world, N)} = '
                f'{pretty_set_print(other_world_strings)}{RESET}'
            )
            indent_num += 1
            for alt_world in other_worlds:
                model_structure.recursive_print(right_argument, alt_world, indent_num)
    
    
# class DefinedOperator(Operator):
#     """NOTE: I wonder about building a sent_obj first thing, adding this to the
#     sentence_dict or updating?"""
#
#     primitive = False
#
#     def derived_definition(self, leftarg, rightarg):
#         """
#         in (kind of) prefix form give the definition of the operator in terms of other operators
#         what's here is the default form—is here to avoid linter complaints
#         """
#         return []
#
#     def __init__(self, semantics, loop_check=True):
#         super().__init__(semantics)
#
#         # check self is an arg of derived_definition
#         op_subclass = self.__class__
#         args_without_self = inspect.signature(self.derived_definition).parameters # parameters besides self in derived_definition
#         args_with_self = inspect.signature(op_subclass.derived_definition).parameters # params above plus 'self'
#         if 'self' not in args_with_self:
#             raise ValueError(f"self should be an argument of {op_subclass.__name__}'s "
#                              "derived_definition method (and it should go unused).")
#         # from now on, can assume 'self' is an argument of derived_definition. 
#
#         # check if derived_definition is implemented (ie is not default)
#         if len(args_with_self) == 1 and 'self' in args_with_self:
#             raise NameError(
#                 f"Derived operator class {op_subclass.__name__} does not have an implemented "
#                 f"derived_definition method. ")
#         
#         # check for arity match between self.arity and derived_def num args (excluding self)
#         derived_def_num_args = len(args_without_self)
#         op_name = op_subclass.__name__
#         mismatch_arity_msg = (
#             f"the specified arity of value {self.arity} for the DerivedOperator class {op_name} "
#             f"does not match the number of arguments (excluding 'self') for {op_name}'s derived_"
#             f"definition property ({derived_def_num_args} non-self arguments currently.)")
#         assert self.arity == derived_def_num_args, mismatch_arity_msg
#
#         # check for DefinedOperators defined in terms of each other
#         sample_derived_def = self.derived_definition(*(derived_def_num_args * ("a",)))
#         ops_in_def = [elem for elem in flatten(sample_derived_def) if isinstance(elem, type)]
#         self.defined_operators_in_definition = [op for op in ops_in_def if not op.primitive]
#         if loop_check:
#             for def_opcls in self.defined_operators_in_definition:
#                 if self.__class__ in def_opcls('dummy sem', False).defined_operators_in_definition:
#                     ermsg = (f"{op_name} and {def_opcls.__name__} are defined in terms of each "
#                             f"other. Please edit their derived_definition methods to avoid this.")
#                     raise RecursionError(ermsg)


class DefinedOperator(Operator):
    """Represents an operator defined in terms of other operators."""

    primitive = False

    def derived_definition(self, *args):
        """
        Returns the definition of the operator in terms of other operators.
        Must be implemented by subclasses.
        """
        pass

    def __init__(self, semantics, loop_check=True):
        super().__init__(semantics)

        op_subclass = self.__class__

        # Ensure derived_definition is implemented
        if self.__class__.derived_definition == DefinedOperator.derived_definition:
            raise NotImplementedError(
                f"Derived operator class {op_subclass.__name__} must implement "
                f"the derived_definition method."
            )

        # Get the signature of derived_definition
        derived_def_sig = inspect.signature(op_subclass.derived_definition)
        params = list(derived_def_sig.parameters.values())

        # Exclude 'self' parameter
        if params and params[0].name == 'self':
            params = params[1:]

        derived_def_num_args = len(params)

        # Ensure 'arity' attribute exists
        if not hasattr(self, 'arity'):
            raise AttributeError(f"{op_subclass.__name__} must define an 'arity' attribute.")

        # Check for arity match
        if self.arity != derived_def_num_args:
            mismatch_arity_msg = (
                f"The specified arity of value {self.arity} for the DerivedOperator class "
                f"{op_subclass.__name__} does not match the number of arguments (excluding 'self') "
                f"for its derived_definition method ({derived_def_num_args} non-self arguments)."
            )
            raise ValueError(mismatch_arity_msg)

        # Check for circular definitions
        dummy_args = [None] * derived_def_num_args
        sample_derived_def = self.derived_definition(*dummy_args)
        ops_in_def = [elem for elem in flatten(sample_derived_def) if isinstance(elem, type)]
        self.defined_operators_in_definition = [op for op in ops_in_def if not op.primitive]
        if loop_check:
            for def_opcls in self.defined_operators_in_definition:
                def_op_instance = def_opcls('dummy sem', False)
                if self.__class__ in def_op_instance.defined_operators_in_definition:
                    ermsg = (
                        f"{op_subclass.__name__} and {def_opcls.__name__} are defined in terms of "
                        f"each other. Please edit their derived_definition methods to avoid this."
                    )
                    raise RecursionError(ermsg)

class OperatorCollection:
    """Stores the operators that will be passed to Syntax."""

    def __init__(self, *input):
        self.operator_classes_dict = {}
        if input:
            self.add_operator(input)

    def __iter__(self):
        yield from self.operator_classes_dict

    # TODO: pytest doesn't like this for some reason
    def __getitem__(self, value):
        return self.operator_classes_dict[value]
    
    def items(self):
        yield from self.operator_classes_dict.items()

    def add_operator(self, input):
        """Input is either an operator class (of type 'type') or a list/tuple of operator classes."""
        if isinstance(input, (list, tuple, set)):
            for operator_class in input:
                self.add_operator(operator_class)
        elif isinstance(input, type):
            if getattr(input, "name", None) is None:
                raise ValueError(f"Operator class {input.__name__} has no name defined.")
            self.operator_classes_dict[input.name] = input
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
        # TODO: this is causing trouble for pytest, by why?
        if isinstance(op, str):
            if op not in self.operator_classes_dict:
                # DEBUG
                # assert False, op
                raise KeyError(f"Operator '{op}' not found in operator_classes_dict.")
            activated.insert(0, self[op])
        else:
            raise TypeError(f"Expected operator name as a string, got {type(op).__name__}.")
        return activated


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

        # 
        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.operator_collection = operator_collection

        infix_inputs = self.infix_premises + self.infix_conclusions
        self.all_sentences = self.sentence_dictionary(infix_inputs)

        self.premises = [
            self.all_sentences[key]
            for key in self.infix_premises
        ]
        self.conclusions = [
            self.all_sentences[key]
            for key in self.infix_conclusions
        ]
        self.sentence_letters = [
            self.all_sentences[key]
            for key in self.all_sentences
            if key.isalnum()
        ]

    def sort_dictionary(self, unstorted_dictionary):
        sorted_sentences = sorted(unstorted_dictionary.items(), key=lambda item: item[1].complexity)
        sorted_dictionary = {s.name: s for _, s in sorted_sentences}
        return sorted_dictionary

    def sub_dictionary(self, sentence):
        """Takes a sentence object as input and builds a dictionary consisting
        of it and all subsentences by looking to its arguments (if any)."""
        sub_dictionary = {}
        sub_dictionary[sentence.name] = sentence
        arguments = []
        if sentence.original_arguments:
            arguments.extend(sentence.original_arguments)
        if sentence.arguments:
            arguments.extend(sentence.arguments)
        if arguments:
            for arg in arguments:
                if arg in sub_dictionary.values():
                    continue
                arg_dict = self.sub_dictionary(arg)
                sub_dictionary.update(arg_dict)
        return sub_dictionary

    def initialize_types(self, sentence):
        """Draws on the operator_collection in order to initialize all sentences
        in the input by replacing operator strings with operator classes and
        updating original_type in that sentence_obj. If the main operator is not
        primitive, derived_arguments are updated with derived_types."""
        operator_collection = self.operator_collection
        # TODO: add appropriate check to avoid redundancy
        if sentence.original_arguments:
            for argument in sentence.original_arguments:
                self.initialize_types(argument)
        sentence.update_types(operator_collection)
        if sentence.arguments: # NOTE: must happen after arguments are stored
            for argument in sentence.arguments:
                self.initialize_types(argument)

    def sentence_dictionary(self, infix_inputs):
        """Takes a list of sentences composing the dictionaries of subsentences
        for each, resulting in a dictionary that includes all subsentences."""
        unsorted_dictionary = {}
        for infix_sent in infix_inputs:
            if infix_sent in unsorted_dictionary.keys():
                continue
            sentence = Sentence(infix_sent)
            self.initialize_types(sentence)
            subsent_dict = self.sub_dictionary(sentence)
            unsorted_dictionary.update(subsent_dict)
        sorted_dictionary = self.sort_dictionary(unsorted_dictionary)
        return sorted_dictionary
