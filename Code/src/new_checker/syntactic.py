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
    initialized to generate and store prefix_types for each.
"""

from hidden_helpers import (
    not_implemented_string,
    flatten,
)

import inspect

from z3 import Const, DeclareSort

from model_checker.model_definitions import bitvec_to_substates, pretty_set_print

AtomSort = DeclareSort("AtomSort")

class Sentence:
    """Given an infix_sentence as input, an instance of this class store the
    original infix_sentence which is used to name the class instance, as well
    as converting and storing that infix_sentence as a prefix_sentence. The
    class instance is later updated in: (1) Syntax to store a prefix_type which
    depends on an operator_collection; (2) ModelConstraints to store a
    prefix_object and prefix_operator which depend on the semantics; and (3)
    ModelStructure to store a proposition for the sentence."""

    def __init__(self, infix_sentence):
        
        # store input, prefix string, complexity, and sentences for arguments
        self.name = infix_sentence
        self.prefix_sentence, self.complexity = self.prefix(infix_sentence)
        if len(self.prefix_sentence) > 1: 
            self.arguments = [
                Sentence(self.infix(arg))
                for arg in self.prefix_sentence[1:]
            ]
        else:
            self.arguments = None

        # set defaults to None for values that will be updated later
        self.prefix_type = None # updated in Syntax with operator_collection
        self.derived_type = None # updated in Syntax with operator_collection
        self.derived_arguments = None # updated in Syntax
        self.prefix_object = None # updated in ModelConstraints with semantics
        self.prefix_operator = None # updated in ModelConstraints with semantics
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
        prefix_object, complexity = self.parse_expression(tokens)
        return prefix_object, complexity

    def infix(self, prefix_sent): 
        """Takes a sentence in prefix notation (in any of the three kinds)
        and translates it to infix notation (a string)."""
        if isinstance(prefix_sent, Operator):
            return str(prefix_sent)
        if len(prefix_sent) == 1:
            return str(prefix_sent[0])
        op = prefix_sent[0]
        if len(prefix_sent) == 2:
            return f"{op} {self.infix(prefix_sent[1])}"
        left_expr = prefix_sent[1]
        right_expr = prefix_sent[2]
        return f"({self.infix(left_expr)} {op} {self.infix(right_expr)})"

    def check_for_defined_operators(self, prefix_type):
        """
        checks if there are defined operators in a prefix type.
        Returns True or False
        """
        flattened_pt = flatten(prefix_type)
        for elem in flattened_pt:
            if isinstance(elem, type):
                if not hasattr(elem, "primitive"):
                    raise TypeError(f"operator {elem} seems to not be a subclass of the Operator class!")
                if not elem.primitive:
                    return True
        return False

    def derive_type(self, prefix_type):
        """This function translates a prefix_type possibly with defined
        operators to a derived_type without defined operators."""

        # Checks for defined operators including atomic cases
        if not self.check_for_defined_operators(prefix_type):
            return prefix_type

        op, args = prefix_type[0], prefix_type[1:]
        translated_args = [self.derive_type(arg) for arg in args]

        if not hasattr(op, 'primitive'):
            raise TypeError(f"Operator {op} is not a subclass of Operator.")

        if not op.primitive:
            translation = op('a').derived_definition(*translated_args)
        else: 
            translation = [op] + translated_args
        return translation
        # DISCUSS: is this really needed?
        # return self.derived_type(translation)

    def update_prefix_type(self, operator_collection):
        """Draws on the operator_collection to apply the operators that occur
        in the prefix_sentence in order to generate a prefix_type which has
        operator classes in place of operator strings and AtomSorts in place
        of sentence letters. If the operator is not primitive, then ."""
        self.prefix_type = operator_collection.apply_operator(self.prefix_sentence)
        self.derived_type = self.derive_type(self.prefix_type)
    
    def update_derived_arguments(self):
        if self.derived_type is None:
            raise ValueError(f"derived_type for {self} is None in update_derived_arguments.")
        derived_args = self.derived_type[1:]
        self.derived_arguments = [
            Sentence(self.infix(arg))
            for arg in derived_args
        ]

    def activate_prefix_with_semantics(self, prefix_type, model_constraints):
        """Given a prefix_type with operator classes and AtomSorts, this method
        replaces each operator class with the instance of that operator stored
        in model_constraints, and so returns a prefix_object."""
        if prefix_type is None:
            raise ValueError(f"prefix_type for {self} is None in activate_prefix_with_semantics.")
        new_prefix_form = []
        for elem in prefix_type:
            if isinstance(elem, type):
                new_prefix_form.append(model_constraints.operators[elem.name])
            elif isinstance(elem, list):
                new_prefix_form.append(self.activate_prefix_with_semantics(elem, model_constraints))
            else:
                new_prefix_form.append(elem)
        return new_prefix_form

    def update_prefix_object(self, model_constraints): # happens in ModelConstraints init
        """Given an instance of ModelConstraints, this method updates the values
        of self.prefix_object and self.prefix_operator with the semantics that
        model_constraints includes."""
        if self.prefix_type is None:
            raise ValueError(f"{self} has None for prefix_type.")
        self.prefix_object = self.activate_prefix_with_semantics(
            self.derived_type,
            model_constraints
        )
        if self.arguments or self.name in {'\\top', '\\bot'}:
            self.prefix_operator = self.prefix_object[0]

    def update_proposition(self, model_structure): # happens in ModelStructure init
        """Builds a proposition object for the sentence given the model_structure."""
        if self.prefix_object is None:
            raise ValueError(f"prefix_object for {self} is None when calling update_proposition.")
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
        sentence_obj.proposition.print_proposition(eval_world, indent_num)
        model_structure = sentence_obj.proposition.model_structure
        indent_num += 1
        if len(sentence_obj.arguments) == 1:
            arg_sent_obj = sentence_obj.arguments[0]
            model_structure.recursive_print(arg_sent_obj, eval_world, indent_num)
        if len(sentence_obj.arguments) == 2:
            left_sent_obj, right_sent_obj = sentence_obj.arguments
            model_structure.recursive_print(left_sent_obj, eval_world, indent_num)
            model_structure.recursive_print(right_sent_obj, eval_world, indent_num)

    def print_over_worlds(self, sentence_obj, eval_world, other_worlds, indent_num):
        """Print counterfactual and the antecedent in the eval_world. Then
        print the consequent in each alternative to the evaluation world.
        """
        CYAN, RESET = '\033[36m', '\033[0m'  # Move to class or config for flexibility
        # DISCUSS: why doesn't sentence_obj.model_structure exist?
        proposition = sentence_obj.proposition
        model_structure = proposition.model_structure
        N = proposition.N
        proposition.print_proposition(eval_world, indent_num)
        indent_num += 1

        if len(sentence_obj.arguments) == 1:
            arg_sent_obj = sentence_obj.arguments[0]
            indent_num += 1
            for alt_world in other_worlds:
                model_structure.recursive_print(arg_sent_obj, alt_world, indent_num)
        if len(sentence_obj.arguments) == 2:
            left_sent_obj, right_sent_obj = sentence_obj.arguments
            model_structure.recursive_print(left_sent_obj, eval_world, indent_num)
            other_world_strings = {bitvec_to_substates(u, N) for u in other_worlds}
            print(
                f'{"  " * indent_num} {CYAN}{left_sent_obj}-alternatives '
                f'to {bitvec_to_substates(eval_world, N)} = '
                f'{pretty_set_print(other_world_strings)}{RESET}'
            )
            indent_num += 1
            for alt_world in other_worlds:
                model_structure.recursive_print(right_sent_obj, alt_world, indent_num)
    
    
class DefinedOperator(Operator):
    """NOTE: I wonder about building a sent_obj first thing, adding this to the
    sentence_dict or updating?"""

    primitive = False

    def derived_definition(self, leftarg, rightarg):
        """
        in (kind of) prefix form give the definition of the operator in terms of other operators
        what's here is the default form—is here to avoid linter complaints
        """
        return []

    def __init__(self, semantics, loop_check=True):
        super().__init__(semantics)

        # check self is an arg of derived_definition
        op_subclass = self.__class__
        args_without_self = inspect.signature(self.derived_definition).parameters # parameters besides self in derived_definition
        args_with_self = inspect.signature(op_subclass.derived_definition).parameters # params above plus 'self'
        if 'self' not in args_with_self:
            raise ValueError(f"self should be an argument of {op_subclass.__name__}'s "
                             "derived_definition method (and it should go unused).")
        # from now on, can assume 'self' is an argument of derived_definition. 

        # check if derived_definition is implemented (ie is not default)
        if len(args_with_self) == 1 and 'self' in args_with_self:
            raise NameError(
                f"Derived operator class {op_subclass.__name__} does not have an implemented "
                f"derived_definition method. ")
        
        # check for arity match between self.arity and derived_def num args (excluding self)
        derived_def_num_args = len(args_without_self)
        op_name = op_subclass.__name__
        mismatch_arity_msg = (
            f"the specified arity of value {self.arity} for the DerivedOperator class {op_name} "
            f"does not match the number of arguments (excluding 'self') for {op_name}'s derived_"
            f"definition property ({derived_def_num_args} non-self arguments currently.)")
        assert self.arity == derived_def_num_args, mismatch_arity_msg

        # check for DefinedOperators defined in terms of each other
        sample_derived_def = self.derived_definition(*(derived_def_num_args * ("a",)))
        ops_in_def = [elem for elem in flatten(sample_derived_def) if isinstance(elem, type)]
        self.defined_operators_in_definition = [op for op in ops_in_def if not op.primitive]
        if loop_check:
            for def_opcls in self.defined_operators_in_definition:
                if self.__class__ in def_opcls('dummy sem', False).defined_operators_in_definition:
                    ermsg = (f"{op_name} and {def_opcls.__name__} are defined in terms of each "
                            f"other. Please edit their derived_definition methods to avoid this.")
                    raise RecursionError(ermsg)


class OperatorCollection:
    """Stores the operators that will be passed to Syntax."""

    def __init__(self, *input):
        self.operator_classes_dict = {}
        if input:
            self.add_operator(input)

    def __iter__(self):
        yield from self.operator_classes_dict

    def __getitem__(self, value):
        return self.operator_classes_dict[value]
    
    def items(self):
        yield from self.operator_classes_dict.items()

    def add_operator(self, input):
        """Input is either an operator class (of type 'type') or a list of operator classes."""
        if input.name is None:
            raise ValueError(f"Operator class {input.__name__} has no name defined.")
        if isinstance(input, (list, tuple, set)):
            for operator_class in input:
                self.add_operator(operator_class)
        elif isinstance(input, type):
            # print(f"Adding operator: {input.name}")  # Debugging line
            self.operator_classes_dict[input.name] = input
        else:
            raise TypeError(f"unexpected input type {type(input)} for add_operator")

    def apply_operator(self, prefix_sentence):
        if len(prefix_sentence) == 1:
            atom = prefix_sentence[0]
            if atom in {"\\top", "\\bot"}:  # Handle extremal operators
                return [self[atom]]
            if atom.isalnum():  # Handle atomic sentences
                return [Const(atom, AtomSort)]
            raise ValueError(f"The atom {atom} is invalid in apply_operator.")
        op, arguments = prefix_sentence[0], prefix_sentence[1:]
        # print(f"Applying operator: {op}")  # Debugging line
        activated = [self.apply_operator(arg) for arg in arguments]
        activated.insert(0, self[op])
        return activated
        # return self.translate_prefix_types(activated)


class Syntax:
    """Takes infix_premises, infix_conclusions, and operator_collection as
    arguments, generating and storing instances of the Sentence class.
    Draws on Sentence instances for the premises and conclusions in order to
    store a dictionary which includes all subsentences for each before drawing
    on the operator_collection in order to initialize the prefix_types in each
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

        self.initialize_types(self.all_sentences.values())

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

    def sub_dictionary(self, sentence):
        """Takes a sentence object as input and builds a dictionary consisting
        of it and all subsentences by looking to its arguments (if any)."""
        sub_dictionary = {}
        sub_dictionary[sentence.name] = sentence
        if sentence.arguments:
            for sent_obj in sentence.arguments:
                if sent_obj in sub_dictionary.values():
                    continue
                arg_dict = self.sub_dictionary(sent_obj)
                sub_dictionary.update(arg_dict)
        return sub_dictionary

    def sentence_dictionary(self, infix_inputs):
        """Takes a list of sentences composing the dictionaries of subsentences
        for each, resulting in a dictionary that includes all subsentences."""
        all_sentences = {}
        for infix_sent in infix_inputs:
            if infix_sent in all_sentences.keys():
                continue
            sentence = Sentence(infix_sent)
            subsent_dict = self.sub_dictionary(sentence)
            all_sentences.update(subsent_dict)
        sorted_sentences = sorted(all_sentences.items(), key=lambda item: item[1].complexity)
        sorted_all_sentences = {s.name: s for _, s in sorted_sentences}
        return sorted_all_sentences

    def initialize_types(self, sentence_objs):
        """Draws on the operator_collection in order to initialize all sentences
        in the input by replacing operator strings with operator classes and
        updating prefix_type in that sentence_obj. If the main operator is not
        primitive, derived_arguments are updated with derived_types."""
        ops = self.operator_collection
        for sent_obj in sentence_objs:
            if sent_obj.prefix_type:
                continue
            if sent_obj.arguments:
                self.initialize_types(sent_obj.arguments)
            sent_obj.update_prefix_type(ops)
            if len(sent_obj.derived_type) > 1:
                sent_obj.update_derived_arguments()
                self.initialize_types(sent_obj.derived_arguments)

