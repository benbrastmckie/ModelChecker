
from hidden_helpers import (
    op_left_right,
    not_implemented_string,
    flatten,
)

import inspect

from z3 import Const, DeclareSort

AtomSort = DeclareSort("AtomSort")

class Sentence:
    """Class with an instance for each sentence."""

    def __init__(self, infix_sentence, operator_collection):
        self.name = infix_sentence
        self.operator_collection = operator_collection
        self.prefix_string = self.prefix(infix_sentence)
        self.prefix_type = operator_collection.apply_operator(self.prefix_string)
        self.arguments = None
        if len(self.prefix_string) > 1: 
            self.arguments = self.prefixes_to_sentences(self.prefix_string[1:])
        self.prefix_sentence = None # requires semantics to instantiate
        self.prefix_operator = None # requires semantics to instantiate
        self.proposition = None # requires model_structure to interpret

        # TODO: add complexity
        
    def __str__(self):
        return self.name
    
    def __repr__(self):
        return self.name
        
    def prefix(self, infix_sentence):
        """For converting from infix to prefix notation without knowing which
        which operators the language includes."""
        tokens = infix_sentence.replace("(", " ( ").replace(")", " ) ").split()
        return self.parse_expression(tokens)

    def infix(self, prefix_sent):
        """Takes a sentence in prefix notation (in any of the three kinds)
        and translates it to infix notation (a string)."""
        if len(prefix_sent) == 1:
            return str(prefix_sent[0])
        op = prefix_sent[0]
        if len(prefix_sent) == 2:
            return f"{op} {self.infix(prefix_sent[1])}"
        left_expr = prefix_sent[1]
        right_expr = prefix_sent[2]
        return f"({self.infix(left_expr)} {op} {self.infix(right_expr)})"

    def prefixes_to_sentences(self, prefix_strings):
        infix_sentences = [self.infix(pre) for pre in prefix_strings]
        sentences = [
            Sentence(inf, self.operator_collection)
            for inf in infix_sentences
        ]
        return sentences
    
    def activate_prefix_with_semantics(self, prefix_type, model_constraints):
        """
        prefix_type has operator classes and AtomSorts
        returns a prefix sentence of the third kind: the same as the second except operator instances
        """
        new_prefix_form = []
        for elem in prefix_type:
            # print("TEST", f"element {elem} has type {type(elem)}")
            if isinstance(elem, type):
                new_prefix_form.append(model_constraints.operators[elem.name])
            elif isinstance(elem, list):
                new_prefix_form.append(self.activate_prefix_with_semantics(elem, model_constraints))
            else:
                new_prefix_form.append(elem)
        return new_prefix_form

    def update_prefix_sentence(self, model_constraints):
        self.prefix_sentence = self.activate_prefix_with_semantics(
            self.prefix_type,
            model_constraints
        )
        if self.arguments:
            self.prefix_operator = self.prefix_sentence[0]

    def update_proposition(self, model_structure):
        """Builds a proposition for the sentence given the model_structure."""
        self.proposition = model_structure.proposition_class(self, model_structure)

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
            operator, left, right = op_left_right(tokens)
            left_arg = self.parse_expression(left)  # Parse the left argument
            right_arg = self.parse_expression(right)  # Parse the right argument
            return [operator, left_arg, right_arg]
        if token.isalnum():  # Handle atomic sentences
            return [token]
        elif token in {"\\top", "\\bot"}:  # Handle extremal operators
            return [token]
        return [  # Unary operators
            token,
            self.parse_expression(tokens),
        ]


class Operator:
    """Defaults inherited by every operator."""

    name = None
    arity = None
    primitive = True # M: a small piece of the avoid DefinedOperator recursion soln

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
    
    
class DefinedOperator(Operator):

    primitive = False

    def derived_definition(self, leftarg, rightarg):
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
        elif len(args_with_self) == 1 and 'self' in args_with_self:
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

    def activate_prefix_definition(self, unactivated_prefix_def):
        '''Helper for get_derived_prefix_form. Takes a sentence in prefix notation
        returned by the derived_definition property of the DerivedOperator subclass
        and returns one with every Operator in that definition instantiated (since
        in the derived_definition operators are defined without an instantiation.)'''
        new_prefix_def = []
        for elem in unactivated_prefix_def:
            if isinstance(elem, type):
                new_prefix_def.append(elem(self.semantics))
            elif isinstance(elem, list):
                new_prefix_def.append(self.activate_prefix_definition(elem))
            else: # so an instantiated operator or a sentence letter
                new_prefix_def.append(elem)
        return new_prefix_def

    def get_derived_prefix_form(self, args):
        '''given a set of arguments, returns a prefix sentence that correctly
        puts them into the derived definition of the derived operator
        returns a sentence in prefix notation (list of AtomSorts and Operator instances)'''
        unact_prefix_def = self.derived_definition(*args)
        return DefinedOperator.activate_prefix_definition(self, unact_prefix_def)
    
    def true_at(self, *args_and_eval_world):
        args, eval_world = args_and_eval_world[0:-1], args_and_eval_world[-1]
        prefix_def = self.get_derived_prefix_form(args)
        operator, new_args = prefix_def[0], prefix_def[1:]
        return operator.true_at(*new_args, eval_world)
    
    def false_at(self, *args_and_eval_world):
        args, eval_world = args_and_eval_world[0:-1], args_and_eval_world[-1]
        prefix_def = self.get_derived_prefix_form(args)
        operator, new_args = prefix_def[0], prefix_def[1:]
        return operator.false_at(*new_args, eval_world)
    
    def find_verifiers_and_falsifiers(self, *argprops):
        prefix_args = [prop.prefix_sentence for prop in argprops]
        prefix_def = self.get_derived_prefix_form(prefix_args)
        prop_class, model_structure = argprops[0].__class__, argprops[0].model_structure
        derived_subprops = (prop_class(pfsent, model_structure) for pfsent in prefix_def[1:])
        operator = prefix_def[0]
        return operator.find_verifiers_and_falsifiers(*derived_subprops)


class OperatorCollection:
    """Stores the operators that will be passed to ModelSetup."""

    def __init__(self, *input):
        self.operator_classes_dict = {}
        if input:
            self.add_operator(input)

    def __iter__(self):
        yield from self.operator_classes_dict

    def items(self):
        yield from self.operator_classes_dict.items()

    def add_operator(self, input):
        """Input is either an operator class (of type 'type') or a list of operator classes."""
        if (
            isinstance(input, list)
            or isinstance(input, tuple)
            or isinstance(input, set)
        ):
            for operator_class in input:
                self.add_operator(operator_class)
        elif isinstance(input, type):
            self.operator_classes_dict[input.name] = input

    def __getitem__(self, value):
        return self.operator_classes_dict[value]
    
    def apply_operator(self, prefix_string):
        """Converts prefix_strings to prefix_types with operator classes."""
        if len(prefix_string) == 1:
            atom = prefix_string[0]
            if atom in {"\\top", "\\bot"}:  # Handle extremal operators
                return [self[atom]]
            if atom.isalnum():  # Handle atomic sentences
                return [Const(prefix_string[0], AtomSort)]
        op, arguments = prefix_string[0], prefix_string[1:]
        activated = [self.apply_operator(arg) for arg in arguments]
        activated.insert(0, self[op])
        return activated


class Syntax:
    """Takes infix_premises, infix_conclusions, and operator_collection as
    arguments, generating and storing instances of the Sentence class.
    Draws on Sentence instances to gather and apply the operators to generate
    and store all_sentence_letters, all_subsentences, prefix_sentences, and
    prefix_conclusions.
    """

    def __init__(
        self,
        infix_premises,
        infix_conclusions,
        operator_collection,
    ):

        self.infix_premises = infix_premises
        self.infix_conclusions = infix_conclusions
        self.operators = operator_collection

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

    def sub_dictionary(self, sentence):
        sub_dictionary = {}
        sub_dictionary[sentence.name] = sentence
        if sentence.arguments:
            for arg in sentence.arguments:
                if arg in sub_dictionary.keys():
                    continue
                arg_dict = self.sub_dictionary(arg)
                sub_dictionary.update(arg_dict)
        return sub_dictionary

    def sentence_dictionary(self, infix_inputs):
        all_sentences = {}
        for input in infix_inputs:
            if input in all_sentences.keys():
                continue
            sentence = Sentence(input, self.operators)
            subsent_dict = self.sub_dictionary(sentence)
            all_sentences.update(subsent_dict)
        return all_sentences
