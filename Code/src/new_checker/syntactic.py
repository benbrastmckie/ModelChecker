'''
things in syntactic right now:
    - Sentence
    - Operator
    - DefinedOperator
    - OperatorCollection
    - Syntax
'''


from hidden_helpers import (
    op_left_right,
    not_implemented_string,
    flatten,
)

import inspect

from z3 import Const, DeclareSort

AtomSort = DeclareSort("AtomSort")

class Sentence:
    """Given an infix_sentence and operator_collection, an instance of this
    class includes attributes for Class with an instance for each sentence."""

    def __init__(self, infix_sentence):
        self.name = infix_sentence
        # self.operator_collection = operator_collection
        self.prefix_string, self.complexity = self.prefix(infix_sentence)

        # B: storing classes for the arguments seems to causing trouble
        # switching to infix sentences which are key values for sentence dict
        if len(self.prefix_string) > 1: 
            self.arguments = [self.infix(arg) for arg in self.prefix_string[1:]]
        else:
            self.arguments = None

        self.prefix_type = None
        # OLD: this required operator_collection
        # self.prefix_type = operator_collection.apply_operator(self.prefix_string)
        self.prefix_sentence = None # requires semantics to instantiate
        self.prefix_operator = None # requires semantics to instantiate
        self.proposition = None # requires model_structure to interpret

    def __str__(self):
        return self.name
    
    def __repr__(self):
        return self.name
        
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
        prefix_sentence, complexity = self.parse_expression(tokens)
        return prefix_sentence, complexity

    def infix(self, prefix_sent): 
        # M: I think this in theory could also take prefix_types and
        # prefix_sentences, if need be—doesn't really matter but
        # just making note for documentation purposes
        # B: that could make for a nice general utility to include in the API
        # by making this a global function defined in hidden_helpers
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

    # B: I think this is causing problems
    def prefixes_to_sentences(self, prefix_strings):
        # M: I think this could be a problem because new Sentence objects are being made
        # that aren't in the bigger model_constraints or model_structure lists
        # B: the thought was that sentence objects include sentence objects for their
        # arguments where these are then gathered recursively in the Syntax class. I'd
        # be curious to DISCUSS if there is a better way to go about this
        infix_sentences = [self.infix(pre) for pre in prefix_strings]
        sentences = [
            Sentence(inf) # OLD , self.operator_collection)
            for inf in infix_sentences
        ]
        return sentences
    
    def update_prefix_type(self, operator_collection):
        # print(f"PRIOR: prefix_type for {self} about to be set")
        self.prefix_type = operator_collection.apply_operator(self.prefix_string)
        # print(f"UPDATE: prefix_type for {self} set to {self.prefix_type}")

    # HINT: maybe something is going wrong here?
    def activate_prefix_with_semantics(self, prefix_type, model_constraints):
        """
        prefix_type has operator classes and AtomSorts
        returns a prefix sentence of the third kind: the same as the second except operator instances
        """
        if prefix_type is None:
            raise ValueError(f"Prefix_type for {self} is None in activate_prefix_with_semantics.")
        new_prefix_form = []
        for elem in prefix_type:
            if isinstance(elem, type):
                new_prefix_form.append(model_constraints.operators[elem.name])
            elif isinstance(elem, list):
                new_prefix_form.append(self.activate_prefix_with_semantics(elem, model_constraints))
            else:
                new_prefix_form.append(elem)
        # print(f"Activating prefix with semantics for {self}: result = {new_prefix_form}")
        return new_prefix_form

    def update_prefix_sentence(self, model_constraints): # happens in ModelConstraints init
        '''
        This method takes a ModelConstraints object and updates self.prefix_sentence
        to be a prefix_sentnece with semantics (ie Operator instances, not objects)
        and makes self.prefix_operator the main operator of the prefix_sentence
        return None
        '''
        # print(f"Updating prefix_sentence for {self}")
        self.prefix_sentence = self.activate_prefix_with_semantics(
            self.prefix_type,
            model_constraints
        )
        if self.prefix_type is None:
            print(f"WARNING: {self} has None for prefix_sentence after activation.")
        if self.arguments:
            self.prefix_operator = self.prefix_sentence[0]

    def update_proposition(self, model_structure): # happens in ModelStructure init
        """Builds a proposition object for the sentence given the model_structure."""
        if self.prefix_sentence is None:
            raise ValueError(f"prefix_sentence for {self} is None when calling update_proposition.")
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
                # print("ATOM", [Const(atom, AtomSort)])
                return [Const(atom, AtomSort)]
        op, arguments = prefix_string[0], prefix_string[1:]
        # print(f"DEBUG: Processing operator {op} with arguments {arguments}")
        activated = [self.apply_operator(arg) for arg in arguments]
        activated.insert(0, self[op])
        # if activated is None:
        #     raise ValueError(f"apply_operator returned None for prefix_string {prefix_string}")
        return activated
        # raise ValueError(f"apply_operator returned None for prefix_string {prefix_string}")


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
        self.operator_collection = operator_collection

        infix_inputs = self.infix_premises + self.infix_conclusions
        self.all_sentences = self.sentence_dictionary(infix_inputs)

        # for sent in self.all_sentences.values():
        #     print(f"BEFORE TYPE: {sent.prefix_type}")

        self.initialize_prefix_types(self.all_sentences.values())

        # for sent in self.all_sentences.values():
        #     print(f"AFTER TYPE: {sent.prefix_type}")

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

    # def infix(self, prefix_sent): 
    #     # M: I think this in theory could also take prefix_types and
    #     # prefix_sentences, if need be—doesn't really matter but
    #     # just making note for documentation purposes
    #     # B: that could make for a nice general utility to include in the API
    #     # by making this a global function defined in hidden_helpers
    #     """Takes a sentence in prefix notation (in any of the three kinds)
    #     and translates it to infix notation (a string)."""
    #     if len(prefix_sent) == 1:
    #         return str(prefix_sent[0])
    #     op = prefix_sent[0]
    #     if len(prefix_sent) == 2:
    #         return f"{op} {self.infix(prefix_sent[1])}"
    #     left_expr = prefix_sent[1]
    #     right_expr = prefix_sent[2]
    #     return f"({self.infix(left_expr)} {op} {self.infix(right_expr)})"

    def sub_dictionary(self, sentence):
        sub_dictionary = {}
        sub_dictionary[sentence.name] = sentence
        if sentence.arguments:
            for infix_arg in sentence.arguments:
                if infix_arg in sub_dictionary.keys():
                    continue
                sentence_arg = Sentence(infix_arg)
                arg_dict = self.sub_dictionary(sentence_arg)
                sub_dictionary.update(arg_dict)
        return sub_dictionary

    def sentence_dictionary(self, infix_inputs):
        all_sentences = {}
        for input in infix_inputs:
            if input in all_sentences.keys():
                continue
            sentence = Sentence(input) # OLD , self.operators)
            subsent_dict = self.sub_dictionary(sentence)
            all_sentences.update(subsent_dict)
        return all_sentences

    def initialize_prefix_types(self, sentences):
        ops = self.operator_collection
        for sent_obj in sentences:
            # print("SENTENCE:", sent_obj)
            if sent_obj.prefix_type:
                # print("SKIPPED:", sent_obj)
                continue
            sent_obj.update_prefix_type(ops)
            # print("UPDATED:", sent_obj)
            # if sent.prefix_type is None:
                # print(f"Setting prefix_type for {sent} to None.")

