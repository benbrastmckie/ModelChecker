
from hidden_helpers import (
    remove_repeats, 
    not_implemented_string,
    flatten,
)

import inspect

from z3 import Const, DeclareSort

# B: I was thinking about if AtomSort could be defined in a function
# instead of globally
AtomSort = DeclareSort("AtomSort")

class Sentence:
    """Class with an instance for each sentence."""

    def __init__(self, infix_sentence, operator_collection):
        self.name = infix_sentence
        self.prefix_string = self.prefix(infix_sentence)
        self.prefix_type = operator_collection.apply_operator(self.prefix_string)
        self.prefix_sentence = None # requires semantics to instantiate type
        letters, meds, ops, complexity = self.constituents_of(self.prefix_string)
        self.sentence_letters = letters
        self.intermediate_strings = meds
        self.subsentence_strings = (letters + meds + [self.prefix_string])
        self.operators = ops
        self.complexity = complexity

    # B: not sure these will be needed
    # def get_values(self):
    #     """Returns components of the Sentence instance as a dictionary."""
    #     return {
    #         'name': self.name,
    #         'prefix_sentence': self.prefix_sentence,
    #         'sentence_letters': self.sentence_letters,
    #         'operators': self.operators,
    #         'subsentences': self.subsentences,
    #         'complexity': self.complexity
    #     }
    

    def __str__(self):
        return self.name
    
    def __repr__(self):
        return self.name
        
    def prefix(self, infix_sentence):
        """For converting from infix to prefix notation without knowing which
        which operators the language includes."""
        tokens = infix_sentence.replace("(", " ( ").replace(")", " ) ").split()
        return self.parse_expression(tokens)
    
    # def update_prefix_type(self, operator_collection):
    #     self.prefix_type = operator_collection.apply_operator(self.prefix_wff)

    def update_prefix_sentence(self, model_constraints):
        self.prefix_sentence = model_constraints.activate_prefix_with_semantics(self.prefix_type)

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

    def constituents_of(self, prefix_sentence):
        """Take a prefix sentence and return sentence_letters, intermediates,
        operators, and complexity."""
        sentence_letters = []
        operators = []
        subsentences = []
        complexity = 0

        if not prefix_sentence:
            raise ValueError("Prefix sentence is empty.")

        def is_operator(token):
            return '\\' in token

        def is_sentence_letter(token):
            return token.isalnum()

        if len(prefix_sentence) == 1:
            token = prefix_sentence[0]
            if is_operator(token):
                operators.append(prefix_sentence)
                return sentence_letters, operators, subsentences, complexity
            elif is_sentence_letter(token):
                sentence_letters.append(prefix_sentence)
                return sentence_letters, operators, subsentences, complexity
            else:
                raise ValueError(f"The sentence {prefix_sentence} is not well-formed.")

        main_operator = prefix_sentence[0]
        operators.append(main_operator)
        complexity += 1

        arguments = prefix_sentence[1:]
        for arg in arguments:
            if len(arg) > 1:
                subsentences.append(arg)
            arg_sent_lets, arg_subs, arg_ops, arg_comp = self.constituents_of(arg)
            sentence_letters.extend(arg_sent_lets)
            subsentences.extend(arg_subs)
            operators.extend(arg_ops)
            complexity += arg_comp

        # Use set for uniqueness during collection, then sort once
        sorted_sent_lets = sorted(remove_repeats(sentence_letters))
        sorted_subs = sorted(remove_repeats(subsentences))  # For subsentences as lists
        sorted_ops = sorted(remove_repeats(operators))

        return sorted_sent_lets, sorted_subs, sorted_ops, complexity


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

    # def derived_definition(self):
    # def derived_definition(self, *args):
    # B: arguments need to be included as below to avoid type errors. I tried
    # the above to accommodate different arity, but no luck. I suppose that
    # errors will come back when we define unary operators
    # TODO: change back to original
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

        # NOTE: add if need to look up sentences
        # self.premises = {prem : Sentence(prem) for prem in infix_premises}
        # self.conclusions = {con : Sentence(con)for con in infix_conclusions}
        self.premises = [Sentence(prem, operator_collection) for prem in infix_premises]
        self.conclusions = [Sentence(con, operator_collection) for con in infix_conclusions]
        self.operators = operator_collection

        # Collect from premises and conclusions and gather constituents
        inputs = list(self.premises) + list(self.conclusions)
        letters, meds, ops = self.gather_constituents(inputs)
        # NOTE: in above, ops not currently needed

        # B: attempt but not successful
        # self.all_sentences = self.subsentence_dictionary(meds)


        self.sentence_letter_types = [Const(letter[0], AtomSort) for letter in letters]
        self.intermediate_types = [self.operators.apply_operator(med) for med in meds]
        self.prefix_premise_types = [prem.prefix_type for prem in self.premises]
        self.prefix_conclusion_types = [conc.prefix_type for conc in self.conclusions]
        self.subsentence_types = (
            self.intermediate_types
            + self.prefix_premise_types
            + self.prefix_conclusion_types
        )

    # def infix(self, prefix_sent):
    #     """Takes a sentence in prefix notation (in any of the three kinds)
    #     and translates it to infix notation (a string)
    #     """
    #     if len(prefix_sent) == 1:
    #         return str(prefix_sent[0])
    #     op = prefix_sent[0]
    #     if len(prefix_sent) == 2:
    #         return f"{op} {self.infix(prefix_sent[1])}"
    #     left_expr = prefix_sent[1]
    #     right_expr = prefix_sent[2]
    #     return f"({self.infix(left_expr)} {op} {self.infix(right_expr)})"

    # def subsentence_dictionary(self, prefix_strings):
    #     sent_dict = {}
    #     for prefix_string in prefix_strings:
    #         infix_sent = self.infix(prefix_string)
    #         sentence_instance = Sentence(infix_sent, self.operators)
    #         sent_dict[infix_sent] = sentence_instance
    #     return sent_dict

    def gather_constituents(self, sentences):
        letters = []
        ops = set()
        meds = []
        for sent in sentences:
            letters.extend(sent.sentence_letters)
            meds.extend(sent.intermediate_strings)
            ops.update(sent.operators)
        sorted_sentence_letters = sorted(remove_repeats(letters))
        sorted_operators = sorted(ops)
        sorted_intermediates = sorted(remove_repeats(meds))
        return sorted_sentence_letters, sorted_intermediates, sorted_operators
    

#################################################################################################
################################### HELPERS FOR op_left_right ###################################
#################################################################################################

# it seems like our current convention is that functions that get called in an
# attribute of only one class are methods of that class, but functions that get
# called in methods of a class but not in the attributes, or that are called in
# multiple classes of a single module are helpers that live at the bottom of
# the module. this helps to keep the classes from getting to long. helpers that
# are needed in multiple modules can then go in in the helpers module.

# seems good to have an explicit convention that can be explained in the docs
# at some point.

# The functions below are only going to be used in op_left_right so was
# thinking they could be subfunctions of op_left_right. if they ended up
# being needed elsewhere (maybe balanced_parentheses is useful), then we could
# pull them out. but let me know if there is a reason not to do this.

def op_left_right(tokens):
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
