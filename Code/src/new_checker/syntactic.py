
from hidden_helpers import (
    remove_repeats, 
    not_implemented_string,
    flatten,
)

import inspect

from z3 import Const, DeclareSort, simplify

# B: I was thinking about if AtomSort could be defined in a function
# instead of globally
AtomSort = DeclareSort("AtomSort")

class Sentence:
    """Class with an instance for each sentence."""

    def __init__(self, infix_sentence):
        self.name = infix_sentence
        self.prefix_wff = self.prefix(infix_sentence)
        # M: I think we should rename this to well_formed_formula_prefix
        # B: sounds good! I can let the LSP take care of this once we are ready
        self.prefix_type = None
        self.prefix_sentence = None
        letters, meds, ops, complexity = self.constituents_of(self.prefix_wff)
        self.sentence_letters = letters
        self.intermediates = meds
        self.subsentences = (letters + meds + [self.prefix_wff])
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
    
    def update_prefix_type(self, operator_collection):
        self.prefix_type = operator_collection.apply_operator(self.prefix_wff)

    def update_prefix_sentence(self, semantics):
        self.prefix_sentence = semantics.activate_prefix_with_semantics(self.prefix_type)

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
        if self.__class__ == Operator:
            raise NotImplementedError(not_implemented_string(self.__class__.__name__))
        if self.name is None or self.arity is None:
            op_class = self.__class__.__name__
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
    
    def apply_operator(self, prefix_wff):
        """
        converts prefix_wffs to prefix_sentences without activated operators
        """
        if len(prefix_wff) == 1:
            atom = prefix_wff[0]
            if atom in {"\\top", "\\bot"}:  # Handle extremal operators
                return [self[atom]]
            if atom.isalnum():  # Handle atomic sentences
                return [Const(prefix_wff[0], AtomSort)]
        op, arguments = prefix_wff[0], prefix_wff[1:]
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

        # Store inputs and create Sentence instances
        # self.operator_collection = operator_collection
        # self.premises = {prem : Sentence(prem) for prem in infix_premises}
        # self.conclusions = {con : Sentence(con)for con in infix_conclusions}
        # B: I switched to the dictionaries above but currently they aren't
        # needed since .values() is used whenever they are called
        # M: I have a feeling we'll never need them as dictionaries, at least on the back end
        # M: I switched them back because I wrote a lot of code as if they were lists so to
        # quick fix I just made them lists here
        # M: what's your reasoning for making them dictionaries?
        self.premises = [Sentence(prem) for prem in infix_premises]
        self.conclusions = [Sentence(con)for con in infix_conclusions]
        self.operators = operator_collection
        for prem in self.premises:
            prem.update_prefix_type(self.operators)
        for conclusion in self.conclusions:
            conclusion.update_prefix_type(self.operators)

        # Collect from premises and conclusions and gather constituents
        inputs = list(self.premises) + list(self.conclusions)
        letters, meds, ops = self.gather_constituents(inputs)
        self.all_sentence_letters = [Const(letter[0], AtomSort) for letter in letters]
        self.all_intermediates = [self.operators.apply_operator(med) for med in meds]
        self.prefix_type_premises = [prem.prefix_type for prem in self.premises]
        self.prefix_type_conclusions = [conc.prefix_type for conc in self.conclusions]
        self.all_subsentences = (
            self.all_sentence_letters # M: think this maybe should get removed from here
            + self.all_intermediates
            + self.prefix_type_premises
            + self.prefix_type_conclusions
        )

    def gather_constituents(self, sentences):
        letters = []
        ops = set()
        meds = []
        for sent in sentences:
            letters.extend(sent.sentence_letters)
            meds.extend(sent.intermediates)
            ops.update(sent.operators)
        sorted_sentence_letters = sorted(remove_repeats(letters))
        # sorted_operators = sorted(list(ops), key=lambda x: str(x))
        sorted_operators = sorted(ops)
        sorted_intermediates = sorted(remove_repeats(meds))
        return sorted_sentence_letters, sorted_intermediates, sorted_operators
    
# M: moved these out of Operator class. Not sure if that's the best place for them to live,
# but also not sure if this is the best place for them either. 
# B: these are very semantic and get used in defining operators.
# even though operators is syntactic, I was thinking it would be convenient for
# them to be automatically inherited by all operators. I was thinking that the
# extremal propositions could be defined in the same place and so always be
# accessible when defining operators. defining operators is also pretty semantic.
# that said, the derived operators stuff I think does make sense to think of as
# syntactic and so fits in nicely in this module. It's maybe a bit of a stretch
# to include more semantic stuff in the Operator class, but if it is useful and
# there is no better place, maybe it makes the most sense? good to DISCUSS
def product(set_A, set_B):
    """set of pairwise fusions of elements in set_A and set_B"""
    product_set = set()
    for bit_a in set_A:
        for bit_b in set_B:
            bit_ab = simplify(bit_a | bit_b)
            product_set.add(bit_ab)
    return product_set

def coproduct(set_A, set_B):
    """union closed under pairwise fusion"""
    A_U_B = set_A.union(set_B)
    return A_U_B.union(product(set_A, set_B))






#################################################################################################
################################### HELPERS FOR op_left_right ###################################
#################################################################################################

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

def op_left_right(tokens):
    """Divides whatever is inside a pair of parentheses into the left argument,
    right argument, and the operator."""
    result = extract_arguments(tokens)
    if result is None:
        raise ValueError("Failed to extract arguments")
    return result