
from hidden_helpers import (remove_repeats, 
                            not_implemented_string,
                            flatten,
                            
                            )

import inspect

from z3 import Const, DeclareSort, simplify

# B: I'm assuming this will need to be included to activate sentence letters if this
# happens separately from finding sentence letters (if separating that is good)
# M: Not sure I understand
AtomSort = DeclareSort("AtomSort")

class Sentence:
    """Class with an instance for each sentence."""

    def __init__(self, infix_sentence):
        self.name = infix_sentence
        self.prefix_wff = self.prefix(infix_sentence)
        # M: I think we should rename this to well_formed_formula_prefix
        # B: sounds good!
        letters, meds, ops, complexity = self.constituents_of(self.prefix_wff)
        self.sentence_letters = letters
        self.intermediates = meds
        self.subsentences = (letters + meds + [self.prefix_wff])
        self.operators = ops
        self.complexity = complexity

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

    def op_left_right(self, tokens):
        """Divides whatever is inside a pair of parentheses into the left argument,
        right argument, and the operator."""
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
        """take a prefix sentence and return sentence_letter, intermediates,
        operators, and complexity."""
        sentence_letters = []
        operators = []
        subsentences = []
        complexity = 0
        if len(prefix_sentence) == 1:
            if '\\' in prefix_sentence[0]:
                operators.append(prefix_sentence)
                return sentence_letters, operators, subsentences, complexity
            if prefix_sentence[0].isalnum():
                # B: would it be better to have lists of length 1 here?
                sentence_letters.append(prefix_sentence[0])
                return sentence_letters, operators, subsentences, complexity
            raise ValueError(f"The sentence {prefix_sentence} is not well-formed.")
        # B: this is instead of above to exclude sentence letters; not sure if this is better
        # subsentences.append(prefix_sentence)
        main_operator = prefix_sentence[0]
        operators.append(main_operator)
        arguments = prefix_sentence[1:]
        complexity += 1
        for arg in arguments:
            arg_sent_lets, arg_subs, arg_ops, arg_comp = self.constituents_of(arg)
            sentence_letters.extend(arg_sent_lets)
            operators.extend(arg_ops)
            subsentences.extend(arg_subs)
            complexity += arg_comp
        sorted_sent_lets = sorted(remove_repeats(sentence_letters))
        sorted_subs = sorted(remove_repeats(subsentences))
        sorted_ops = sorted(remove_repeats(operators))
        return sorted_sent_lets, sorted_subs, sorted_ops, complexity

class Operator:
    """Defaults inherited by every operator."""

    name = None
    arity = None
    primitive = True # a small piece of the avoid DefinedOperator recursion soln

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

    def derived_definition(self):
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

        # Store inputs
        # self.infix_premises = infix_premises # M: I think we can get rid of this given new Sentence class
        # self.infix_conclusions = infix_conclusions # M: I think we can get rid of this given new Sentence class
        self.operator_collection = operator_collection

        # Create Sentence instances for the premises and conclusions
        # self.premises = {prem : Sentence(prem) for prem in infix_premises}
        # self.conclusions = {con : Sentence(con)for con in infix_conclusions}
        self.premises = [Sentence(prem) for prem in infix_premises]
        self.conclusions = [Sentence(con)for con in infix_conclusions]
        self.operators = operator_collection
        self.prefix_premises = [
            self.apply_operator(prem.prefix_wff)
            for prem in self.premises
        ] # the only point of this is to make sure that all the operators are in the OperatorCollection
        self.prefix_conclusions = [
            self.apply_operator(con.prefix_wff)
            for con in self.conclusions
        ]

        # Collect from premises and conclusions and gather constituents
        inputs = list(self.premises) + list(self.conclusions)
        letters, meds, ops = self.gather_constituents(inputs) # small issue with meds
        # ['A', ['A'], 'B', ['\\leftrightarrow', ['A'], ['B']], ['\\neg', ['B']]]
        self.all_sentence_letters = [
            Const(letter, AtomSort)
            for letter in letters
        ]
        self.all_intermediates = [
            self.apply_operator(med)
            for med in meds
        ]
        self.all_subsentences = (
            self.all_sentence_letters +
            self.all_intermediates +
            self.prefix_premises +
            self.prefix_conclusions
        )

    def apply_operator(self, prefix_wff):
        """
        converts prefix_wffs to prefix_sentences without activated operators
        """
        if len(prefix_wff) == 1:
            atom = prefix_wff[0]
            if atom in {"\\top", "\\bot"}:  # Handle extremal operators
                return [self.operators[atom]]
            if atom.isalnum():  # Handle atomic sentences
                return [Const(prefix_wff[0], AtomSort)]
        op, arguments = prefix_wff[0], prefix_wff[1:]
        activated = [self.apply_operator(arg) for arg in arguments]
        activated.insert(0, self.operators[op])
        return activated

    def gather_constituents(self, sentences):
        letters = set()
        ops = set()
        meds = []
        for sent in sentences:
            letters.update(sent.sentence_letters)
            ops.update(sent.operators)
            meds.extend(sent.subsentences)
        sorted_sentence_letters = sorted(list(letters), key=lambda x: str(x))
        sorted_operators = sorted(list(ops), key=lambda x: str(x))
        sorted_intermediates = remove_repeats(meds)
        return sorted_sentence_letters, sorted_intermediates, sorted_operators
    
# M: moved these out of Operator class. Not sure if that's the best place for them to live,
# but also not sure if this is the best place for them either. 
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
